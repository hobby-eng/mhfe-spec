use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::layout::{self, GEOMETRY_TOLERANCE, PAGE_HEIGHT, PAGE_WIDTH, Position};
use crate::process::{run, text};
use crate::raster::{Raster, RasterResult};
use roxmltree::Node;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs;
use std::path::Path;

#[derive(Clone)]
pub(crate) struct Word {
    pub(crate) page: usize,
    pub(crate) left: f64,
    pub(crate) right: f64,
    pub(crate) top: f64,
    pub(crate) bottom: f64,
    pub(crate) text: String,
}

/// Checks PDF text and geometry through Poppler, independently of Typst layout.
pub(crate) struct PdfCheck {
    pages: usize,
    pub(crate) words: Vec<Word>,
}

#[derive(Serialize)]
pub(crate) struct PdfResult {
    pub(crate) pages: usize,
    pub(crate) pdf_characters: usize,
    pub(crate) native_characters: usize,
    pub(crate) cells: usize,
    pub(crate) raster: Vec<RasterResult>,
}

impl PdfCheck {
    pub(crate) fn read(path: &Path, directory: &Path, name: &str) -> Result<Self> {
        run("pdfinfo", [path.as_os_str()], None, None)?;
        let bytes = run(
            "pdftotext",
            [
                OsStr::new("-bbox-layout"),
                OsStr::new("-enc"),
                OsStr::new("UTF-8"),
                path.as_os_str(),
                OsStr::new("-"),
            ],
            None,
            None,
        )?;
        fs::write(directory.join(format!("{name}-pdf-text.html")), &bytes)?;
        let source = text(bytes)?;
        // Poppler emits an XHTML doctype. roxmltree has no network or filesystem
        // entity resolver; allowing this generated DTD does not fetch its URL.
        let xml = roxmltree::Document::parse_with_options(
            &source,
            roxmltree::ParsingOptions {
                allow_dtd: true,
                ..Default::default()
            },
        )
        .map_err(|e| Failure::new("PDF-XML", e.to_string()))?;
        let pages: Vec<_> = xml
            .descendants()
            .filter(|node| node.has_tag_name("page"))
            .collect();
        if pages.is_empty() || pages.len() > 400 {
            return Err(Failure::new("PDF-PAGES", "Empty or oversized PDF"));
        }
        let mut words = Vec::new();
        for (i, page) in pages.iter().enumerate() {
            if (attribute(*page, "width")? - PAGE_WIDTH).abs() > GEOMETRY_TOLERANCE
                || (attribute(*page, "height")? - PAGE_HEIGHT).abs() > GEOMETRY_TOLERANCE
            {
                return Err(Failure::new("PDF-PAGES", "Unexpected PDF page size"));
            }
            let mut count = 0;
            for node in page.descendants().filter(|n| n.has_tag_name("word")) {
                let word = Word {
                    page: i + 1,
                    left: attribute(node, "xMin")?,
                    right: attribute(node, "xMax")?,
                    top: attribute(node, "yMin")?,
                    bottom: attribute(node, "yMax")?,
                    text: node.text().unwrap_or_default().into(),
                };
                if word.left < -GEOMETRY_TOLERANCE
                    || word.right > PAGE_WIDTH + GEOMETRY_TOLERANCE
                    || word.top < -GEOMETRY_TOLERANCE
                    || word.bottom > PAGE_HEIGHT + GEOMETRY_TOLERANCE
                    || word.text.contains(['\u{fffd}', '\0'])
                {
                    return Err(Failure::new(
                        "PDF-GLYPH",
                        format!("Invalid or overflowing PDF glyph on page {}", i + 1),
                    ));
                }
                words.push(word);
                count += 1;
            }
            if count == 0 {
                return Err(Failure::new(
                    "PDF-PAGES",
                    "An unexpected empty page was produced",
                ));
            }
        }
        Ok(Self {
            pages: pages.len(),
            words,
        })
    }

    pub(crate) fn validate(
        &self,
        document: &Document,
        metadata: &[Value],
        directory: &Path,
        name: &str,
        images: bool,
    ) -> Result<PdfResult> {
        layout::coverage(document, metadata)?;
        let native = layout::native_text(metadata);
        let actual: String = self.words.iter().map(|word| word.text.as_str()).collect();
        let expected_counts = layout::counts(&native);
        let actual_counts = layout::counts(&actual);
        let characters: std::collections::BTreeSet<_> = expected_counts
            .keys()
            .chain(actual_counts.keys())
            .copied()
            .collect();
        let differences: Vec<_> = characters
            .into_iter()
            .filter_map(|c| {
                let expected = expected_counts.get(&c).copied().unwrap_or(0);
                let actual = actual_counts.get(&c).copied().unwrap_or(0);
                (expected != actual).then(|| json!({"character":c,"native":expected,"pdf":actual}))
            })
            .collect();
        // Retain a precise diagnostic before refusing, so a font mapping mismatch can
        // be distinguished from a missing glyph without accepting a damaged result.
        if !differences.is_empty() {
            crate::process::json_file(
                &directory.join(format!("{name}-text-differences.json")),
                &differences,
            )?;
            return Err(Failure::new(
                "PDF-TEXT",
                format!(
                    "PDF/native character counts differ for {} characters",
                    differences.len()
                ),
            ));
        }
        self.prose(document, metadata)?;
        self.headings(metadata)?;
        self.contents_spacing(metadata)?;
        let cells = self.cells(metadata)?;
        let raster = if images {
            self.images(metadata, directory, name)?
        } else {
            Vec::new()
        };
        Ok(PdfResult {
            pages: self.pages,
            pdf_characters: layout::normalized(&actual).chars().count(),
            native_characters: native.chars().count(),
            cells,
            raster,
        })
    }

    fn headings(&self, metadata: &[Value]) -> Result<()> {
        for (index, record) in metadata
            .iter()
            .enumerate()
            .filter(|(_, v)| v["kind"] == "heading-start")
        {
            let end_index = metadata
                .iter()
                .enumerate()
                .skip(index + 1)
                .find(|(_, v)| v["kind"] == "heading-end" && v["id"] == record["id"])
                .map(|(i, _)| i)
                .ok_or_else(|| Failure::new("PDF-HEADING", "Missing heading end"))?;
            let start = layout::position(&record["pos"])?;
            let end = layout::position(&metadata[end_index]["pos"])?;
            if start.page != end.page {
                return Err(Failure::new(
                    "PDF-HEADING",
                    "A heading was split across pages",
                ));
            }
            let title = layout::native_text(&metadata[index + 1..end_index]);
            let words = self.heading_words(start, end, &title)?;
            let top = words
                .iter()
                .map(|w| w.top)
                .reduce(f64::min)
                .ok_or_else(|| Failure::new("PDF-HEADING", "A heading has no visible text"))?;
            let bottom = words.iter().map(|w| w.bottom).fold(top, f64::max);
            let previous = self
                .words
                .iter()
                .filter(|w| {
                    w.page == start.page
                        && w.top < top
                        && !words.iter().any(|h| std::ptr::eq(*h, *w))
                })
                .map(|w| w.bottom)
                .reduce(f64::max);
            let next = self
                .words
                .iter()
                .filter(|w| {
                    w.page == start.page
                        && w.top >= top
                        && w.top < PAGE_HEIGHT - 50.0
                        && !words.iter().any(|h| std::ptr::eq(*h, *w))
                })
                .map(|w| w.top)
                .reduce(f64::min)
                .ok_or_else(|| {
                    Failure::new("PDF-HEADING", "A heading is stranded at a page end")
                })?;
            if previous.is_some_and(|y| top - y < 11.0) || next - bottom < 9.0 {
                return Err(Failure::new(
                    "PDF-HEADING",
                    format!("Insufficient visible heading space on page {}", start.page),
                ));
            }
        }
        Ok(())
    }

    fn heading_words(&self, start: Position, end: Position, title: &str) -> Result<Vec<&Word>> {
        let candidates: Vec<_> = self
            .words
            .iter()
            .filter(|w| w.page == start.page && w.top >= start.y - 1.0 && w.top <= end.y + 1.0)
            .collect();
        for first in 0..candidates.len() {
            let mut text = String::new();
            for last in first..candidates.len() {
                text.push_str(&layout::normalized(&candidates[last].text));
                if !text.is_empty() && text == title {
                    return Ok(candidates[first..=last].to_vec());
                }
                if !title.starts_with(&text) {
                    break;
                }
            }
        }
        Err(Failure::new(
            "PDF-HEADING",
            "The exact heading text was not found in the PDF",
        ))
    }

    fn contents_spacing(&self, metadata: &[Value]) -> Result<()> {
        for (_, pairs) in ranges(metadata, "contents-start", "contents-end")? {
            for (start, end) in pairs {
                let mut words: Vec<_> = self
                    .words
                    .iter()
                    .filter(|w| {
                        w.page >= start.page
                            && w.page <= end.page
                            && (w.page != start.page || w.top >= start.y - 1.0)
                            && (w.page != end.page || w.top <= end.y + 1.0)
                            && w.text.chars().any(char::is_alphanumeric)
                    })
                    .collect();
                words.sort_by(|a, b| a.page.cmp(&b.page).then(a.top.total_cmp(&b.top)));
                let mut rows: Vec<(usize, f64, f64)> = Vec::new();
                for word in words {
                    if let Some((page, top, bottom)) = rows.last_mut()
                        && *page == word.page
                        && word.top - *top < 2.0
                    {
                        *bottom = bottom.max(word.bottom);
                    } else {
                        rows.push((word.page, word.top, word.bottom));
                    }
                }
                for rows in rows.windows(2) {
                    if rows[0].0 == rows[1].0 && rows[1].1 - rows[0].2 < 0.5 {
                        return Err(Failure::new(
                            "PDF-CONTENTS",
                            "Contents lines overlap or have no visible gap",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn prose(&self, document: &Document, metadata: &[Value]) -> Result<()> {
        let ranges = ranges(metadata, "block-start", "block-end")?;
        for block in &document.blocks {
            if block.prose.is_empty() {
                continue;
            }
            let expected = layout::normalized(&block.prose);
            let candidates = ranges
                .get(&block.id)
                .ok_or_else(|| Failure::new("PDF-COVERAGE", "Missing source block range"))?;
            for (start, end) in candidates {
                let words: Vec<_> = self
                    .words
                    .iter()
                    .filter(|word| {
                        word.page >= start.page
                            && word.page <= end.page
                            && (word.page != start.page || word.bottom >= start.y - 1.0)
                            && (word.page != end.page || word.top <= end.y + 1.0)
                    })
                    .collect();
                let text = reading_order(words);
                let actual = layout::normalized(&text);
                let mut available = actual.chars();
                if !expected
                    .chars()
                    .all(|character| available.by_ref().any(|c| c == character))
                {
                    return Err(Failure::new(
                        "PDF-PROSE",
                        format!("Source text was lost or reordered in {}", block.id),
                    ));
                }
            }
        }
        Ok(())
    }

    fn cells(&self, metadata: &[Value]) -> Result<usize> {
        let mut count = 0;
        for (index, record) in metadata
            .iter()
            .enumerate()
            .filter(|(_, v)| v["kind"] == "cell")
        {
            count += 1;
            let p = layout::position(&record["pos"])?;
            let width = layout::length(&record["width"])?;
            let height = layout::length(&record["height"])?;
            if p.x + width > PAGE_WIDTH + GEOMETRY_TOLERANCE || p.y + height > PAGE_HEIGHT - 40.0 {
                return Err(Failure::new(
                    "PDF-TABLE",
                    "Table cell does not fit its page",
                ));
            }
            let end = metadata[index + 1..]
                .iter()
                .position(|v| {
                    v["kind"] == "cell-end"
                        && v["id"] == record["id"]
                        && v["row"] == record["row"]
                        && v["column"] == record["column"]
                })
                .map(|offset| index + 1 + offset)
                .ok_or_else(|| Failure::new("PDF-TABLE", "Table cell has no end marker"))?;
            let expected = layout::counts(&layout::native_text(&metadata[index + 1..end]));
            let actual: String = self
                .words
                .iter()
                .filter(|word| {
                    word.page == p.page
                        && word.left >= p.x - GEOMETRY_TOLERANCE
                        && word.right <= p.x + width + GEOMETRY_TOLERANCE
                        && word.top >= p.y - GEOMETRY_TOLERANCE
                        && word.bottom <= p.y + height + GEOMETRY_TOLERANCE
                })
                .map(|word| word.text.as_str())
                .collect();
            let actual = layout::counts(&actual);
            if expected
                .iter()
                .any(|(c, n)| actual.get(c).copied().unwrap_or(0) < *n)
            {
                return Err(Failure::new(
                    "PDF-TABLE",
                    format!("Text does not fit its own table cell on page {}", p.page),
                ));
            }
            for word in self.words.iter().filter(|word| {
                word.page == p.page
                    && word.left >= p.x - 0.1
                    && word.left < p.x + width - 0.1
                    && word.top >= p.y - 0.1
                    && word.top < p.y + height - 0.1
            }) {
                if word.right > p.x + width + GEOMETRY_TOLERANCE {
                    return Err(Failure::new(
                        "PDF-TABLE",
                        format!("Text crosses a table column on page {}", p.page),
                    ));
                }
            }
        }
        Ok(count)
    }

    fn images(
        &self,
        metadata: &[Value],
        directory: &Path,
        name: &str,
    ) -> Result<Vec<RasterResult>> {
        let pdf = directory.join(format!("{name}.pdf"));
        let prefix = directory.join(format!("{name}-pdf"));
        run(
            "pdftoppm",
            [
                OsStr::new("-r"),
                OsStr::new("96"),
                OsStr::new("-png"),
                pdf.as_os_str(),
                prefix.as_os_str(),
            ],
            None,
            None,
        )?;
        let math: Vec<_> = ranges(metadata, "math-start", "math-end")?
            .into_values()
            .flatten()
            .collect();
        let mut output = Vec::new();
        for page in 1..=self.pages {
            let native = page_image(directory, &format!("{name}-native"), page, self.pages);
            let actual = page_image(directory, &format!("{name}-pdf"), page, self.pages);
            let native = Raster::read(&native)?;
            let actual = Raster::read(&actual)?;
            native.save_difference(
                &actual,
                &directory.join(format!("{name}-difference-{page}.png")),
            )?;
            output.push(native.compare(&actual, page, &math)?);
        }
        Ok(output)
    }
}

fn page_image(directory: &Path, prefix: &str, page: usize, pages: usize) -> std::path::PathBuf {
    let path = directory.join(format!("{prefix}-{page}.png"));
    if path.exists() {
        path
    } else {
        directory.join(format!(
            "{prefix}-{page:0width$}.png",
            width = pages.to_string().len()
        ))
    }
}

// Poppler can mistake widely justified fragments for separate columns. Rebuild
// physical rows by their shared vertical band, then read each row left to right.
fn reading_order(mut words: Vec<&Word>) -> String {
    words.sort_by(|a, b| {
        a.page
            .cmp(&b.page)
            .then(a.top.total_cmp(&b.top))
            .then(a.left.total_cmp(&b.left))
    });
    let mut rows: Vec<(usize, f64, Vec<&Word>)> = Vec::new();
    for word in words {
        if let Some((page, bottom, row)) = rows.last_mut()
            && *page == word.page
            && word.top < *bottom
        {
            *bottom = bottom.min(word.bottom);
            row.push(word);
        } else {
            rows.push((word.page, word.bottom, vec![word]));
        }
    }
    let mut result = String::new();
    for (_, _, mut row) in rows {
        row.sort_by(|a, b| a.left.total_cmp(&b.left));
        for word in row {
            result.push_str(&word.text);
        }
    }
    result
}

pub(crate) fn ranges(
    metadata: &[Value],
    start_kind: &str,
    end_kind: &str,
) -> Result<BTreeMap<String, Vec<(Position, Position)>>> {
    let mut starts: BTreeMap<&str, Vec<Position>> = BTreeMap::new();
    let mut ranges: BTreeMap<String, Vec<(Position, Position)>> = BTreeMap::new();
    for record in metadata {
        let id = record["id"].as_str().unwrap_or_default();
        if record["kind"] == start_kind {
            starts
                .entry(id)
                .or_default()
                .push(layout::position(&record["pos"])?);
        }
        if record["kind"] == end_kind {
            let start = starts
                .get_mut(id)
                .and_then(Vec::pop)
                .ok_or_else(|| Failure::new("PDF-LAYOUT", "End marker has no start"))?;
            let end = layout::position(&record["pos"])?;
            if end.page < start.page || (end.page == start.page && end.y + 1.0 < start.y) {
                return Err(Failure::new("PDF-LAYOUT", "Reversed content range"));
            }
            ranges.entry(id.into()).or_default().push((start, end));
        }
    }
    if starts.values().any(|v| !v.is_empty()) {
        return Err(Failure::new("PDF-LAYOUT", "Start marker has no end"));
    }
    Ok(ranges)
}

fn attribute(node: Node<'_, '_>, name: &str) -> Result<f64> {
    let value: f64 = node
        .attribute(name)
        .ok_or_else(|| Failure::new("PDF-XML", "Missing PDF geometry attribute"))?
        .parse()
        .map_err(|_| Failure::new("PDF-XML", "Invalid PDF geometry attribute"))?;
    if !value.is_finite() {
        return Err(Failure::new("PDF-XML", "Non-finite PDF coordinate"));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::{Word, reading_order};

    fn word(text: &str, left: f64, top: f64, bottom: f64) -> Word {
        Word {
            page: 1,
            left,
            right: left + 10.0,
            top,
            bottom,
            text: text.into(),
        }
    }

    #[test]
    fn reads_justified_fragments_as_rows_instead_of_columns() {
        let words = [
            word("Definition.", 0.0, 0.2, 10.9),
            word("7,776", 0.0, 18.3, 29.2),
            word("The", 70.0, 0.0, 10.9),
            word("lines", 70.0, 18.3, 29.2),
            word("filename.txt", 140.0, 0.7, 10.7),
        ];
        assert_eq!(
            reading_order(words.iter().collect()),
            "Definition.Thefilename.txt7,776lines"
        );
        let moved = [
            word("second", 0.0, 0.0, 10.9),
            word("first", 40.0, 0.0, 10.9),
        ];
        assert_eq!(reading_order(moved.iter().collect()), "secondfirst");
    }

    #[test]
    fn a_tall_glyph_cannot_merge_two_physical_rows() {
        let words = [
            word("one", 10.0, 0.0, 10.0),
            word("tall", 30.0, 1.0, 30.0),
            word("two", 0.0, 20.0, 30.0),
        ];
        assert_eq!(reading_order(words.iter().collect()), "onetalltwo");
    }
}
