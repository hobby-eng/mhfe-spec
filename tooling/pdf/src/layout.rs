use crate::document::Document;
use crate::failure::{Failure, Result};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use unicode_normalization::UnicodeNormalization;

pub(crate) const PAGE_WIDTH: f64 = 595.275_590_551;
pub(crate) const PAGE_HEIGHT: f64 = 841.889_763_780;
pub(crate) const GEOMETRY_TOLERANCE: f64 = 1.0;

#[derive(Clone, Copy)]
pub(crate) struct Position {
    pub(crate) page: usize,
    pub(crate) x: f64,
    pub(crate) y: f64,
}

pub(crate) fn length(value: &Value) -> Result<f64> {
    let text = value
        .as_str()
        .ok_or_else(|| Failure::new("PDF-LAYOUT", "Expected a layout length"))?;
    let number: f64 = text
        .strip_suffix("pt")
        .ok_or_else(|| Failure::new("PDF-LAYOUT", "Layout lengths must be points"))?
        .parse()
        .map_err(|_| Failure::new("PDF-LAYOUT", "Invalid layout length"))?;
    if !number.is_finite() {
        return Err(Failure::new("PDF-LAYOUT", "Non-finite layout length"));
    }
    Ok(number)
}

pub(crate) fn position(value: &Value) -> Result<Position> {
    let page = value["page"]
        .as_u64()
        .ok_or_else(|| Failure::new("PDF-LAYOUT", "Missing page number"))? as usize;
    let result = Position {
        page,
        x: length(&value["x"])?,
        y: length(&value["y"])?,
    };
    if page == 0
        || page > 400
        || result.x < -GEOMETRY_TOLERANCE
        || result.x > PAGE_WIDTH + GEOMETRY_TOLERANCE
        || result.y < -GEOMETRY_TOLERANCE
        || result.y > PAGE_HEIGHT + GEOMETRY_TOLERANCE
    {
        return Err(Failure::new(
            "PDF-LAYOUT",
            "Content marker lies outside its page",
        ));
    }
    Ok(result)
}

/// Checks source identities independently of the renderer's successful exit status.
pub(crate) fn coverage(document: &Document, metadata: &[Value]) -> Result<()> {
    let mut math: BTreeMap<&str, usize> = BTreeMap::new();
    let mut blocks: BTreeMap<&str, usize> = BTreeMap::new();
    let mut ends: BTreeMap<&str, usize> = BTreeMap::new();
    let mut math_ends: BTreeMap<&str, usize> = BTreeMap::new();
    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    for record in metadata {
        let kind = record["kind"].as_str().unwrap_or_default();
        position(&record["pos"])?;
        let id = record["id"].as_str().unwrap_or_default();
        match kind {
            "math-start" => *math.entry(id).or_default() += 1,
            "math-end" => *math_ends.entry(id).or_default() += 1,
            "block-end" => *ends.entry(id).or_default() += 1,
            "block-start" => {
                *blocks.entry(id).or_default() += 1;
                if seen.insert(id) {
                    order.push(id);
                }
            }
            _ => (),
        }
    }
    if math.len() != document.expressions.len() || blocks.len() != document.blocks.len() {
        return Err(Failure::new(
            "PDF-COVERAGE",
            "The laid out source inventory is incomplete",
        ));
    }
    for expression in &document.expressions {
        let count = math.get(expression.id.as_str()).copied().unwrap_or(0);
        if count == 0
            || (!expression.repeatable && count != 1)
            || math_ends.get(expression.id.as_str()) != Some(&count)
        {
            return Err(Failure::new(
                "PDF-COVERAGE",
                format!("Lost or duplicated {}", expression.id),
            ));
        }
    }
    for block in &document.blocks {
        let count = blocks.get(block.id.as_str()).copied().unwrap_or(0);
        if count == 0
            || (!block.repeatable && count != 1)
            || ends.get(block.id.as_str()) != Some(&count)
        {
            return Err(Failure::new(
                "PDF-COVERAGE",
                format!("Lost or duplicated {}", block.id),
            ));
        }
    }
    if order
        != document
            .blocks
            .iter()
            .map(|b| b.id.as_str())
            .collect::<Vec<_>>()
    {
        return Err(Failure::new(
            "PDF-COVERAGE",
            "Source blocks changed their order",
        ));
    }
    contents(metadata)?;
    crate::pagination::verify(document, metadata)?;
    Ok(())
}

fn contents(metadata: &[Value]) -> Result<()> {
    let starts: Vec<_> = metadata
        .iter()
        .filter(|v| v["kind"] == "contents-start")
        .collect();
    let ends: Vec<_> = metadata
        .iter()
        .filter(|v| v["kind"] == "contents-end")
        .collect();
    if starts.len() != ends.len() || starts.len() > 1 {
        return Err(Failure::new("PDF-CONTENTS", "Invalid contents markers"));
    }
    for (start, end) in starts.into_iter().zip(ends) {
        let first = position(&start["pos"])?;
        let last = position(&end["pos"])?;
        if start["oversized"] == true {
            // The top content margin is 18 mm, about 51 points.
            if first.y > 52.1 {
                return Err(Failure::new(
                    "PDF-CONTENTS",
                    "Oversized contents did not start on a fresh page",
                ));
            }
        } else if first.page != last.page {
            return Err(Failure::new(
                "PDF-CONTENTS",
                "Contents that fit a complete page were split",
            ));
        }
        let body = metadata
            .iter()
            .find(|v| v["kind"] == "contents-body-start")
            .ok_or_else(|| Failure::new("PDF-CONTENTS", "Missing body boundary after contents"))?;
        if position(&body["pos"])?.page != last.page + 1 {
            return Err(Failure::new(
                "PDF-CONTENTS",
                "The document body must begin on the page after contents",
            ));
        }
        let heading = metadata
            .iter()
            .find(|v| {
                v["kind"] == "heading-start"
                    && position(&v["pos"]).is_ok_and(|p| p.page > last.page)
            })
            .ok_or_else(|| Failure::new("PDF-CONTENTS", "No body heading after contents"))?;
        let heading = position(&heading["pos"])?;
        if heading.page != last.page + 1 || heading.y > 52.1 {
            return Err(Failure::new(
                "PDF-CONTENTS",
                "The first body heading must start a fresh page",
            ));
        }
    }
    Ok(())
}

pub(crate) fn normalized(source: &str) -> String {
    source
        .nfkc()
        .filter(|c| {
            !c.is_whitespace()
                && !matches!(
                    c,
                    '\u{00ad}'
                        | '\u{200b}'
                        | '\u{200c}'
                        | '\u{200d}'
                        | '\u{2061}'
                        | '\u{2062}'
                        | '\u{feff}'
                )
        })
        .collect()
}

pub(crate) fn native_text(metadata: &[Value]) -> String {
    let mut result = String::new();
    let mut in_math = 0usize;
    let mut in_footer = false;
    let mut seen_math = false;
    let mut tails = Vec::new();
    for record in metadata {
        match record["kind"].as_str() {
            Some("native-text") if in_math == 0 || in_footer => {
                result.push_str(record["text"].as_str().unwrap_or_default())
            }
            Some("footer-start") => in_footer = true,
            Some("footer-end") => in_footer = false,
            Some("native-math") if !seen_math => {
                result.push_str(&crate::math_content::glyphs(&record["body"]));
                result.push_str(&crate::math_content::pdf_decorations(&record["body"]));
                seen_math = true;
            }
            Some("math-start") => {
                in_math += 1;
                seen_math = false;
                tails.push(crate::math_content::glyphs(&record["tail"]));
                if let Some(tag) = record["tag"].as_str() {
                    result.push_str(tag);
                }
            }
            Some("math-promoted") => {
                // Its tail is already part of the complete native math tree.
                if let Some(tail) = tails.last_mut() {
                    tail.clear();
                }
            }
            Some("math-end") => {
                in_math = in_math.saturating_sub(1);
                if let Some(tail) = tails.pop() {
                    result.push_str(&tail);
                }
            }
            _ => (),
        }
    }
    normalized(&result)
}

pub(crate) fn counts(text: &str) -> BTreeMap<char, usize> {
    let mut counts = BTreeMap::new();
    for character in normalized(text).chars() {
        *counts.entry(character).or_default() += 1;
    }
    counts
}
