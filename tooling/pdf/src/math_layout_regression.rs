use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::layout::{self, Position};
use crate::pdf::{PdfCheck, Word};
use crate::process::{Toolchain, run as process};
use crate::raster::Raster;
use crate::regression::refused;
use crate::typeset::Typesetter;
use serde_json::{Value, json};
use std::ffi::OsStr;
use std::fs;
use std::path::Path;

pub(crate) fn run(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let source = include_str!("../tests/math-layout.md");
    let doc = Document::parse(root, &root.join("regression.md"), "fixture", source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&doc, "math-layout", directory)?;
    let original = fs::read_to_string(directory.join("math-layout.typ"))?;
    let metadata = typesetter.compile("math-layout", directory)?;
    crate::semantics::verify(&doc, &metadata, tools, directory, "math-layout")?;
    let pdf = PdfCheck::read(&directory.join("math-layout.pdf"), directory, "math-layout")?;
    pdf.validate(&doc, &metadata, directory, "math-layout", false)?;
    geometry(&pdf, &metadata, directory, "math-layout")?;
    checks.push(json!({"case":"math-array-rules-aligned-gutters-concatenation-probability-and-punctuation","status":"pass"}));
    for (name, from, to) in [
        ("math-no-gutter", "#h(1.5em)", "#h(0em)"),
        ("math-no-rules", "stroke: 0.4pt", "stroke: 0pt"),
        (
            "math-nonbinary-join",
            "class(\"binary\", bar.v.double)",
            "bar.v.double",
        ),
        (
            "math-probability-break",
            r"Y = y\,G = g",
            r"Y = y\,#linebreak() G = g",
        ),
    ] {
        let changed = original.replace(from, to);
        if changed == original {
            return Err(Failure::new(
                "PDF-REGRESSION",
                format!("{name}: mutation did not match"),
            ));
        }
        fs::write(directory.join(format!("{name}.typ")), changed)?;
        let metadata = typesetter.compile(name, directory)?;
        let pdf = PdfCheck::read(&directory.join(format!("{name}.pdf")), directory, name)?;
        refused(
            name,
            "PDF-MATH-LAYOUT",
            geometry(&pdf, &metadata, directory, name),
            checks,
        )?;
    }
    part_spacing(&typesetter, &original, directory, checks)?;
    display_mode(&typesetter, &doc, &original, tools, directory, checks)?;
    unsafe_breaks(root, tools, directory, checks)?;
    short_probability(root, tools, directory, checks)?;
    relation_wrap(root, tools, directory, checks)?;
    norm_wrapping(root, tools, directory, checks)?;
    term_column(root, tools, directory, checks)
}

/// The A4 side margin of the document template.
const MARGIN: f64 = 20.0 / 25.4 * 72.0;

fn display_mode(
    typesetter: &Typesetter<'_>,
    doc: &Document,
    original: &str,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let start = original
        .find("#mhfe-math(\"math-13\",")
        .ok_or_else(|| bad("Missing tagged aligned fixture"))?;
    let end = start
        + original[start..]
            .find("]#mhfe-math-end(\"math-13\")")
            .ok_or_else(|| bad("Missing aligned fixture end"))?;
    let fragment = &original[start..end];
    let first = fragment
        .find('$')
        .ok_or_else(|| bad("Missing aligned delimiter"))?;
    let last = fragment
        .rfind('$')
        .ok_or_else(|| bad("Missing aligned delimiter"))?;
    let changed = format!(
        "{}{}${}${}{}",
        &original[..start],
        &fragment[..first],
        fragment[first + 1..last].trim(),
        &fragment[last + 1..],
        &original[end..]
    );
    fs::write(directory.join("math-display-lost.typ"), &changed)?;
    let metadata = typesetter.compile("math-display-lost", directory)?;
    refused(
        "math-display-lost",
        "PDF-MATH-LAYOUT",
        crate::semantics::verify(doc, &metadata, tools, directory, "math-display-lost"),
        checks,
    )?;
    let joint = changed.replacen(
        "#mhfe-math(\"math-13\", display: true",
        "#mhfe-math(\"math-13\", display: false",
        1,
    );
    fs::write(directory.join("math-display-metadata-lost.typ"), joint)?;
    let metadata = typesetter.compile("math-display-metadata-lost", directory)?;
    refused(
        "math-display-metadata-lost",
        "PDF-MATH-LAYOUT",
        crate::semantics::verify(
            doc,
            &metadata,
            tools,
            directory,
            "math-display-metadata-lost",
        ),
        checks,
    )
}

fn geometry(pdf: &PdfCheck, metadata: &[Value], directory: &Path, name: &str) -> Result<()> {
    let aligned = words(pdf, metadata, "math-1")?;
    let left = aligned
        .iter()
        .filter(|w| w.text == "256]")
        .min_by(|a, b| a.left.total_cmp(&b.left))
        .ok_or_else(|| bad("Missing aligned column"))?;
    let next = aligned
        .iter()
        .filter(|w| w.left > left.right && (w.top - left.top).abs() < 2.0)
        .min_by(|a, b| a.left.total_cmp(&b.left))
        .ok_or_else(|| bad("Missing paired column"))?;
    if next.left - left.right < 12.0 {
        return Err(bad("Equation pairs have no visible gutter"));
    }
    let concat = words(pdf, metadata, "math-3")?;
    let bars: Vec<_> = concat
        .iter()
        .filter(|w| w.text.contains(['‖', '∥']))
        .collect();
    if bars.len() != 4 {
        return Err(bad("Missing concatenation signs"));
    }
    for bar in bars {
        if !["‖", "∥"].contains(&bar.text.as_str()) {
            return Err(bad("Concatenation touches an operand"));
        }
        let left = concat
            .iter()
            .filter(|w| w.right <= bar.left && w.bottom > bar.top && w.top < bar.bottom)
            .map(|w| w.right)
            .max_by(f64::total_cmp)
            .ok_or_else(|| bad("Missing left operand"))?;
        let right = concat
            .iter()
            .filter(|w| w.left >= bar.right && w.bottom > bar.top && w.top < bar.bottom)
            .map(|w| w.left)
            .min_by(f64::total_cmp)
            .ok_or_else(|| bad("Missing right operand"))?;
        let (a, b) = (bar.left - left, right - bar.right);
        if a < 1.5 || b < 1.5 || (a - b).abs() > 0.8 {
            return Err(bad("Concatenation spacing is asymmetric"));
        }
    }
    probabilities(pdf, metadata)?;
    column_alignment(pdf, metadata)?;
    array_rules(pdf, metadata, directory, name)
}

fn probabilities(pdf: &PdfCheck, metadata: &[Value]) -> Result<()> {
    for id in ["math-4", "math-5"] {
        let region = words(pdf, metadata, id)?;
        let (left, width) = container(metadata, id)?;
        if region
            .iter()
            .any(|w| w.left < left - 1.0 || w.right > left + width + 1.0)
        {
            return Err(bad("Equation overflows its text container"));
        }
        let first = region
            .iter()
            .find(|w| layout::normalized(&w.text).starts_with("Pr[Y"))
            .ok_or_else(|| bad("Missing probability left side"))?;
        let last = region
            .iter()
            .find(|w| layout::normalized(&w.text) == "g]")
            .ok_or_else(|| bad("Missing probability closing fence"))?;
        if (first.top - last.top).abs() > 1.0 {
            return Err(bad("Probability brackets were split across lines"));
        }
        if !region.iter().any(|w| w.text.ends_with("],")) {
            return Err(bad("Sentence punctuation detached from its equation"));
        }
    }
    Ok(())
}

fn container(metadata: &[Value], id: &str) -> Result<(f64, f64)> {
    let mut blocks = Vec::new();
    let mut current = "";
    for record in metadata {
        match record["kind"].as_str() {
            Some("block-start") => blocks.push(layout::position(&record["pos"])?),
            Some("block-end") => {
                blocks.pop();
            }
            Some("math-start") => current = record["id"].as_str().unwrap_or_default(),
            Some("math-promoted") if current == id => {
                let left = blocks
                    .last()
                    .ok_or_else(|| bad("Missing enclosing paragraph"))?
                    .x;
                let width = layout::length(&record["width"])?;
                let expected = layout::PAGE_WIDTH - 20.0 / 25.4 * 72.0 - left;
                if (width - expected).abs() > 0.2 {
                    return Err(bad(
                        "Measured container width differs from its enclosing paragraph",
                    ));
                }
                return Ok((left, width));
            }
            _ => (),
        }
    }
    Err(bad("Wide probability was not promoted"))
}

fn column_alignment(pdf: &PdfCheck, metadata: &[Value]) -> Result<()> {
    let region = words(pdf, metadata, "math-12")?;
    let word = |text: &str| {
        region
            .iter()
            .find(|w| w.text == text)
            .copied()
            .ok_or_else(|| bad("Missing alignment fixture cell"))
    };
    if (word("1")?.left - word("111")?.left).abs() > 0.2
        || (word("22")?.left + word("22")?.right - word("2")?.left - word("2")?.right).abs() > 0.4
        || (word("333")?.right - word("3")?.right).abs() > 0.2
    {
        return Err(bad("Array left, centre or right alignment changed"));
    }
    Ok(())
}

fn array_rules(pdf: &PdfCheck, metadata: &[Value], directory: &Path, name: &str) -> Result<()> {
    let (start, end) = region_bounds(metadata, "math-2")?;
    if start.page != end.page {
        return Err(bad("Array split across pages"));
    }
    let image = directory.join(format!("{name}-rules"));
    process(
        "pdftoppm",
        [
            OsStr::new("-f"),
            OsStr::new(&start.page.to_string()),
            OsStr::new("-singlefile"),
            OsStr::new("-r"),
            OsStr::new("96"),
            OsStr::new("-png"),
            directory.join(format!("{name}.pdf")).as_os_str(),
            image.as_os_str(),
        ],
        None,
        None,
    )?;
    let (vertical, horizontal) = Raster::read(&image.with_extension("png"))?.rules(start, end);
    if vertical.len() != 3 || horizontal.len() != 1 {
        return Err(bad("Array rules are missing from the PDF raster"));
    }
    let cells = words(pdf, metadata, "math-2")?;
    let row = cells
        .iter()
        .find(|w| w.text == "12")
        .ok_or_else(|| bad("Missing first array row"))?;
    let header_bottom = cells
        .iter()
        .filter(|w| w.text == "words" || w.text == "if")
        .map(|w| w.bottom)
        .max_by(f64::total_cmp)
        .ok_or_else(|| bad("Missing array heading"))?;
    if horizontal[0] < header_bottom - 1.0 || horizontal[0] > row.top + 1.0 {
        return Err(bad("Array rule is not below its heading"));
    }
    for number in ["12", "15", "18", "21"] {
        let row = cells
            .iter()
            .find(|w| w.text == number)
            .ok_or_else(|| bad("Missing array data row"))?;
        let row_words: Vec<_> = cells
            .iter()
            .filter(|w| (w.top - row.top).abs() < 2.0)
            .collect();
        let ends: Vec<_> = row_words.iter().filter(|w| w.text.ends_with(']')).collect();
        let starts: Vec<_> = row_words
            .iter()
            .filter(|w| {
                layout::normalized(&w.text).starts_with('X') || layout::normalized(&w.text) == "V"
            })
            .collect();
        if ends.len() != 2 || starts.len() != 3 {
            return Err(bad("Array cell boundaries changed"));
        }
        for (index, left) in [row.right, ends[0].right, ends[1].right]
            .into_iter()
            .enumerate()
        {
            if vertical[index] <= left || vertical[index] >= starts[index].left {
                return Err(bad("Array separators cross cell contents"));
            }
        }
    }
    Ok(())
}

fn words<'a>(pdf: &'a PdfCheck, metadata: &[Value], id: &str) -> Result<Vec<&'a Word>> {
    let (start, end) = region_bounds(metadata, id)?;
    Ok(pdf
        .words
        .iter()
        .filter(|w| {
            w.page >= start.page
                && w.page <= end.page
                && (w.page != start.page || w.top >= start.y - 2.0)
                && (w.page != end.page || w.top < end.y + 1.0)
        })
        .collect())
}

fn region_bounds(metadata: &[Value], id: &str) -> Result<(Position, Position)> {
    let ranges = crate::pdf::ranges(metadata, "math-start", "math-end")?;
    ranges
        .get(id)
        .and_then(|v| v.first())
        .copied()
        .ok_or_else(|| bad("Missing mathematical range"))
}

fn bad(message: &str) -> Failure {
    Failure::new("PDF-MATH-LAYOUT", message)
}

pub(crate) fn seed_arguments(pdf: &PdfCheck) -> Result<()> {
    let mnemonic = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text).contains("mnemonic"))
        .ok_or_else(|| bad("Missing seed argument"))?;
    let passphrase = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text).starts_with("UTF8(NFKD(q)"))
        .ok_or_else(|| bad("Missing passphrase argument"))?;
    if mnemonic.page != passphrase.page || (mnemonic.top - passphrase.top).abs() > 2.0 {
        return Err(bad("A seed function argument was split internally"));
    }
    Ok(())
}

fn unsafe_breaks(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let probability = format!(
        "# Indivisible probability\n\n$`\\mathop{{\\mathrm{{Pr}}}}\\nolimits [ \\text{{{}}}, \\text{{{}}} ]`$",
        "A".repeat(100),
        "B".repeat(100)
    );
    let last_argument = format!(
        "# Wide last argument\n\n$`f(a,\\text{{{}}})`$",
        "B".repeat(150)
    );
    let nested_norm = format!(
        "# Indivisible nested norm\n\n$`f(\\Vert \\text{{{}}}+\\text{{{}}}\\Vert,c)`$",
        "A".repeat(70),
        "B".repeat(70)
    );
    let scaled_norm = format!(
        "# Indivisible scaled norm\n\n$`\\bigl\\Vert \\text{{{}}}+\\text{{{}}}\\bigr\\Vert`$",
        "A".repeat(70),
        "B".repeat(70)
    );
    let mixed_norm = format!(
        "# Indivisible mixed norm\n\n$`\\lvert x+\\Vert \\text{{{}}}+\\text{{{}}}\\Vert\\rvert`$",
        "A".repeat(70),
        "B".repeat(70)
    );
    let indexed_modulus = format!(
        "# Indivisible indexed modulus\n\n$`\\lvert x+\\lvert \\text{{{}}}+\\text{{{}}}\\rvert_p+w\\rvert_q`$",
        "A".repeat(70),
        "B".repeat(70)
    );
    for (name, source, message) in [
        (
            "math-no-safe-break",
            probability,
            "Wide equation has no safe outer break",
        ),
        (
            "math-wide-last-argument",
            last_argument,
            "An indivisible equation segment exceeds its container",
        ),
        (
            "math-wide-nested-norm",
            nested_norm,
            "An indivisible equation segment exceeds its container",
        ),
        (
            "math-wide-scaled-norm",
            scaled_norm,
            "Wide equation has no safe outer break",
        ),
        (
            "math-wide-mixed-norm",
            mixed_norm,
            "Wide equation has no safe outer break",
        ),
        (
            "math-wide-indexed-modulus",
            indexed_modulus,
            "Wide equation has no safe outer break",
        ),
    ] {
        let doc = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
        let typesetter = Typesetter::new(tools, root);
        typesetter.source(&doc, name, directory)?;
        match typesetter.compile(name, directory) {
            Err(error) if error.to_string().contains(message) => {
                refused(name, "PDF-PROCESS", Err(error), checks)?
            }
            Err(error) => return Err(error),
            Ok(_) => return Err(bad("Unsafe line breaking was accepted")),
        }
    }
    Ok(())
}

fn short_probability(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let source = "# Short inline probability\n\nAn otherwise ordinary sentence with some preceding words. An otherwise ordinary sentence with some preceding words. An otherwise ordinary sentence with some preceding words. $`\\mathop{\\mathrm{Pr}}\\nolimits [Y=y,G=g]=2^{-256}\\cdot p_1+\\frac{q_G}{2^{128}}`$, continues here.\n";
    let doc = Document::parse(root, &root.join("regression.md"), "fixture", source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&doc, "short-inline", directory)?;
    let original = fs::read_to_string(directory.join("short-inline.typ"))?;
    let metadata = typesetter.compile("short-inline", directory)?;
    crate::semantics::verify(&doc, &metadata, tools, directory, "short-inline")?;
    let pdf = PdfCheck::read(
        &directory.join("short-inline.pdf"),
        directory,
        "short-inline",
    )?;
    pdf.validate(&doc, &metadata, directory, "short-inline", false)?;
    short_fences(&pdf)?;
    checks.push(json!({"case":"short-probability-fences-at-paragraph-wrap","status":"pass"}));
    // Damage the fence guard so that the only line-break opportunities lie inside brackets.
    let changed = original.replace(
        "if depth != 0 or bars.len() > 0 or not (relation",
        "if depth == 0 or not (relation",
    );
    if changed == original {
        return Err(bad("Short-probability mutation did not match"));
    }
    fs::write(directory.join("short-inline-break.typ"), changed)?;
    typesetter.compile("short-inline-break", directory)?;
    let pdf = PdfCheck::read(
        &directory.join("short-inline-break.pdf"),
        directory,
        "short-inline-break",
    )?;
    refused(
        "short-inline-break",
        "PDF-MATH-LAYOUT",
        short_fences(&pdf),
        checks,
    )
}

/// Inline equations that may wrap must keep their width when they do not.
fn part_spacing(
    typesetter: &Typesetter,
    original: &str,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let checked = original.replace(
        "#let mhfe-check-parts = false",
        "#let mhfe-check-parts = true",
    );
    if checked == original {
        return Err(bad("Part-spacing check flag did not match"));
    }
    fs::write(directory.join("math-parts.typ"), &checked)?;
    let metadata = typesetter.compile("math-parts", directory)?;
    let split: Vec<_> = metadata
        .iter()
        .filter(|v| v["kind"] == "math-parts")
        .filter_map(|v| v["id"].as_str())
        .collect();
    // The norms may wrap only after a plus sign between them.
    if split != ["math-10", "math-14", "math-15", "math-16", "math-17"] {
        return Err(bad(
            "Inline equations were not split at their outer operators",
        ));
    }
    checks.push(json!({"case":"inline-equation-parts-keep-equation-width","status":"pass"}));
    let changed = checked.replace("5em / 18", "6em / 18");
    if changed == checked {
        return Err(bad("Relation-spacing mutation did not match"));
    }
    fs::write(directory.join("math-parts-spacing.typ"), changed)?;
    match typesetter.compile("math-parts-spacing", directory) {
        Err(error)
            if error
                .to_string()
                .contains("Inline equation parts change its spacing") =>
        {
            refused("math-parts-spacing", "PDF-PROCESS", Err(error), checks)
        }
        Err(error) => Err(error),
        Ok(_) => Err(bad("Changed inline-equation spacing was accepted")),
    }
}

fn relation_wrap(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    // The filler places the outer relation at the end of a full line.
    let source = format!(
        "# Inline wrap after a relation\n\n{}$`\\mathop{{\\mathrm{{Pr}}}}\\nolimits [Y=y,G=g]=2^{{-256}}\\cdot p_1+\\frac{{q_G}}{{2^{{128}}}}`$, continues here.\n",
        "Words ".repeat(25)
    );
    let doc = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&doc, "relation-wrap", directory)?;
    let original = fs::read_to_string(directory.join("relation-wrap.typ"))?;
    let metadata = typesetter.compile("relation-wrap", directory)?;
    crate::semantics::verify(&doc, &metadata, tools, directory, "relation-wrap")?;
    let pdf = PdfCheck::read(
        &directory.join("relation-wrap.pdf"),
        directory,
        "relation-wrap",
    )?;
    pdf.validate(&doc, &metadata, directory, "relation-wrap", false)?;
    relation_at_line_end(&pdf)?;
    checks.push(json!({"case":"inline-equation-wraps-after-outer-relation","status":"pass"}));
    // Spacing that is not weak stays at the line end instead of disappearing.
    let changed = original.replace("h(gap, weak: true)", "h(gap)");
    if changed == original {
        return Err(bad("Relation-wrap mutation did not match"));
    }
    fs::write(directory.join("relation-wrap-kept-space.typ"), changed)?;
    typesetter.compile("relation-wrap-kept-space", directory)?;
    let pdf = PdfCheck::read(
        &directory.join("relation-wrap-kept-space.pdf"),
        directory,
        "relation-wrap-kept-space",
    )?;
    refused(
        "relation-wrap-kept-space",
        "PDF-MATH-LAYOUT",
        relation_at_line_end(&pdf),
        checks,
    )
}

fn relation_at_line_end(pdf: &PdfCheck) -> Result<()> {
    let opening = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text).starts_with("Pr[Y"))
        .ok_or_else(|| bad("Missing probability opening"))?;
    let closing = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text) == "g]")
        .ok_or_else(|| bad("Missing probability closing"))?;
    if opening.page != closing.page || (opening.top - closing.top).abs() > 1.0 {
        return Err(bad("Probability brackets were split across lines"));
    }
    let same_line = |w: &&Word| w.page == closing.page && (w.top - closing.top).abs() < 1.0;
    let relation = pdf
        .words
        .iter()
        .filter(|w| same_line(w) && w.left > closing.right && w.text == "=")
        .min_by(|a, b| a.left.total_cmp(&b.left))
        .ok_or_else(|| bad("The outer relation is not on the line of its left side"))?;
    if pdf
        .words
        .iter()
        .any(|w| same_line(&w) && w.left > relation.right)
    {
        return Err(bad(
            "An inline equation did not wrap after its outer relation",
        ));
    }
    // The next line includes the raised numerator of its fraction.
    let next = pdf
        .words
        .iter()
        .filter(|w| {
            w.page == closing.page && w.top > closing.bottom && w.top < closing.bottom + 12.0
        })
        .min_by(|a, b| a.left.total_cmp(&b.left))
        .ok_or_else(|| bad("Missing the right side of the wrapped equation"))?;
    if (relation.right - (layout::PAGE_WIDTH - MARGIN)).abs() > 0.5
        || (next.left - MARGIN).abs() > 0.5
    {
        return Err(bad("Spacing at an inline equation wrap was not removed"));
    }
    Ok(())
}

fn short_fences(pdf: &PdfCheck) -> Result<()> {
    let first = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text).starts_with("Pr[Y"))
        .ok_or_else(|| bad("Missing short probability opening"))?;
    let last = pdf
        .words
        .iter()
        .find(|w| layout::normalized(&w.text) == "g]")
        .ok_or_else(|| bad("Missing short probability closing"))?;
    if first.page != last.page || (first.top - last.top).abs() > 1.0 {
        return Err(bad("A short probability was split at paragraph wrapping"));
    }
    Ok(())
}

fn norm_wrapping(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    for (name, expression, filler, from, to) in [
        (
            "scaled-norm-wrap",
            r"\bigl\Vert x_1+x_2+x_3+x_4\bigr\Vert",
            10,
            "if atom.func() == scale { atom = atom.body }",
            "if false { atom = atom.body }",
        ),
        (
            "nested-norm-wrap",
            r"\lvert x+\Vert y+z\Vert\rvert",
            11,
            "if bars.len() > 0 and bars.last() == text",
            "if bars.len() > 0",
        ),
        (
            "same-kind-norm-wrap",
            r"\lvert x+\lvert y+z\rvert+w\rvert",
            11,
            "if role == \"opening\"",
            "if false",
        ),
        (
            "sized-same-kind-norm-wrap",
            r"\bigl\lvert x+\bigl\lvert y+z\bigr\rvert+w\bigr\rvert",
            11,
            "if role == \"opening\"",
            "if false",
        ),
        (
            "indexed-same-kind-norm-wrap",
            r"\lvert x+\lvert y+z\rvert_p+w\rvert_q",
            11,
            "if role == \"opening\"",
            "if false",
        ),
    ] {
        // The public review reproducer puts the opening fence near a line end.
        let source = format!(
            "# Norm wrapping\n\n{} {filler}: {}$`{expression}`$, ends.\n",
            if filler == 10 { "scaled" } else { "nested" },
            "Words ".repeat(filler),
        );
        let doc = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
        let typesetter = Typesetter::new(tools, root);
        typesetter.source(&doc, name, directory)?;
        let original = fs::read_to_string(directory.join(format!("{name}.typ")))?;
        let metadata = typesetter.compile(name, directory)?;
        crate::semantics::verify(&doc, &metadata, tools, directory, name)?;
        let pdf = PdfCheck::read(&directory.join(format!("{name}.pdf")), directory, name)?;
        pdf.validate(&doc, &metadata, directory, name, false)?;
        norm_on_one_line(&pdf)?;
        checks.push(json!({"case":name,"status":"pass"}));
        // Fault: restore the delimiter-recognition bug; glyph checks alone miss the wrap.
        let changed = original.replace(from, to);
        if changed == original {
            return Err(bad("Norm-wrapping mutation did not match"));
        }
        let broken = format!("{name}-broken");
        fs::write(directory.join(format!("{broken}.typ")), changed)?;
        typesetter.compile(&broken, directory)?;
        let pdf = PdfCheck::read(&directory.join(format!("{broken}.pdf")), directory, &broken)?;
        refused(&broken, "PDF-MATH-LAYOUT", norm_on_one_line(&pdf), checks)?;
    }
    Ok(())
}

fn norm_on_one_line(pdf: &PdfCheck) -> Result<()> {
    let bars: Vec<_> = pdf
        .words
        .iter()
        .filter(|word| word.text.contains(['|', '‖', '∥']))
        .collect();
    let first = bars.first().ok_or_else(|| bad("Missing opening norm"))?;
    let last = bars.last().ok_or_else(|| bad("Missing closing norm"))?;
    if bars.len() < 2 || first.page != last.page || (first.top - last.top).abs() > 1.0 {
        return Err(bad("A norm was split inside its vertical fences"));
    }
    Ok(())
}

fn term_column(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let source = "# Wide mathematical term\n\n| Term | Event |\n| --- | --- |\n| `(12·p_1·k_A + 66 + q_B)/2^128` | A fresh salt or half of the real chain hits an earlier query. |\n";
    let doc = Document::parse(root, &root.join("regression.md"), "fixture", source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&doc, "term-column", directory)?;
    let original = fs::read_to_string(directory.join("term-column.typ"))?;
    let metadata = typesetter.compile("term-column", directory)?;
    crate::semantics::verify(&doc, &metadata, tools, directory, "term-column")?;
    PdfCheck::read(&directory.join("term-column.pdf"), directory, "term-column")?.validate(
        &doc,
        &metadata,
        directory,
        "term-column",
        false,
    )?;
    checks.push(json!({"case":"indivisible-term-fits-its-table-column","status":"pass"}));
    let changed = original.replace("40%", "29%");
    if changed == original {
        return Err(bad("Term-column mutation did not match"));
    }
    fs::write(directory.join("term-column-narrow.typ"), changed)?;
    match typesetter.compile("term-column-narrow", directory) {
        Err(error)
            if error
                .to_string()
                .contains("Wide equation has no safe outer break") =>
        {
            refused("term-column-narrow", "PDF-PROCESS", Err(error), checks)
        }
        Err(error) => Err(error),
        Ok(_) => Err(bad("Narrow indivisible-term column was accepted")),
    }
}
