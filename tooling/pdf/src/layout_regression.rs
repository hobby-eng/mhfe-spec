use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::pdf::PdfCheck;
use crate::process::Toolchain;
use crate::regression::refused;
use crate::typeset::Typesetter;
use serde_json::{Value, json};
use std::fs;
use std::path::Path;

/// Checks visible heading gaps and the complete BIP preamble against actual PDFs.
pub(crate) fn run(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let source = "A preceding paragraph.\n\n## Single internal heading\n\nFollowing text with a visible gap.\n\nA second independent paragraph follows.\n\n```text\nBIP: ?\nLayer: Applications\nTitle: Public layout fixture\nAuthors: Public test\nStatus: Draft\nType: Specification\nAssigned: ?\nLicense: CC-BY-4.0\nVersion: 0.7.0\nRequires: 39\n```\n";
    let source = format!(
        "{source}\n## Heading before a tall formula\n\n```math\n\\begin{{aligned}}\nm(\\mathrm{{MEM}})&=(2+\\mathrm{{MEM}}\\bmod 2)\\cdot 2^{{20+\\lfloor\\mathrm{{MEM}}/2\\rfloor}}\\ \\mathrm{{KiB}},&&\\mathrm{{MEM}}\\in\\{{0,\\ldots,21\\}},\\\\\nt(\\mathrm{{PIM}})&=12\\cdot(\\mathrm{{PIM}}+1),&&\\mathrm{{PIM}}\\in\\{{0,\\ldots,1023\\}}.\n\\end{{aligned}}\n```\n"
    );
    let document = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&document, "heading-spacing", directory)?;
    let path = directory.join("heading-spacing.typ");
    let original = fs::read_to_string(&path)?;
    let metadata = typesetter.compile("heading-spacing", directory)?;
    PdfCheck::read(
        &directory.join("heading-spacing.pdf"),
        directory,
        "heading-spacing",
    )?
    .validate(&document, &metadata, directory, "heading-spacing", false)?;
    for (name, from, to) in [
        ("heading-no-top-gap", "above: 24pt", "above: 0pt"),
        ("heading-no-bottom-gap", "below: 18pt", "below: 0pt"),
    ] {
        fs::write(
            directory.join(format!("{name}.typ")),
            original.replace(from, to),
        )?;
        let changed = typesetter.compile(name, directory)?;
        refused(
            name,
            "PDF-HEADING",
            PdfCheck::read(&directory.join(format!("{name}.pdf")), directory, name)?
                .validate(&document, &changed, directory, name, false)
                .map(|_| ()),
            checks,
        )?;
    }
    fs::write(
        directory.join("bip-preamble.typ"),
        original.replacen("#mhfe-code(\"block", "#v(560pt)\n#mhfe-code(\"block", 1),
    )?;
    let metadata = typesetter.compile("bip-preamble", directory)?;
    PdfCheck::read(
        &directory.join("bip-preamble.pdf"),
        directory,
        "bip-preamble",
    )?
    .validate(&document, &metadata, directory, "bip-preamble", false)?;
    let start = metadata
        .iter()
        .find(|v| v["kind"] == "code-start")
        .ok_or_else(|| Failure::new("PDF-REGRESSION", "Missing BIP preamble boundary"))?;
    if start["pos"]["page"] != 2 {
        return Err(Failure::new(
            "PDF-REGRESSION",
            "The BIP preamble did not move intact",
        ));
    }
    let mut split = metadata.clone();
    for record in &mut split {
        if record["kind"] == "code-end" {
            record["pos"]["page"] = 3.into();
        }
    }
    refused(
        "split-bip-preamble",
        "PDF-CODE",
        crate::layout::coverage(&document, &split),
        checks,
    )?;
    checks.push(json!({"case":"visible-heading-gaps-and-whole-bip-preamble","status":"pass"}));
    oversized(root, tools, directory, checks)
}

fn oversized(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let mut source = String::from("# Oversized table\n\n| Description | Value |\n| --- | --- |\n");
    for i in 0..90 {
        source.push_str(&format!("| Row {i} | A value |\n"));
    }
    let document = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&document, "oversized-table", directory)?;
    let result = typesetter
        .compile("oversized-table", directory)
        .and_then(|metadata| {
            PdfCheck::read(
                &directory.join("oversized-table.pdf"),
                directory,
                "oversized-table",
            )?
            .validate(&document, &metadata, directory, "oversized-table", false)
            .map(|_| ())
        });
    match result {
        Err(error)
            if error.to_string().starts_with("PDF-WARNING:")
                || error.to_string().starts_with("PDF-GLYPH:")
                || error.to_string().starts_with("PDF-TABLE:")
                || error.to_string().starts_with("PDF-LAYOUT:") =>
        {
            checks.push(json!({"case":"oversized-whole-table-refused","status":"pass","refusal":error.to_string()}));
            Ok(())
        }
        Err(error) => Err(error),
        Ok(()) => Err(Failure::new(
            "PDF-REGRESSION",
            "An oversized table was accepted",
        )),
    }
}
