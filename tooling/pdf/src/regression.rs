use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::pdf::PdfCheck;
use crate::process::Toolchain;
use crate::typeset::Typesetter;
use serde_json::{Value, json};
use std::fs;
use std::path::Path;

/// Exercises validation failures against real public fixture documents.
pub(crate) fn run(root: &Path, tools: &Toolchain, directory: &Path) -> Result<Vec<Value>> {
    let source = "# Rendering regression\n\nLiteral `filename.txt` and `$x$` stay code. Formula $`x + y`$.\n\n```math\n\\Pr_{\\Gamma_0}[\\text{win}] \\le \\frac{1}{2} + {\\Theta_{0}}^{\\prime} + \\mathop{\\mathrm{SHA-256}}\\nolimits(x) \\tag{R}\n```\n\n| Field | Value |\n| --- | --- |\n| Alpha | beta gamma |\n";
    let document = Document::parse(root, &root.join("regression.md"), "fixture", source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&document, "regression", directory)?;
    let metadata = typesetter.compile("regression", directory)?;
    crate::semantics::verify(&document, &metadata, tools, directory, "regression")?;
    let pdf = PdfCheck::read(&directory.join("regression.pdf"), directory, "regression")?;
    inline_code(directory, "regression")?;
    pdf.validate(&document, &metadata, directory, "regression", false)?;
    let mut checks = vec![json!({"case":"valid-public-fixture","status":"pass"})];
    let incomplete: Vec<_> = metadata
        .iter()
        .filter(|v| v["kind"] != "math-start")
        .cloned()
        .collect();
    refused(
        "missing-math",
        "PDF-COVERAGE",
        crate::layout::coverage(&document, &incomplete),
        &mut checks,
    )?;
    let mut cell = metadata.clone();
    for item in &mut cell {
        if item["kind"] == "cell" {
            item["width"] = "1pt".into();
        }
    }
    refused(
        "narrow-table-cell",
        "PDF-TABLE",
        pdf.validate(&document, &cell, directory, "regression", false)
            .map(|_| ()),
        &mut checks,
    )?;
    let typ = directory.join("regression.typ");
    let original = fs::read_to_string(&typ)?;
    let reordered = original.replacen("stay code", "code stay", 1);
    if reordered == original {
        return Err(Failure::new(
            "PDF-REGRESSION",
            "Prose mutation did not match",
        ));
    }
    fs::write(directory.join("reordered-prose.typ"), reordered)?;
    let changed = typesetter.compile("reordered-prose", directory)?;
    refused(
        "reordered-prose",
        "PDF-PROSE",
        PdfCheck::read(
            &directory.join("reordered-prose.pdf"),
            directory,
            "reordered-prose",
        )?
        .validate(&document, &changed, directory, "reordered-prose", false)
        .map(|_| ()),
        &mut checks,
    )?;
    let broken = original.replace("raw.where(block: true)", "raw");
    if broken == original {
        return Err(Failure::new(
            "PDF-REGRESSION",
            "Inline-code mutation did not match",
        ));
    }
    fs::write(directory.join("inline-code-paragraph.typ"), broken)?;
    typesetter.compile("inline-code-paragraph", directory)?;
    PdfCheck::read(
        &directory.join("inline-code-paragraph.pdf"),
        directory,
        "inline-code-paragraph",
    )?;
    refused(
        "inline-code-paragraph",
        "PDF-INLINE",
        inline_code(directory, "inline-code-paragraph"),
        &mut checks,
    )?;
    for (case, replacement) in [
        ("substituted-math-symbol", "x - y"),
        ("reordered-operands", "y + x"),
        ("added-math-symbol", "x + y !"),
    ] {
        let altered = original.replacen("x + y", replacement, 1);
        if altered == original {
            return Err(Failure::new(
                "PDF-REGRESSION",
                "Glyph mutation did not match its fixture",
            ));
        }
        fs::write(&typ, altered)?;
        let changed = typesetter.compile("regression", directory)?;
        refused(
            case,
            "PDF-MATHML",
            crate::semantics::verify(&document, &changed, tools, directory, case),
            &mut checks,
        )?;
        let changed_pdf = PdfCheck::read(&directory.join("regression.pdf"), directory, case)?;
        if case != "reordered-operands" {
            refused(
                case,
                "PDF-TEXT",
                changed_pdf
                    .validate(&document, &metadata, directory, case, false)
                    .map(|_| ()),
                &mut checks,
            )?;
        }
    }
    fs::write(directory.join("truncated.pdf"), b"%PDF-1.7\ntruncated")?;
    refused(
        "truncated-pdf",
        "PDF-PROCESS",
        PdfCheck::read(&directory.join("truncated.pdf"), directory, "truncated").map(|_| ()),
        &mut checks,
    )?;
    for (name, input) in [
        ("unclosed-inline", "$x"),
        ("unclosed-display", "$$x"),
        ("stateful-macro", "```math\n\\def\\x{1}\n```\n"),
    ] {
        refused(
            name,
            "PDF-",
            Document::parse(root, &root.join("regression.md"), "fixture", input, tools).map(|_| ()),
            &mut checks,
        )?;
    }
    long_inline(root, tools, directory, &mut checks)?;
    contents(root, tools, directory, &mut checks)?;
    tables(root, tools, directory, &mut checks)?;
    crate::layout_regression::run(root, tools, directory, &mut checks)?;
    crate::math_layout_regression::run(root, tools, directory, &mut checks)?;
    Ok(checks)
}

fn contents(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    for (name, count) in [("contents-move", 44), ("contents-oversized", 90)] {
        let mut source = String::from("# Contents fixture\n\n");
        for _ in 0..8 {
            source.push_str("A preceding paragraph with enough lines to occupy some of the first page. More words extend this paragraph and leave less space for the contents.\n\n");
        }
        source.push_str("## Contents\n\n");
        for i in 0..count {
            source.push_str(&format!("- [Entry {i}](#end)\n"));
        }
        source.push_str("\n## End\n\nThe final section.\n");
        let document =
            Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
        let typesetter = Typesetter::new(tools, root);
        typesetter.source(&document, name, directory)?;
        let metadata = typesetter.compile(name, directory)?;
        let pdf = PdfCheck::read(&directory.join(format!("{name}.pdf")), directory, name)?;
        pdf.validate(&document, &metadata, directory, name, false)?;
        if name == "contents-move" {
            let marker = metadata
                .iter()
                .find(|v| v["kind"] == "contents-start")
                .ok_or_else(|| Failure::new("PDF-REGRESSION", "Fixture has no contents marker"))?;
            if marker["oversized"] != false {
                return Err(Failure::new(
                    "PDF-REGRESSION",
                    "Contents move fixture must fit one complete page",
                ));
            }
            if marker["pos"]["page"] == 1 {
                return Err(Failure::new(
                    "PDF-REGRESSION",
                    "Contents fixture did not exercise a page move",
                ));
            }
            let path = directory.join(format!("{name}.typ"));
            let crowded =
                fs::read_to_string(path)?.replace("list(spacing: 5pt)", "list(spacing: 1.5pt)");
            fs::write(directory.join("contents-crowded.typ"), crowded)?;
            let changed = typesetter.compile("contents-crowded", directory)?;
            refused(
                "crowded-contents-lines",
                "PDF-CONTENTS",
                PdfCheck::read(
                    &directory.join("contents-crowded.pdf"),
                    directory,
                    "contents-crowded",
                )?
                .validate(&document, &changed, directory, "contents-crowded", false)
                .map(|_| ()),
                checks,
            )?;
        }
        let mut bad = metadata.clone();
        for item in &mut bad {
            if item["kind"] == "contents-start" {
                item["oversized"] = true.into();
                item["pos"]["y"] = "200pt".into();
            }
        }
        refused(
            name,
            "PDF-CONTENTS",
            crate::layout::coverage(&document, &bad),
            checks,
        )?;
        let mut bad = metadata.clone();
        for item in &mut bad {
            if item["kind"] == "contents-body-start" {
                item["pos"]["page"] = 1.into();
            }
        }
        refused(
            "body-on-contents-page",
            "PDF-CONTENTS",
            crate::layout::coverage(&document, &bad),
            checks,
        )?;
    }
    Ok(())
}

pub(crate) fn refused(
    name: &str,
    stage: &str,
    result: Result<()>,
    checks: &mut Vec<Value>,
) -> Result<()> {
    match result {
        Err(error) if error.to_string().starts_with(stage) => {
            checks.push(json!({"case":name,"status":"pass","refusal":error.to_string()}));
            Ok(())
        }
        Err(error) => Err(Failure::new(
            "PDF-REGRESSION",
            format!("{name}: unexpected refusal: {error}"),
        )),
        Ok(()) => Err(Failure::new(
            "PDF-REGRESSION",
            format!("{name}: damaged input was accepted"),
        )),
    }
}

fn tables(root: &Path, tools: &Toolchain, directory: &Path, checks: &mut Vec<Value>) -> Result<()> {
    let mut source = String::from(
        "# Table regression\n\nIntroductory text.\n\n| Supplied with the container | The application admits to recovery |\n| --- | --- |\n",
    );
    for i in 0..4 {
        source.push_str(&format!(
            "| Suite {i} | A longer description with a $`2^r`$ term and several words that need more room than the short labels on the left. |\n"
        ));
    }
    let document = Document::parse(root, &root.join("regression.md"), "fixture", &source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&document, "tables", directory)?;
    let path = directory.join("tables.typ");
    let original = fs::read_to_string(&path)?;
    fs::write(
        &path,
        original.replacen("#mhfe-table(\"block", "#v(560pt)\n#mhfe-table(\"block", 1),
    )?;
    let metadata = typesetter.compile("tables", directory)?;
    crate::semantics::verify(&document, &metadata, tools, directory, "tables")?;
    let pdf = PdfCheck::read(&directory.join("tables.pdf"), directory, "tables")?;
    let result = pdf.validate(&document, &metadata, directory, "tables", false)?;
    let start = metadata
        .iter()
        .find(|v| v["kind"] == "table-start")
        .ok_or_else(|| Failure::new("PDF-REGRESSION", "Missing table boundary"))?;
    if result.pages < 2 || start["pos"]["page"] != 2 {
        return Err(Failure::new(
            "PDF-REGRESSION",
            "The table fixture did not move intact to a new page",
        ));
    }
    let columns: Vec<_> = metadata
        .iter()
        .filter(|v| v["kind"] == "cell" && v["row"] == 0)
        .collect();
    if columns.len() != 2
        || crate::layout::length(&columns[1]["width"])?
            < 2.0 * crate::layout::length(&columns[0]["width"])?
    {
        return Err(Failure::new(
            "PDF-REGRESSION",
            "The descriptive table column is too narrow",
        ));
    }
    let mut broken = metadata.clone();
    for record in &mut broken {
        if record["kind"] == "table-end" {
            record["pos"]["page"] = 3.into();
        }
    }
    refused(
        "split-whole-table",
        "PDF-TABLE",
        crate::layout::coverage(&document, &broken),
        checks,
    )?;
    checks.push(json!({"case":"whole-table-move-and-prose-column-width","status":"pass"}));
    Ok(())
}

fn long_inline(
    root: &Path,
    tools: &Toolchain,
    directory: &Path,
    checks: &mut Vec<Value>,
) -> Result<()> {
    let source = r#"# Long inline equation

- `S : {0,1}^256 × Qw → {0,1}^512`, the BIP39 seed
  `PBKDF2-HMAC-SHA512(UTF8(NFKD(M(e))), "mnemonic" ‖ UTF8(NFKD(q)), 2048, 512)` computed from the
  phrase `M(e)` of `e` and the passphrase `q`. `Qw` is the set of normalized passphrases. `M(e)`
  contains the checksum `Trunc_8(SHA-256(e))` and is an injective encoding of `e`, so modelling `S`
  as a function of `(e, q)` loses nothing. One query stands for one seed computation of 2,048
  iterations, and the budget `k_S` counts these computations as the second expensive resource.
"#;
    let document = Document::parse(root, &root.join("regression.md"), "fixture", source, tools)?;
    let typesetter = Typesetter::new(tools, root);
    typesetter.source(&document, "long-inline", directory)?;
    let metadata = typesetter.compile("long-inline", directory)?;
    crate::semantics::verify(&document, &metadata, tools, directory, "long-inline")?;
    let pdf = PdfCheck::read(&directory.join("long-inline.pdf"), directory, "long-inline")?;
    pdf.validate(&document, &metadata, directory, "long-inline", false)?;
    let generated = fs::read_to_string(directory.join("long-inline.typ"))?;
    crate::math_layout_regression::seed_arguments(&pdf)?;
    let unbroken = generated.replace(
        "mhfe-fit-inline(rendered, tail: tail, id: id, width: width)",
        "{ rendered; tail }",
    );
    fs::write(directory.join("long-inline-unbroken.typ"), unbroken)?;
    typesetter.compile("long-inline-unbroken", directory)?;
    let changed = PdfCheck::read(
        &directory.join("long-inline-unbroken.pdf"),
        directory,
        "long-inline-unbroken",
    )?;
    refused(
        "unbroken-long-inline",
        "PDF-MATH-LAYOUT",
        crate::math_layout_regression::seed_arguments(&changed),
        checks,
    )?;
    checks.push(json!({"case":"wide-inline-function-two-line-layout","status":"pass"}));
    Ok(())
}

fn inline_code(directory: &Path, name: &str) -> Result<()> {
    let source = fs::read_to_string(directory.join(format!("{name}-pdf-text.html")))?;
    let xml = roxmltree::Document::parse_with_options(
        &source,
        roxmltree::ParsingOptions {
            allow_dtd: true,
            ..Default::default()
        },
    )
    .map_err(|e| Failure::new("PDF-XML", e.to_string()))?;
    let same_line = xml
        .descendants()
        .filter(|node| node.has_tag_name("line"))
        .any(|line| {
            let words: Vec<_> = line
                .children()
                .filter(|node| node.has_tag_name("word"))
                .filter_map(|word| word.text())
                .collect();
            words.contains(&"Literal") && words.contains(&"filename.txt")
        });
    if !same_line {
        return Err(Failure::new(
            "PDF-INLINE",
            "An inline code span unexpectedly starts a paragraph",
        ));
    }
    Ok(())
}
