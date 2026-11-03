use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::process::json_file;
use serde_json::{Value, json};
use std::path::Path;

/// A retained predecessor-parser/KaTeX reference independent of Pandoc.
pub(crate) fn verify(
    name: &str,
    document: &Document,
    evidence: &[Value],
    directory: &Path,
) -> Result<()> {
    if !["mhfe-specification", "mhfe-supplement"].contains(&name) {
        return Ok(());
    }
    let fixture: Value =
        serde_json::from_str(include_str!("../tests/independent-math-glyphs.json"))?;
    let entries = fixture["expressions"]
        .as_array()
        .ok_or_else(|| Failure::new("PDF-ORACLE", "Invalid reference corpus"))?;
    let expected = entries
        .iter()
        .filter(|v| v["document"] == name)
        .collect::<Vec<_>>();
    if expected.len() != document.expressions.len() || evidence.len() != expected.len() {
        return Err(Failure::new(
            "PDF-ORACLE",
            "The reference corpus must cover every canonical expression",
        ));
    }
    for ((expected, expression), actual) in expected.iter().zip(&document.expressions).zip(evidence)
    {
        if expected["id"] != expression.id
            || expected["sha256"] != expression.sha256
            || expected["display"] != expression.display
            || normalized(expected["glyphs"].as_str().unwrap_or_default())
                != normalized(actual["typst"]["glyphs"].as_str().unwrap_or_default())
        {
            return Err(Failure::new(
                "PDF-ORACLE",
                format!(
                    "{} differs from the independent retained reference",
                    expression.id
                ),
            ));
        }
    }
    json_file(
        &directory.join(format!("{name}-independent-oracle.json")),
        &json!({"status":"pass","expressions":expected.len(),"fixture":"tooling/pdf/tests/independent-math-glyphs.json"}),
    )?;
    Ok(())
}

fn normalized(source: &str) -> String {
    crate::layout::normalized(source)
        .chars()
        .map(|c| match c {
            '−' | '‐' | '‑' | '–' => '-',
            '∗' => '*',
            '′' => '\'',
            '⋅' => '·',
            '∥' => '‖',
            '∣' => '|',
            '“' | '”' => '"',
            _ => c,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_is_complete_and_does_not_ignore_symbol_order() {
        let fixture: Value =
            serde_json::from_str(include_str!("../tests/independent-math-glyphs.json"))
                .unwrap_or_default();
        assert_eq!(fixture["expressions"].as_array().map(Vec::len), Some(2708));
        assert_ne!(normalized("x+y"), normalized("y+x"));
        assert_ne!(normalized("x+y"), normalized("x-y"));
        assert_ne!(normalized("x+y"), normalized("x+y!"));
    }
}
