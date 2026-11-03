use crate::ascii::{AsciiMath, Conversion, Vocabulary};
use crate::failure::{Failure, Result};
use regex::Regex;

/// Classifies only Markdown code boundaries; ordinary prose stays literal.
pub(crate) struct Notation {
    vocabulary: Vocabulary,
    named_index: Regex,
    literal: Regex,
    mathematical: Regex,
}

pub(crate) enum Inline {
    Literal(Option<String>),
    Math(Conversion),
}

impl Notation {
    pub(crate) fn new() -> Result<Self> {
        Ok(Self {
            vocabulary: Vocabulary::load()?,
            named_index: Regex::new(r"^([a-zA-Z]{2,})_")?,
            literal: Regex::new(
                r"^(?:MHFE-|CC-BY-|v\d+\.\d+|[a-f\d]{32,}$)|(?:\.md|\.txt|\.sh)$|^(?:vectors/|docs/|scripts/|hobby-eng/)",
            )?,
            mathematical: Regex::new(
                r"^[\p{L}]$|[_^=<>+*∈≠≤≥‖⊕∧∨¬Σ⌊⌈]|^(?:\d|-[\d]|[NC]\d|[ΓΔΘ]\d|Pw$|Qw$|ENT$|PIM$|MEM$|Perm$|seed$|Ex$|Cross$|CS$|tau|RoundMask$|xor$|XOR$|[A-Za-z]+\()|[()\[\]{}…]|(?:[A-Z], ){1,}[A-Z]|[\p{L}0-9]/|[\p{L}]'|\s[-−/|·]\s",
            )?,
        })
    }

    pub(crate) fn convert(&self, source: &str) -> Result<Conversion> {
        AsciiMath::convert(source, &self.vocabulary)
    }

    pub(crate) fn inline(&self, source: &str) -> Result<Inline> {
        if let Some(literal) = source.strip_prefix("literal:") {
            return Ok(Inline::Literal(Some(literal.into())));
        }
        if let Some(math) = source.strip_prefix("ascii:") {
            return Ok(Inline::Math(self.convert(math.trim())?));
        }
        if self
            .vocabulary
            .literals
            .iter()
            .any(|literal| literal == source)
            || self.literal.is_match(source)
        {
            return Ok(Inline::Literal(None));
        }
        if let Some(captures) = self.named_index.captures(source) {
            let known = [
                "Pr", "Exp", "Perm", "Inv", "Trunc", "Packed", "Early", "Bad", "Coll",
            ];
            if !known.contains(&&captures[1]) {
                return Err(Failure::new(
                    "PDF-NOTATION",
                    "Ambiguous identifier: use ascii: for mathematics or literal: for code",
                ));
            }
        }
        if self.mathematical.is_match(source) {
            Ok(Inline::Math(self.convert(source)?))
        } else {
            Ok(Inline::Literal(None))
        }
    }

    pub(crate) fn is_math_block(&self, source: &str) -> bool {
        let source = source.trim_start();
        if source.starts_with("BIP:")
            || source
                .strip_prefix("SUITE_ID")
                .is_some_and(|s| s.trim_start().starts_with('='))
        {
            return false;
        }
        source.contains(['_', '^', '=', '≤', '≥', '⊕', '∈'])
    }

    pub(crate) fn block(&self, source: &str) -> Result<(String, serde_json::Value)> {
        let label = Regex::new(r"^([a-z]+(?:[ ,]+[a-z]+)+):\s*(.+)$")?;
        let mut latex = Vec::new();
        let mut converted = Vec::new();
        for line in source.trim().lines().filter(|line| !line.trim().is_empty()) {
            let conversion = if let Some(captures) = label.captures(line) {
                let mut result = self.convert(&captures[2])?;
                result.latex = format!("\\text{{{}: }} {}", &captures[1], result.latex);
                result.tokens.insert(0, format!("{}:", &captures[1]));
                result
            } else {
                self.convert(line.trim())?
            };
            latex.push(conversion.latex.clone());
            converted.push(conversion);
        }
        if latex.is_empty() {
            return Err(Failure::new("PDF-NOTATION", "Empty mathematical block"));
        }
        Ok((
            format!(
                "\\begin{{gathered}}\n{}\n\\end{{gathered}}",
                latex.join(" \\\\\n")
            ),
            serde_json::to_value(converted)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn reproduces_predecessor_conversions_from_independent_evidence() {
        // Fixed expected results were retained from the previous source-bound renderer,
        // before this port. The new implementation does not produce its own expectations.
        let corpus: BTreeMap<String, String> =
            serde_json::from_str(include_str!("../tests/legacy-notation.json")).unwrap();
        let notation = Notation::new().unwrap();
        assert_eq!(corpus.len(), 1040);
        for (source, latex) in corpus {
            assert_eq!(notation.convert(&source).unwrap().latex, latex, "{source}");
        }
    }

    #[test]
    fn refuses_malformed_or_ambiguous_notation() {
        let notation = Notation::new().unwrap();
        for source in [
            "x^",
            "x_",
            "x^(n-1",
            "x_{i]",
            "x_i_j",
            "x^^2",
            "x_{}",
            "R_0^(1)",
            "R^(1)_0",
            "x^)",
            "x_]",
            "x^}",
            "x_⌋",
            "x^+)",
            "x^-{}",
            "x^*",
            "x^/",
            "\"\\alpha\"",
            "\"a{b}\"",
            "x+\\unknown",
            "x🙂y",
            "",
        ] {
            assert!(notation.convert(source).is_err(), "{source}");
        }
        assert!(notation.convert(&"x".repeat(12_001)).is_err());
        assert!(notation.inline("account_index").is_err());
        assert!(notation.block("x=2\ny=x^(").is_err());
    }

    #[test]
    fn preserves_literal_identifiers_and_explicit_choices() {
        let notation = Notation::new().unwrap();
        for source in [
            "MHFE-REPAIR-1",
            "DS_SALT",
            "scripts/build-argon2-wasm.sh",
            "encrypt_key",
            "0x13",
            "literal:x^2",
        ] {
            assert!(matches!(
                notation.inline(source).unwrap(),
                Inline::Literal(_)
            ));
        }
        assert!(!notation.is_math_block("SUITE_ID = ASCII(\"MHFE\")"));
        assert!(notation.is_math_block("m(x) = d_0*x^(n-1) + d_1"));
    }
}
