use crate::failure::{Failure, Result};
use regex::Regex;
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Serialize)]
pub(crate) struct ModulusFence {
    opening: bool,
    scale_percent: u16,
}

impl ModulusFence {
    /// Keeps the original glyph and explicit size, with its mathematical delimiter class.
    pub(crate) fn typst(&self) -> String {
        let body = if self.scale_percent == 100 {
            r"\|".into()
        } else {
            format!(
                "#scale(x: {}%, y: {}%)[$\\|$]",
                self.scale_percent, self.scale_percent
            )
        };
        format!(
            "class(\"{}\", {body})",
            if self.opening { "opening" } else { "closing" }
        )
    }
}

/// Preserve directional modulus roles before Pandoc flattens their identical glyphs.
pub(crate) fn modulus_fences(
    source: &str,
    id: &str,
    aliases: &mut BTreeMap<String, ModulusFence>,
) -> Result<String> {
    if !source.contains("\\lvert") || !source.contains("\\rvert") {
        return Ok(source.into());
    }
    let pattern = Regex::new(
        r"(?:\\(?:left|right|bigl|bigr|Bigl|Bigr|biggl|biggr|Biggl|Biggr)\s*)?\\(?:lvert|rvert)",
    )?;
    // TeX control words end before an index or digit, not at a regex word boundary.
    let fences: Vec<_> = pattern
        .find_iter(source)
        .filter(|fence| !source[fence.end()..].starts_with(|c: char| c.is_ascii_alphabetic()))
        .collect();
    let mut depth = 0_i32;
    let mut nested = false;
    for fence in &fences {
        if fence.as_str().ends_with("\\lvert") {
            depth += 1;
            nested |= depth > 1;
        } else {
            depth -= 1;
        }
    }
    if !nested {
        return Ok(source.into());
    }
    let mut out = String::new();
    let mut end = 0;
    for fence in fences {
        let opening = fence.as_str().ends_with("\\lvert");
        let prefix = &fence.as_str()[..fence.as_str().len() - "\\lvert".len()];
        let prefix = prefix.trim();
        // Pandoc already keeps explicit left/right pairs as native lr groups.
        if matches!(prefix, "\\left" | "\\right") {
            continue;
        }
        let scale_percent = match prefix {
            "\\bigl" | "\\bigr" => 120,
            "\\Bigl" | "\\Bigr" => 180,
            "\\biggl" | "\\biggr" => 240,
            "\\Biggl" | "\\Biggr" => 300,
            _ => 100,
        };
        let alias = format!("MHFEFENCE{}N{}", id.replace('-', ""), aliases.len());
        if source.contains(&alias) {
            return Err(Failure::new(
                "PDF-MATH-LAYOUT",
                "Reserved fence alias occurs in source",
            ));
        }
        aliases.insert(
            alias.clone(),
            ModulusFence {
                opening,
                scale_percent,
            },
        );
        out.push_str(&source[end..fence.start()]);
        out.push_str(&format!("\\operatorname{{{alias}}}"));
        end = fence.end();
    }
    out.push_str(&source[end..]);
    Ok(out)
}

/// Keep concatenation as a binary symbol without changing explicit norm fences.
pub(crate) fn concatenations(
    source: &str,
    id: &str,
    operators: &mut BTreeMap<String, String>,
) -> String {
    let mut out = String::new();
    let mut end = 0;
    let mut norm = false;
    for (offset, _) in source.match_indices("\\Vert") {
        let prefix = source[..offset].trim_end();
        let suffix = &source[offset + 5..];
        if suffix.starts_with(char::is_alphabetic)
            || prefix.ends_with("\\left")
            || prefix.ends_with("\\right")
            || [
                "\\bigl", "\\bigr", "\\Bigl", "\\Bigr", "\\biggl", "\\biggr", "\\Biggl", "\\Biggr",
            ]
            .iter()
            .any(|size| prefix.ends_with(size))
        {
            continue;
        }
        let atom = prefix
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || ")]}'".contains(c));
        if norm {
            norm = false;
        } else if !atom {
            norm = true;
        } else if suffix
            .trim_start()
            .chars()
            .next()
            .is_some_and(|c| c.is_alphanumeric() || "\\({".contains(c))
        {
            let alias = format!("MHFEJOIN{}N{}", id.replace('-', ""), operators.len());
            operators.insert(alias.clone(), "‖".into());
            out.push_str(&source[end..offset]);
            out.push_str(&format!("\\operatorname{{{alias}}}"));
            end = offset + 5;
        }
    }
    out.push_str(&source[end..]);
    out
}

/// Pandoc's math writer discards array rules and TeX's aligned-pair gutter.
/// Adapt only these supported outer environments; the canonical source stays intact.
pub(crate) fn structure(source: &str, fragment: &str, display: bool) -> Result<String> {
    let array = source.trim().starts_with("\\begin{array}");
    let aligned = source.trim().starts_with("\\begin{aligned}");
    if !array && !aligned {
        return Ok(fragment.into());
    }
    let start = fragment
        .find('$')
        .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Missing math delimiter"))?;
    let end = fragment
        .rfind('$')
        .filter(|end| *end > start)
        .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Missing math delimiter"))?;
    let rows = rows(&fragment[start + 1..end])?;
    if aligned {
        let body = rows
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .map(|(column, cell)| {
                        if column > 0 && column % 2 == 0 {
                            format!("#h(1.5em) {cell}")
                        } else {
                            cell.clone()
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" & ")
            })
            .collect::<Vec<_>>()
            .join(" \\\n");
        let spacing = if display { " " } else { "" };
        return Ok(format!(
            "{}${spacing}{body}{spacing}${}",
            &fragment[..start],
            &fragment[end + 1..]
        ));
    }
    let rest = source
        .trim()
        .strip_prefix("\\begin{array}{")
        .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Unsupported array specification"))?;
    let (spec, body) = rest
        .split_once('}')
        .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Unclosed array specification"))?;
    let mut columns = Vec::new();
    let mut rules = Vec::new();
    for c in spec.chars().filter(|c| !c.is_whitespace()) {
        match c {
            'c' | 'l' | 'r' => columns.push(c.to_string()),
            '|' if !rules.contains(&columns.len()) => rules.push(columns.len()),
            _ => {
                return Err(Failure::new(
                    "PDF-MATH-LAYOUT",
                    "Unsupported array column or repeated rule",
                ));
            }
        }
    }
    if columns.is_empty()
        || rows.iter().any(|row| row.len() != columns.len())
        || rules
            .iter()
            .any(|column| *column == 0 || *column == columns.len())
        || body.contains("\\begin{")
        || body.contains("\\cline")
        || body.contains("\\multicolumn")
    {
        return Err(Failure::new(
            "PDF-MATH-LAYOUT",
            "Unsupported array structure",
        ));
    }
    // A rule at the start of a row separates it from the preceding one.
    let body = body
        .trim()
        .strip_suffix("\\end{array}")
        .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Unclosed array"))?;
    let mut hlines = Vec::new();
    for (row, source_row) in body.split("\\\\").enumerate() {
        let source_row = source_row.trim();
        if source_row.starts_with("\\hline") {
            if row == 0 || row >= rows.len() || source_row.matches("\\hline").count() != 1 {
                return Err(Failure::new(
                    "PDF-MATH-LAYOUT",
                    "Unsupported horizontal array rule",
                ));
            }
            hlines.push(row);
        } else if source_row.contains("\\hline") {
            return Err(Failure::new(
                "PDF-MATH-LAYOUT",
                "Misplaced horizontal array rule",
            ));
        }
    }
    let data = rows
        .iter()
        .map(|row| {
            format!(
                "({},)",
                row.iter()
                    .map(|cell| format!("(${cell}$).body"))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "{}#mhfe-array(({},), ({},), ({},), ({data},)){}",
        &fragment[..start],
        columns
            .iter()
            .map(|column| format!("\"{column}\""))
            .collect::<Vec<_>>()
            .join(","),
        rules
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(","),
        hlines
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(","),
        &fragment[end + 1..]
    ))
}

/// Split writer output at outer alignment points and row terminators only.
fn rows(source: &str) -> Result<Vec<Vec<String>>> {
    let mut rows = Vec::new();
    let mut cells = Vec::new();
    let mut start = 0;
    let mut depth = 0usize;
    let mut quoted = false;
    let mut escaped = false;
    for (offset, c) in source.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if c == '\\' {
            if !quoted && depth == 0 && source[offset + 1..].starts_with('\n') {
                cells.push(source[start..offset].trim().into());
                rows.push(std::mem::take(&mut cells));
                start = offset + 1;
            } else {
                escaped = true;
            }
            continue;
        }
        if c == '"' {
            quoted = !quoted;
        }
        if quoted {
            continue;
        }
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Unbalanced writer output"))?
            }
            '&' if depth == 0 => {
                cells.push(source[start..offset].trim().into());
                start = offset + 1;
            }
            _ => (),
        }
    }
    cells.push(source[start..].trim().into());
    rows.push(cells);
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_moduli_keep_their_opening_and_closing_roles() {
        for suffix in ["", "_p", "^2", "2"] {
            let source = format!(r"\lvert x+\lvert y+z\rvert{suffix}+w\rvert{suffix}");
            let rendered = crate::source::math_presentation(&source, "nested").unwrap();
            assert_eq!(rendered.fences.len(), 4);
            assert_eq!(
                rendered
                    .fences
                    .values()
                    .map(ModulusFence::typst)
                    .collect::<Vec<_>>(),
                [
                    r#"class("opening", \|)"#,
                    r#"class("opening", \|)"#,
                    r#"class("closing", \|)"#,
                    r#"class("closing", \|)"#,
                ]
            );
            if !suffix.is_empty() {
                assert_eq!(rendered.latex.matches(&format!("}}{suffix}")).count(), 2);
            }
        }
        for source in [r"\lvert x+y\rvert", r"\bigl\lvert x+y\bigr\rvert"] {
            assert_eq!(
                crate::source::math_presentation(source, "single")
                    .unwrap()
                    .latex,
                source
            );
        }
    }

    #[test]
    fn fences_and_nested_alignment_are_preserved() {
        let mut aliases = BTreeMap::new();
        let result = concatenations(
            r"A\Vert B\Vert C + \Vert x\Vert + \left\Vert y\right\Vert",
            "test",
            &mut aliases,
        );
        assert_eq!(aliases.len(), 2);
        assert!(result.ends_with(r"+ \Vert x\Vert + \left\Vert y\right\Vert"));
        assert_eq!(
            rows("a & f(\"&\", x) & b & c \\\nd & e & f & g")
                .unwrap()
                .len(),
            2
        );
        let mut aliases = BTreeMap::new();
        let result = concatenations(
            r"A'\Vert B\Vert C + \bigl\Vert z\bigr\Vert + \lVert u\rVert",
            "prime",
            &mut aliases,
        );
        assert_eq!(aliases.len(), 2);
        assert!(result.ends_with(r"+ \bigl\Vert z\bigr\Vert + \lVert u\rVert"));
    }

    #[test]
    fn unsupported_arrays_fail_closed() {
        for source in [
            r"\begin{array}{p{2cm}}a\end{array}",
            r"\begin{array}{c||l}a&b\end{array}",
            r"\begin{array}{c}\multicolumn{2}{c}{a}\end{array}",
        ] {
            assert!(structure(source, "#mhfe-math[ $a & b$ ", true).is_err());
        }
    }
}
