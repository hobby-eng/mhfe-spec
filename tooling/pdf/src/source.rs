use crate::failure::{Failure, Result};
use regex::Regex;
use std::collections::{BTreeMap, HashMap};

/// Protects mathematics only outside CommonMark code, HTML and link destinations.
pub(crate) struct ProtectedSource {
    pub(crate) markdown: String,
    pub(crate) expressions: HashMap<String, ProtectedMath>,
}

#[derive(Clone)]
pub(crate) struct ProtectedMath {
    pub(crate) source: String,
    pub(crate) display: bool,
    pub(crate) protected: bool,
}

impl ProtectedSource {
    pub(crate) fn parse(source: &str) -> Result<Self> {
        if source.len() > 4 * 1024 * 1024 {
            return Err(Failure::new("PDF-SOURCE", "Document exceeds 4 MiB"));
        }
        let (mut ignored, protected) = code_ranges(source)?;
        ignored.sort_by_key(|range| range.start);
        let mut replacements = Vec::new();
        let mut offset = 0;
        let mut skip = 0;
        while offset < source.len() {
            while ignored.get(skip).is_some_and(|range| range.end <= offset) {
                skip += 1;
            }
            if ignored
                .get(skip)
                .is_some_and(|range| range.start <= offset && range.end > offset)
            {
                offset = ignored[skip].end;
                continue;
            }
            let rest = &source[offset..];
            if rest.starts_with('\\') {
                offset += 1;
                if let Some(next) = source[offset..].chars().next() {
                    offset += next.len_utf8();
                }
                continue;
            }
            if let Some((end, contents)) = protected.get(&offset) {
                replacements.push((
                    offset,
                    *end,
                    ProtectedMath {
                        source: contents.clone(),
                        display: false,
                        protected: true,
                    },
                ));
                offset = *end;
                continue;
            }
            if rest.starts_with("$`") {
                return Err(Failure::new(
                    "PDF-SOURCE",
                    "Unclosed protected inline math delimiter",
                ));
            }
            if rest.starts_with('$') {
                let width = if rest.starts_with("$$") { 2 } else { 1 };
                if width == 2
                    && source[..offset]
                        .rsplit('\n')
                        .next()
                        .is_some_and(|line| !line.trim().is_empty())
                {
                    return Err(Failure::new(
                        "PDF-SOURCE",
                        "Display math must be in its own block",
                    ));
                }
                let mut end = offset + width;
                loop {
                    if end >= source.len() {
                        return Err(Failure::new("PDF-SOURCE", "Unclosed dollar math delimiter"));
                    }
                    let remaining = &source[end..];
                    if remaining.starts_with('\\') {
                        end += 1;
                        if let Some(next) = source[end..].chars().next() {
                            end += next.len_utf8();
                        }
                    } else if remaining.starts_with(if width == 2 { "$$" } else { "$" }) {
                        break;
                    } else {
                        end += remaining.chars().next().map(char::len_utf8).unwrap_or(1);
                    }
                }
                replacements.push((
                    offset,
                    end + width,
                    ProtectedMath {
                        source: source[offset + width..end].into(),
                        display: width == 2,
                        protected: false,
                    },
                ));
                offset = end + width;
            } else {
                offset += rest.chars().next().map(char::len_utf8).unwrap_or(1);
            }
        }
        let mut result = Self {
            markdown: String::new(),
            expressions: HashMap::new(),
        };
        let mut previous = 0;
        for (start, end, math) in replacements {
            let marker = format!("MHFEPROTECTED{:06}TOKEN", result.expressions.len() + 1);
            if source.contains(&marker) {
                return Err(Failure::new(
                    "PDF-SOURCE",
                    "Reserved math marker occurs in source",
                ));
            }
            result.markdown.push_str(&source[previous..start]);
            result.markdown.push_str(&format!("`{marker}`"));
            result.expressions.insert(marker, math);
            previous = end;
        }
        result.markdown.push_str(&source[previous..]);
        Ok(result)
    }
}

type ProtectedRanges = HashMap<usize, (usize, String)>;

fn code_ranges(source: &str) -> Result<(Vec<std::ops::Range<usize>>, ProtectedRanges)> {
    use pulldown_cmark::{CodeBlockKind, Event, LinkType, Parser, Tag, TagEnd};
    let mut ignored = Vec::new();
    let mut protected = HashMap::new();
    let mut block: Option<(std::ops::Range<usize>, bool, usize)> = None;
    let mut links: Vec<(std::ops::Range<usize>, usize)> = Vec::new();
    let parser = Parser::new(source);
    ignored.extend(
        parser
            .reference_definitions()
            .iter()
            .map(|(_, def)| def.span.clone()),
    );
    for (event, range) in parser.into_offset_iter() {
        if matches!(
            event,
            Event::Text(_)
                | Event::Code(_)
                | Event::InlineHtml(_)
                | Event::Start(Tag::Image { .. })
        ) && let Some((_, end)) = links.last_mut()
        {
            *end = range.end;
        }
        if let Event::Text(_) = &event
            && let Some((_, _, end)) = &mut block
        {
            *end = range.end;
        }
        match event {
            Event::Start(Tag::CodeBlock(kind)) => {
                let math = matches!(kind, CodeBlockKind::Fenced(_));
                let opening_end = source[range.start..range.end]
                    .find('\n')
                    .map(|i| range.start + i + 1)
                    .unwrap_or(range.end);
                block = Some((range, math, opening_end));
            }
            Event::End(TagEnd::CodeBlock) => {
                if let Some((start, math, text_end)) = block.take() {
                    let end = range.end.max(start.end);
                    if math {
                        let raw = &source[start.start..end];
                        let strip = |line: &str| {
                            let mut line = line.trim();
                            while let Some(rest) = line.strip_prefix('>') {
                                line = rest.trim();
                            }
                            line.to_owned()
                        };
                        let first = raw.lines().next().map(strip).unwrap_or_default();
                        let last = raw.lines().last().map(strip).unwrap_or_default();
                        let delimiter = first.chars().next().unwrap_or('`');
                        let count = first.chars().take_while(|c| *c == delimiter).count();
                        if text_end >= end
                            || raw.lines().count() < 2
                            || last.chars().count() < count
                            || !last.chars().all(|c| c == delimiter)
                        {
                            return Err(Failure::new("PDF-SOURCE", "Unclosed mathematical fence"));
                        }
                    }
                    ignored.push(start.start..end);
                }
            }
            Event::Code(_) => {
                if range.start > 0
                    && source[..range.start].ends_with('$')
                    && source[range.end..].starts_with('$')
                    && source[range.start..range.end].starts_with('`')
                    && !source[range.start..range.end].starts_with("``")
                {
                    protected.insert(
                        range.start - 1,
                        (range.end + 1, source[range.start + 1..range.end - 1].into()),
                    );
                }
                ignored.push(range);
            }
            Event::Html(_) | Event::InlineHtml(_) => ignored.push(range),
            Event::Start(Tag::Image { .. }) => ignored.push(range),
            Event::Start(Tag::Link { link_type, .. }) => {
                if matches!(link_type, LinkType::Autolink | LinkType::Email) {
                    ignored.push(range.clone());
                }
                links.push((range.clone(), range.start));
            }
            Event::End(TagEnd::Link) => {
                if let Some((whole, label_end)) = links.pop()
                    && let Some(offset) = source[label_end..whole.end].find("](")
                {
                    ignored.push(label_end + offset + 2..whole.end);
                }
            }
            _ => (),
        }
    }
    Ok((ignored, protected))
}

pub(crate) struct MathPresentation {
    pub(crate) latex: String,
    pub(crate) operators: BTreeMap<String, String>,
    pub(crate) tag: Option<String>,
    pub(crate) fences: BTreeMap<String, crate::math_layout::ModulusFence>,
}

/// Gives operator names opaque identities before a writer can parse their literal hyphens.
pub(crate) fn math_presentation(source: &str, id: &str) -> Result<MathPresentation> {
    let custom = Regex::new(
        r"\\operatorname\{([^{}]+)\}|\\mathop\{\\(?:mathrm|text)\{([^{}]+)\}\}\\nolimits",
    )?;
    let mut operators = BTreeMap::new();
    let mut latex = String::new();
    let mut end = 0;
    for capture in custom.captures_iter(source) {
        let found = capture
            .get(0)
            .ok_or_else(|| Failure::new("PDF-OPERATOR", "Missing operator macro"))?;
        let name = capture
            .get(1)
            .or_else(|| capture.get(2))
            .ok_or_else(|| Failure::new("PDF-OPERATOR", "Missing operator name"))?
            .as_str();
        if name.contains('\\') {
            return Err(Failure::new(
                "PDF-OPERATOR",
                "Operator names must be literal text",
            ));
        }
        let alias = format!("MHFEOP{}N{}", id.replace('-', ""), operators.len() + 1);
        if source.contains(&alias) {
            return Err(Failure::new(
                "PDF-OPERATOR",
                "Reserved operator alias occurs in source",
            ));
        }
        operators.insert(alias.clone(), name.into());
        latex.push_str(&source[end..found.start()]);
        latex.push_str(&format!("\\operatorname{{{alias}}}"));
        end = found.end();
    }
    latex.push_str(&source[end..]);
    latex = crate::math_layout::concatenations(&latex, id, &mut operators);
    let mut fences = BTreeMap::new();
    latex = crate::math_layout::modulus_fences(&latex, id, &mut fences)?;
    // Pandoc 3.13 otherwise writes {\Theta_0}^\prime as Theta_0', whose prime
    // Typst binds to 0. Removing this redundant group preserves the TeX atom
    // but makes the writer emit Theta'_0 with the intended attachment.
    let grouped_prime = Regex::new(
        r"\{(\\(?:Theta|Gamma|Delta)_(?:\{[^{}]+\}|[A-Za-z0-9]))\}\^\{((?:\\prime\s*)+)\}",
    )?;
    latex = grouped_prime
        .replace_all(&latex, "${1}^{${2}}")
        .into_owned();
    if unsupported_grouped_prime(&latex)? {
        return Err(Failure::new(
            "PDF-PRIME",
            "Unsupported grouped prime; rewrite with an explicit ungrouped base",
        ));
    }
    let remaining_ops = Regex::new(r"\\mathop\{\\downarrow\}\\limits")?.replace_all(&latex, "");
    if remaining_ops.contains("\\mathop") {
        return Err(Failure::new(
            "PDF-OPERATOR",
            "Unsupported named operator macro; use a literal name with nolimits",
        ));
    }
    let tags: Vec<_> = Regex::new(r"\\tag(\*)?\s*\{([^{}\\]+)\}")?
        .captures_iter(source)
        .map(|c| (c.get(1).is_some(), c[2].to_owned()))
        .collect();
    if source.contains("\\tag")
        && (tags.len() != 1 || Regex::new(r"\\tag\b")?.find_iter(source).count() != 1)
    {
        return Err(Failure::new(
            "PDF-TAG",
            "Unsupported or repeated equation tag",
        ));
    }
    if tags.iter().any(|(_, name)| {
        !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || " .,:;-()[]".contains(c))
    }) {
        return Err(Failure::new(
            "PDF-TAG",
            "Equation tags must be plain ASCII labels",
        ));
    }
    let tag = tags.first().map(|(star, name)| {
        if *star {
            name.clone()
        } else {
            format!("({name})")
        }
    });
    Ok(MathPresentation {
        latex,
        operators,
        tag,
        fences,
    })
}

fn unsupported_grouped_prime(source: &str) -> Result<bool> {
    for power in Regex::new(r"\^\s*(?:\{\s*)*\\prime")?.find_iter(source) {
        let prefix = source[..power.start()].trim_end();
        if !prefix.ends_with('}') {
            continue;
        }
        let mut depth = 0usize;
        for (offset, c) in prefix.char_indices().rev() {
            if prefix[..offset]
                .bytes()
                .rev()
                .take_while(|b| *b == b'\\')
                .count()
                % 2
                == 1
            {
                continue;
            }
            if c == '}' {
                depth += 1;
            }
            if c == '{' {
                depth -= 1;
                if depth == 0 {
                    // An index group may precede the prime. A group around the
                    // entire base needs an explicit supported normalization.
                    let base = &prefix[offset + 1..prefix.len() - 1];
                    let complicated = base.contains('_')
                        || ["\\sum", "\\prod", "\\lim", "\\int"]
                            .iter()
                            .any(|op| base.contains(op));
                    if complicated && !prefix[..offset].trim_end().ends_with('_') {
                        return Ok(true);
                    }
                    break;
                }
            }
        }
    }
    Ok(false)
}

pub(crate) fn explicit_math(source: &str, protected: bool) -> Result<()> {
    if source.trim().is_empty() || source.len() > 64 * 1024 {
        return Err(Failure::new(
            "PDF-MATH",
            "Empty or oversized LaTeX expression",
        ));
    }
    if Regex::new(r"\\operatorname\b")?.is_match(source) {
        return Err(Failure::new(
            "PDF-GITHUB",
            "GitHub rejects operatorname; use mathop with mathrm and nolimits",
        ));
    }
    if source.contains('<') {
        return Err(Failure::new(
            "PDF-GITHUB",
            "Use \\lt instead of a literal less-than sign",
        ));
    }
    if !protected && (source.contains(['\r', '\n']) || Regex::new(r"\\[^A-Za-z]")?.is_match(source))
    {
        return Err(Failure::new(
            "PDF-GITHUB",
            "Markdown-sensitive math needs a protected delimiter or a math fence",
        ));
    }
    if Regex::new(r"\\(?:href|url|includegraphics|html\w*|def|gdef|edef|xdef|let|global|newcommand|renewcommand|input|include|write|openout|read|catcode|csname|usepackage|documentclass)\b")?.is_match(source) {
        return Err(Failure::new("PDF-MATH", "Stateful or resource commands are not allowed in mathematical expressions"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_protected_latex_and_does_not_read_literal_fences() {
        let source =
            ProtectedSource::parse("$`\\{x_1\\}`$\n\n```text\n$`literal`$\n```\n").unwrap();
        assert_eq!(source.expressions.len(), 1);
        assert_eq!(
            source.expressions.values().next().unwrap().source,
            "\\{x_1\\}"
        );
        assert!(source.markdown.contains("$`literal`$"));
        assert!(ProtectedSource::parse("$`x_1$").is_err());
        assert!(ProtectedSource::parse("```math\nx\n").is_err());
    }

    #[test]
    fn refuses_markdown_damage_and_resource_commands() {
        for source in [
            r"\operatorname{top}(x)",
            r"\Pr[A_{<t}]",
            r"\input{file}",
            r"\def\a{b}",
        ] {
            assert!(explicit_math(source, true).is_err(), "{source}");
        }
        let source = r"\mathop{\mathrm{top}}\nolimits\!\left(\{x_1,x_2\}\right)";
        assert!(explicit_math(source, true).is_ok());
        assert!(explicit_math(source, false).is_err());
        assert!(explicit_math(r"\Pr[A_{\lt t}]", true).is_ok());
    }

    #[test]
    fn keeps_code_delimiters_literal_and_refuses_unclosed_dollar_math() {
        for source in ["`` literal:$`x_1`$ ``", "> ```text\n> $`x_1`$\n> ```\n"] {
            let parsed = ProtectedSource::parse(source).unwrap();
            assert_eq!(parsed.markdown, source);
            assert!(parsed.expressions.is_empty());
        }
        for source in ["$x", "$$x"] {
            assert!(ProtectedSource::parse(source).is_err());
        }
        assert!(
            ProtectedSource::parse(r"A literal \$ sign.")
                .unwrap()
                .expressions
                .is_empty()
        );
    }

    #[test]
    fn preserves_hyphenated_operator_names_and_both_tag_forms() {
        let prepared =
            math_presentation(r"\mathop{\text{SHA-256}}\nolimits(E)\tag*{A}", "math-1").unwrap();
        assert_eq!(prepared.operators.values().next().unwrap(), "SHA-256");
        assert!(
            prepared
                .latex
                .starts_with(r"\operatorname{MHFEOPmath1N1}(E)")
        );
        assert_eq!(prepared.tag.as_deref(), Some("A"));
        assert_eq!(
            math_presentation(r"x\tag{1}", "math-2")
                .unwrap()
                .tag
                .as_deref(),
            Some("(1)")
        );
        assert!(math_presentation(r"x\tag{1}\tag{2}", "math-3").is_err());
        assert_eq!(
            math_presentation(r"{\Theta_{0}}^{\prime}", "math-4")
                .unwrap()
                .latex,
            r"\Theta_{0}^{\prime}"
        );
        assert_eq!(
            math_presentation(r"\Theta_{0^{\prime}}", "math-5")
                .unwrap()
                .latex,
            r"\Theta_{0^{\prime}}"
        );
    }
    #[test]
    fn refuses_unsupported_primes_operators_tags_and_unclosed_fences() {
        for input in [
            r"{\Theta_{{0}}}^{\prime}",
            r"{\sum_{i}}^{\prime}",
            r"{\lim_{i}}^{\prime}",
            r"A\mathop{x}\nolimits B",
            r"x\tag{1}\tag {2}",
            r"x\tag{A\%}",
            r"x\tag{A~B}",
            r"{\Theta_{0}}^{{\prime}}",
            r"{\Theta_{\}}}^{\prime}",
        ] {
            assert!(math_presentation(input, "math-1").is_err(), "{input}");
        }
        assert_eq!(
            math_presentation(r"{\Theta_0}^{\prime}", "math-1")
                .unwrap()
                .latex,
            r"\Theta_0^{\prime}"
        );
        for input in ["```text\nx=1\n", "```\nx=1\n", "```math\nx=1\n> ```"] {
            assert!(ProtectedSource::parse(input).is_err());
        }
        for input in [
            "[x](https://example.org/?a=1&amp;b=$)",
            "[x](https://example.org/$](a))",
            "[x][ref]\n\n[ref]:\n  https://example.org/$\n",
            "[x][ref]\n\n[ref]: https://example.org/$\n",
        ] {
            assert!(
                ProtectedSource::parse(input)
                    .unwrap()
                    .expressions
                    .is_empty()
            );
        }
    }
}
