use crate::failure::{Failure, Result};
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

const MAX_SOURCE_LENGTH: usize = 12_000;
const MAX_DEPTH: usize = 64;
const GROUPS: [(&str, &str); 5] = [("(", ")"), ("[", "]"), ("{", "}"), ("⌊", "⌋"), ("⌈", "⌉")];

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Vocabulary {
    pub(crate) symbols: BTreeMap<String, String>,
    pub(crate) functions: Vec<String>,
    pub(crate) special_names: Vec<String>,
    pub(crate) literals: Vec<String>,
}

impl Vocabulary {
    pub(crate) fn load() -> Result<Self> {
        Ok(serde_json::from_str(include_str!("../notation-data.json"))?)
    }
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct Token {
    value: String,
    offset: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub(crate) enum Node {
    Token {
        value: String,
    },
    Group {
        open: String,
        children: Vec<Node>,
    },
    Sequence {
        children: Vec<Node>,
    },
    Script {
        base: Box<Node>,
        sub: Option<Box<Node>>,
        power: Option<Box<Node>>,
        primes: String,
    },
}

#[derive(Debug, Serialize)]
pub(crate) struct Conversion {
    pub(crate) original: String,
    pub(crate) latex: String,
    pub(crate) tokens: Vec<String>,
    pub(crate) tree: Node,
}

/// Transcribes grouped notation without changing precedence or inferring fractions.
pub(crate) struct AsciiMath<'a> {
    vocabulary: &'a Vocabulary,
    tokens: Vec<Token>,
    position: usize,
}

impl<'a> AsciiMath<'a> {
    pub(crate) fn convert(source: &str, vocabulary: &'a Vocabulary) -> Result<Conversion> {
        if source.trim().is_empty() || source.encode_utf16().count() > MAX_SOURCE_LENGTH {
            return Err(Failure::new(
                "PDF-NOTATION",
                "Empty or oversized ASCII math",
            ));
        }
        let tokens = Self::lex(source, vocabulary)?;
        let mut parser = Self {
            vocabulary,
            tokens,
            position: 0,
        };
        let tree = Node::Sequence {
            children: parser.sequence(None, 0)?,
        };
        let latex = parser.emit(&tree)?;
        let tokens = parser.tokens.into_iter().map(|token| token.value).collect();
        Ok(Conversion {
            original: source.into(),
            latex,
            tokens,
            tree,
        })
    }

    fn lex(source: &str, vocabulary: &Vocabulary) -> Result<Vec<Token>> {
        let identifier = Regex::new(r"^(?:0x[0-9a-fA-F]+|\d+(?:\.\d+)?|[a-zA-Z]+\d*|[\p{L}])")?;
        let game = Regex::new(r"^[ΓΔΘ]\d+")?;
        let mut symbols: Vec<_> = vocabulary
            .symbols
            .keys()
            .filter(|symbol| !symbol.chars().all(|c| c.is_alphanumeric() || c == '_'))
            .collect();
        symbols.sort_by_key(|symbol| std::cmp::Reverse(symbol.len()));
        let mut offset = 0;
        let mut tokens = Vec::new();
        while offset < source.len() {
            let rest = &source[offset..];
            let space = rest.len() - rest.trim_start().len();
            if space > 0 {
                offset += space;
                continue;
            }
            let named = vocabulary
                .special_names
                .iter()
                .find(|name| rest.starts_with(name.as_str()));
            let symbol = symbols
                .iter()
                .find(|symbol| rest.starts_with(symbol.as_str()));
            let value = named
                .map(String::as_str)
                .or_else(|| game.find(rest).map(|m| m.as_str()))
                .or_else(|| symbol.map(|s| s.as_str()))
                .or_else(|| identifier.find(rest).map(|m| m.as_str()))
                .or_else(|| Self::quoted(rest))
                .or_else(|| {
                    rest.chars()
                        .next()
                        .filter(|c| "()[]{}⌊⌋⌈⌉_^'+-*/=<>|,:;.".contains(*c))
                        .map(|c| &rest[..c.len_utf8()])
                });
            let value = value.ok_or_else(|| {
                Failure::new(
                    "PDF-NOTATION",
                    format!(
                        "Unsupported ASCII math at column {}",
                        source[..offset].chars().count() + 1
                    ),
                )
            })?;
            tokens.push(Token {
                value: value.into(),
                offset,
            });
            offset += value.len();
        }
        Ok(tokens)
    }

    fn quoted(source: &str) -> Option<&str> {
        if !source.starts_with('"') {
            return None;
        }
        let end = source[1..].find('"')? + 2;
        (!source[..end].contains('\n')).then_some(&source[..end])
    }

    fn sequence(&mut self, stop: Option<&str>, depth: usize) -> Result<Vec<Node>> {
        Self::depth(depth)?;
        let mut nodes = Vec::new();
        while let Some(next) = self.tokens.get(self.position) {
            if stop == Some(next.value.as_str()) {
                self.position += 1;
                return Ok(nodes);
            }
            if GROUPS.iter().any(|(_, close)| *close == next.value) {
                return Err(Failure::new("PDF-NOTATION", "Unexpected closing delimiter"));
            }
            if matches!(next.value.as_str(), "_" | "^") {
                return Err(Failure::new("PDF-NOTATION", "Script without a base"));
            }
            nodes.push(self.atom(depth, false)?);
        }
        if stop.is_some() {
            return Err(Failure::new("PDF-NOTATION", "Unclosed ASCII math group"));
        }
        Ok(nodes)
    }

    fn atom(&mut self, depth: usize, script: bool) -> Result<Node> {
        Self::depth(depth)?;
        let value = self
            .tokens
            .get(self.position)
            .ok_or_else(|| Failure::new("PDF-NOTATION", "Missing script argument"))?
            .value
            .clone();
        self.position += 1;
        if GROUPS.iter().any(|(_, close)| *close == value) {
            return Err(Failure::new("PDF-NOTATION", "Unexpected closing delimiter"));
        }
        let mut node = if let Some((_, close)) = GROUPS.iter().find(|(open, _)| *open == value) {
            Node::Group {
                open: value.clone(),
                children: self.sequence(Some(close), depth + 1)?,
            }
        } else {
            Node::Token {
                value: value.clone(),
            }
        };
        if script {
            if matches!(&node, Node::Group { children, .. } if children.is_empty()) {
                return Err(Failure::new("PDF-NOTATION", "Empty script argument"));
            }
            if matches!(value.as_str(), "+" | "−" | "-") {
                node = Node::Sequence {
                    children: vec![node, self.atom(depth + 1, true)?],
                };
            }
            if "_^=,;*/<>|:.".contains(value.as_str()) {
                return Err(Failure::new("PDF-NOTATION", "Invalid script argument"));
            }
            return Ok(node);
        }
        self.scripts(node, depth)
    }

    fn scripts(&mut self, base: Node, depth: usize) -> Result<Node> {
        let (mut sub, mut power, mut primes, mut numeric_group) =
            (None, None, String::new(), false);
        while let Some(next) = self.tokens.get(self.position).map(|t| t.value.as_str()) {
            if matches!(next, "_" | "^") {
                let is_sub = next == "_";
                if if is_sub {
                    sub.is_some()
                } else {
                    power.is_some()
                } {
                    return Err(Failure::new(
                        "PDF-NOTATION",
                        "Repeated script; group the expression explicitly",
                    ));
                }
                self.position += 1;
                let argument = self.atom(depth + 1, true)?;
                numeric_group |= !is_sub
                    && matches!(&argument, Node::Group { open, children } if open == "(" && children.len() == 1 && matches!(&children[0], Node::Token { value } if value.chars().all(|c| c.is_ascii_digit())));
                let argument = match argument {
                    Node::Group { open, children } if open == "(" || open == "{" => {
                        Node::Sequence { children }
                    }
                    other => other,
                };
                if is_sub {
                    sub = Some(Box::new(argument));
                } else {
                    power = Some(Box::new(argument));
                }
            } else if next == "'" || (next == "*" && self.suffix_star(&base)) {
                primes.push_str(next);
                self.position += 1;
            } else {
                break;
            }
        }
        if sub.is_some() && numeric_group {
            return Err(Failure::new(
                "PDF-NOTATION",
                "Ambiguous parenthesized superscript: use ^1 for a power or ^{(1)} for a label",
            ));
        }
        Ok(if sub.is_some() || power.is_some() || !primes.is_empty() {
            Node::Script {
                base: Box::new(base),
                sub,
                power,
                primes,
            }
        } else {
            base
        })
    }

    fn suffix_star(&self, base: &Node) -> bool {
        let Some(before) = self
            .position
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
        else {
            return false;
        };
        let Some(current) = self.tokens.get(self.position) else {
            return false;
        };
        matches!(base, Node::Token { value } if value.starts_with(char::is_alphabetic))
            && current.offset == before.offset + before.value.len()
            && self.tokens.get(self.position + 1).is_none_or(|after| {
                matches!(
                    after.value.as_str(),
                    ")" | "]"
                        | "}"
                        | ","
                        | ":"
                        | ";"
                        | "="
                        | "<"
                        | ">"
                        | "!"
                        | "+"
                        | "−"
                        | "-"
                        | "("
                        | "["
                        | "∈"
                        | "≠"
                        | "‖"
                        | "||"
                        | "∨"
                        | "∧"
                        | "←"
                        | "→"
                        | "↦"
                        | "<="
                        | ">="
                        | "≤"
                        | "≥"
                        | "!="
                        | "=="
                        | "/"
                        | "·"
                        | "×"
                )
            })
    }

    fn depth(depth: usize) -> Result<()> {
        if depth > MAX_DEPTH {
            Err(Failure::new(
                "PDF-NOTATION",
                "ASCII math nesting is too deep",
            ))
        } else {
            Ok(())
        }
    }

    fn emit(&self, node: &Node) -> Result<String> {
        match node {
            Node::Token { value } => self.token_latex(value),
            Node::Sequence { children } => self.children(children),
            Node::Group { open, children } => {
                let close = GROUPS
                    .iter()
                    .find(|(candidate, _)| candidate == open)
                    .map(|(_, close)| *close)
                    .ok_or_else(|| Failure::new("PDF-NOTATION", "Unknown group"))?;
                Ok(format!(
                    "{} {} {}",
                    delimiter(open),
                    self.children(children)?,
                    delimiter(close)
                ))
            }
            Node::Script {
                base,
                sub,
                power,
                primes,
            } => {
                let sub = sub
                    .as_ref()
                    .map(|n| self.emit(n).map(|s| format!("_{{{s}}}")))
                    .transpose()?
                    .unwrap_or_default();
                let mut supers = power
                    .as_ref()
                    .map(|n| self.emit(n))
                    .transpose()?
                    .into_iter()
                    .collect::<Vec<_>>();
                supers.extend(primes.chars().map(|c| {
                    if c == '\'' {
                        "\\prime".into()
                    } else {
                        "*".into()
                    }
                }));
                let power = if supers.is_empty() {
                    String::new()
                } else {
                    format!("^{{{}}}", supers.join(" "))
                };
                Ok(format!("{{{}}}{sub}{power}", self.emit(base)?))
            }
        }
    }

    fn children(&self, children: &[Node]) -> Result<String> {
        Ok(children
            .iter()
            .map(|n| self.emit(n))
            .collect::<Result<Vec<_>>>()?
            .join(" "))
    }

    fn token_latex(&self, value: &str) -> Result<String> {
        if let Some(symbol) = self.vocabulary.symbols.get(value) {
            return Ok(symbol.clone());
        }
        if value.starts_with('"') {
            if value.contains(['\\', '{', '}']) {
                return Err(Failure::new(
                    "PDF-NOTATION",
                    "Quoted text cannot contain LaTeX commands or braces",
                ));
            }
            let escaped: String = value
                .chars()
                .map(|c| match c {
                    '~' => "\\textasciitilde{}".into(),
                    '^' => "\\textasciicircum{}".into(),
                    '%' | '&' | '#' | '_' | '$' => format!("\\{c}"),
                    _ => c.to_string(),
                })
                .collect();
            return Ok(format!("\\texttt{{{escaped}}}"));
        }
        let result = match value {
            "in" => "\\in".into(),
            "mod" => "\\bmod".into(),
            "|" => "\\vert".into(),
            "/" => "\\mathbin{/}".into(),
            "log2" => "\\log_{2}".into(),
            _ if self.vocabulary.functions.iter().any(|s| s == value) => {
                format!("\\operatorname{{{value}}}")
            }
            _ if value.starts_with(['Γ', 'Δ', 'Θ'])
                && value.chars().skip(1).all(|c| c.is_ascii_digit()) =>
            {
                let mut chars = value.chars();
                let first = chars
                    .next()
                    .ok_or_else(|| Failure::new("PDF-NOTATION", "Missing game name"))?;
                format!(
                    "{}_{{{}}}",
                    self.vocabulary.symbols[&first.to_string()],
                    chars.as_str()
                )
            }
            _ if value.starts_with(['N', 'C'])
                && value.len() > 1
                && value[1..].chars().all(|c| c.is_ascii_digit()) =>
            {
                format!("{}_{{{}}}", &value[..1], &value[1..])
            }
            _ if self.vocabulary.special_names.iter().any(|s| s == value)
                && value.contains('-') =>
            {
                format!("\\text{{{value}}}")
            }
            _ if value.starts_with(|c: char| c.is_ascii_alphabetic())
                && value.len() > 1
                && value
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-') =>
            {
                format!("\\mathrm{{{}}}", value.replace('_', "\\_"))
            }
            _ if value.starts_with("0x") => format!("\\mathtt{{{value}}}"),
            _ => value.into(),
        };
        Ok(result)
    }
}

fn delimiter(value: &str) -> &str {
    match value {
        "{" => "\\{",
        "}" => "\\}",
        "⌊" => "\\lfloor",
        "⌋" => "\\rfloor",
        "⌈" => "\\lceil",
        "⌉" => "\\rceil",
        _ => value,
    }
}
