use crate::failure::{Failure, Result};
use crate::notation::{Inline, Notation};
use crate::process::{Toolchain, digest};
use crate::source::{ProtectedMath, ProtectedSource, explicit_math};
use regex::Regex;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Component, Path, PathBuf};

#[derive(Serialize)]
pub(crate) struct Expression {
    pub(crate) id: String,
    pub(crate) source: String,
    pub(crate) display: bool,
    pub(crate) conversion: Option<Value>,
    pub(crate) sha256: String,
    pub(crate) repeatable: bool,
    pub(crate) operators: BTreeMap<String, String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub(crate) fences: BTreeMap<String, crate::math_layout::ModulusFence>,
}

#[derive(Serialize)]
pub(crate) struct SourceBlock {
    pub(crate) id: String,
    pub(crate) kind: String,
    pub(crate) prose: String,
    pub(crate) repeatable: bool,
}

/// Owns one Markdown source, its typed AST and the conversion evidence.
pub(crate) struct Document {
    root: PathBuf,
    source_path: PathBuf,
    source_text: String,
    commit: String,
    notation: Notation,
    protected: HashMap<String, ProtectedMath>,
    headers: BTreeSet<String>,
    slugs: HashMap<String, usize>,
    links: Vec<String>,
    repeating: bool,
    in_table: bool,
    indented: bool,
    pub(crate) expressions: Vec<Expression>,
    pub(crate) blocks: Vec<SourceBlock>,
    pub(crate) source_sha256: String,
    pub(crate) ast: Value,
}

const READER: &str = "markdown-raw_tex-raw_attribute-smart+tex_math_dollars";

impl Document {
    pub(crate) fn parse(
        root: &Path,
        path: &Path,
        commit: &str,
        source: &str,
        tools: &Toolchain,
    ) -> Result<Self> {
        let protected = ProtectedSource::parse(source)?;
        let ast = serde_json::from_slice(&tools.pandoc(
            &["--from", READER, "--to", "json", "--fail-if-warnings"],
            protected.markdown.as_bytes(),
        )?)?;
        let mut document = Self {
            root: root.into(),
            source_path: path.into(),
            source_text: source.into(),
            commit: commit.into(),
            notation: Notation::new()?,
            protected: protected.expressions,
            headers: BTreeSet::new(),
            slugs: HashMap::new(),
            links: Vec::new(),
            repeating: false,
            in_table: false,
            indented: false,
            expressions: Vec::new(),
            blocks: Vec::new(),
            source_sha256: digest(source.as_bytes()),
            ast: Value::Null,
        };
        let mut ast = ast;
        document.headings(&mut ast)?;
        document.walk(&mut ast)?;
        for link in &document.links {
            if !document.headers.contains(link) {
                return Err(Failure::new(
                    "PDF-LINK",
                    format!("Unresolved internal anchor: {link}"),
                ));
            }
        }
        document.ast = ast;
        Ok(document)
    }

    fn headings(&mut self, value: &mut Value) -> Result<()> {
        if value["t"] == "Header" {
            let title = plain(&value["c"][2]);
            let slug = Regex::new(r"[^\p{L}\p{N}_\- ]")?
                .replace_all(&title.to_lowercase().replace(['`', '*', '_'], ""), "")
                .replace(' ', "-");
            let count = self.slugs.entry(slug.clone()).or_default();
            let id = if *count == 0 {
                slug.clone()
            } else {
                format!("{slug}-{count}")
            };
            *count += 1;
            self.headers.insert(id.clone());
            value["c"][1][0] = id.into();
        }
        match value {
            Value::Array(values) => {
                for item in values {
                    self.headings(item)?;
                }
            }
            Value::Object(values) => {
                for item in values.values_mut() {
                    self.headings(item)?;
                }
            }
            _ => (),
        }
        Ok(())
    }

    fn walk(&mut self, value: &mut Value) -> Result<()> {
        match value {
            Value::Array(values) => self.array(values),
            Value::Object(values) => {
                for child in values.values_mut() {
                    self.walk(child)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn array(&mut self, values: &mut Vec<Value>) -> Result<()> {
        let mut input = std::mem::take(values);
        let mut index = 0;
        while index < input.len() {
            let value = input[index].clone();
            if value["t"] == "Header"
                && plain(&value["c"][2]) == "Contents"
                && input
                    .get(index + 1)
                    .is_some_and(|v| matches!(v["t"].as_str(), Some("BulletList" | "OrderedList")))
            {
                values.push(raw("RawBlock", "#mhfe-contents["));
                values.extend(self.item(value)?);
                values.extend(self.item(input[index + 1].clone())?);
                values.push(raw("RawBlock", "]"));
                index += 2;
                continue;
            }
            if value["t"] == "RawInline"
                && matches!(value["c"][1].as_str(), Some("<sup>" | "<sub>"))
            {
                let superscript = value["c"][1] == "<sup>";
                let close = if superscript { "</sup>" } else { "</sub>" };
                let end = (index + 1..input.len())
                    .find(|i| input[*i]["t"] == "RawInline" && input[*i]["c"][1] == close)
                    .ok_or_else(|| Failure::new("PDF-HTML", "Unclosed HTML script element"))?;
                let mut children = Value::Array(input[index + 1..end].to_vec());
                self.walk(&mut children)?;
                values.push(
                    json!({"t":if superscript {"Superscript"} else {"Subscript"},"c":children}),
                );
                index = end + 1;
                continue;
            }
            let mut rendered = self.item(value)?;
            // Keep sentence punctuation attached when a wide inline formula is
            // promoted to display. It remains ordinary text for short formulas.
            if rendered.first().is_some_and(|v| {
                v["t"] == "RawInline"
                    && v["c"][1].as_str().is_some_and(|s| {
                        s.starts_with("#mhfe-math(") && s.contains("display: false")
                    })
            }) && let Some(next) = input.get_mut(index + 1)
                && next["t"] == "Str"
                && let Some(text) = next["c"].as_str()
            {
                let count = text.chars().take_while(|c| ",.;:".contains(*c)).count();
                if count > 0 {
                    let punctuation = &text[..count];
                    let wrapper = rendered[0]["c"][1].as_str().unwrap_or_default();
                    rendered[0]["c"][1] = wrapper
                        .replacen(")[", &format!(", tail: [{}])[", punctuation), 1)
                        .into();
                    next["c"] = text[count..].into();
                }
            }
            values.extend(rendered);
            index += 1;
        }
        Ok(())
    }

    fn item(&mut self, mut value: Value) -> Result<Vec<Value>> {
        let kind = value["t"].as_str().unwrap_or_default().to_owned();
        match kind.as_str() {
            "Code" => {
                let raw_source = value["c"][1]
                    .as_str()
                    .ok_or_else(|| Failure::new("PDF-AST", "Invalid code span"))?;
                // markdown-it consumes escaped table separators inside code spans;
                // Pandoc leaves those table-only escapes in its Code node.
                let source = if self.in_table {
                    raw_source.replace(r"\|", "|")
                } else {
                    raw_source.into()
                };
                if let Some(math) = self.protected.get(&source).cloned() {
                    explicit_math(&math.source, math.protected)?;
                    return self.math(math.source, math.display, None);
                }
                let converted = self.notation.inline(&source).map_err(|error| {
                    let offset = self
                        .source_text
                        .find(&format!("`{source}`"))
                        .or_else(|| self.source_text.find(&source))
                        .unwrap_or(0);
                    let line = self.source_text[..offset].lines().count();
                    Failure::new(
                        "PDF-NOTATION",
                        format!("{}:{line}: {error}", self.source_path.display()),
                    )
                })?;
                match converted {
                    Inline::Math(converted) => {
                        return self.math(
                            converted.latex.clone(),
                            false,
                            Some(serde_json::to_value(converted)?),
                        );
                    }
                    Inline::Literal(Some(literal)) => value["c"][1] = literal.into(),
                    Inline::Literal(None) => value["c"][1] = source.into(),
                }
            }
            "Math" => {
                let latex = string(&value["c"][1])?;
                explicit_math(&latex, false)?;
                return self.math(latex, value["c"][0]["t"] == "DisplayMath", None);
            }
            "CodeBlock" => return self.code_block(value),
            "Str" => return self.prose_games(value),
            "RawInline" | "RawBlock" => return self.html(value),
            "Image" => return self.image(value),
            "Link" => {
                let target = string(&value["c"][2][0])?;
                value["c"][2][0] = self.link(&target)?.into();
            }
            "Table" => {
                let previous_table = self.in_table;
                self.in_table = true;
                crate::table::columns(&mut value)?;
                let id = format!("block-{}", self.blocks.len() + 1);
                self.blocks.push(SourceBlock {
                    id: id.clone(),
                    kind: kind.clone(),
                    prose: String::new(),
                    repeatable: self.repeating,
                });
                let content = value["c"]
                    .as_array_mut()
                    .ok_or_else(|| Failure::new("PDF-AST", "Invalid table"))?;
                for (i, item) in content.iter_mut().enumerate() {
                    let previous = self.repeating;
                    self.repeating = i == 3;
                    self.walk(item)?;
                    self.repeating = previous;
                }
                self.in_table = previous_table;
                return Ok(vec![
                    raw(
                        "RawBlock",
                        &format!("#mhfe-table(\"{id}\", mhfe-width => ["),
                    ),
                    value,
                    raw("RawBlock", "])"),
                ]);
            }
            _ => (),
        }
        let block = matches!(
            kind.as_str(),
            "Para"
                | "Plain"
                | "Header"
                | "BlockQuote"
                | "BulletList"
                | "OrderedList"
                | "HorizontalRule"
                | "Div"
        );
        let needs_width =
            (self.indented || self.in_table) && matches!(kind.as_str(), "Para" | "Plain");
        let indents_children = matches!(kind.as_str(), "BulletList" | "OrderedList" | "BlockQuote");
        let id = format!("block-{}", self.blocks.len() + 1);
        let block_index = self.blocks.len();
        if block {
            self.blocks.push(SourceBlock {
                id: id.clone(),
                kind,
                prose: String::new(),
                repeatable: self.repeating,
            });
        }
        let previous_indent = self.indented;
        self.indented |= indents_children;
        self.walk(&mut value)?;
        self.indented = previous_indent;
        if block {
            self.blocks[block_index].prose = if matches!(
                self.blocks[block_index].kind.as_str(),
                "Para" | "Plain" | "Header"
            ) {
                plain(&value)
            } else {
                String::new()
            };
            let heading = self.blocks[block_index].kind == "Header";
            let title = plain(&value["c"][2]);
            let mut rendered = Vec::new();
            if heading
                && value["c"][0] == 2
                && ["Part ", "Suite 4:", "Appendix:"]
                    .iter()
                    .any(|prefix| title.starts_with(prefix))
            {
                rendered.push(raw("RawBlock", "#pagebreak(weak: true)"));
            }
            let wrapper = if heading {
                "mhfe-heading"
            } else if needs_width {
                "mhfe-narrow-block"
            } else {
                "mhfe-block"
            };
            rendered.extend([
                raw("RawBlock", &format!("#{wrapper}(\"{id}\", mhfe-width => [")),
                value,
                raw("RawBlock", "])"),
            ]);
            Ok(rendered)
        } else {
            Ok(vec![value])
        }
    }

    fn math(
        &mut self,
        source: String,
        display: bool,
        conversion: Option<Value>,
    ) -> Result<Vec<Value>> {
        if self.expressions.len() >= 20_000 {
            return Err(Failure::new(
                "PDF-LIMIT",
                "Too many mathematical expressions",
            ));
        }
        let id = format!("math-{}", self.expressions.len() + 1);
        let mode = if display { "DisplayMath" } else { "InlineMath" };
        let presentation = crate::source::math_presentation(&source, &id)?;
        let tag = presentation
            .tag
            .map(|s| serde_json::to_string(&s))
            .transpose()?
            .unwrap_or_else(|| "none".into());
        self.expressions.push(Expression {
            id: id.clone(),
            sha256: digest(source.as_bytes()),
            source: source.clone(),
            display,
            conversion,
            repeatable: self.repeating,
            operators: presentation.operators,
            fences: presentation.fences,
        });
        Ok(vec![
            raw(
                "RawInline",
                &format!(
                    "#mhfe-math(\"{id}\", display: {display}, tag: {tag}, width: mhfe-width)["
                ),
            ),
            json!({"t":"Math","c":[{"t":mode},presentation.latex]}),
            raw("RawInline", &format!("]#mhfe-math-end(\"{id}\")")),
        ])
    }

    fn code_block(&mut self, value: Value) -> Result<Vec<Value>> {
        let label = value["c"][0][1][0].as_str().unwrap_or_default();
        let source = string(&value["c"][1])?;
        let automatic = ["", "text"].contains(&label) && self.notation.is_math_block(&source);
        if label == "math" {
            explicit_math(&source, true)?;
            return Ok(vec![
                json!({"t":"Para","c":self.math(source.trim().into(),true,None)?}),
            ]);
        }
        if label == "ascii-math" || automatic {
            let (latex, converted) = self.notation.block(&source)?;
            return Ok(vec![
                json!({"t":"Para","c":self.math(latex.clone(),true,Some(json!({"original":source,"latex":latex,"lines":converted})))?}),
            ]);
        }
        let id = format!("block-{}", self.blocks.len() + 1);
        self.blocks.push(SourceBlock {
            id: id.clone(),
            kind: "CodeBlock".into(),
            prose: source,
            repeatable: self.repeating,
        });
        Ok(vec![
            raw("RawBlock", &format!("#mhfe-code(\"{id}\", mhfe-width => [")),
            value,
            raw("RawBlock", "])"),
        ])
    }

    fn prose_games(&mut self, value: Value) -> Result<Vec<Value>> {
        let source = string(&value["c"])?;
        let pattern = Regex::new(r"[ΓΔΘ]\d+(?:_j)?|(?:Bad|Early)_[A-Za-z]")?;
        let game_index = Regex::new(r"^([ΓΔΘ])(\d+)_j$")?;
        let mut result = Vec::new();
        let mut end = 0;
        for found in pattern.find_iter(&source) {
            if source[..found.start()]
                .chars()
                .next_back()
                .is_some_and(char::is_alphanumeric)
                || source[found.end()..]
                    .chars()
                    .next()
                    .is_some_and(char::is_alphanumeric)
            {
                continue;
            }
            if end < found.start() {
                result.push(json!({"t":"Str","c":&source[end..found.start()]}));
            }
            let indexed = game_index.replace(found.as_str(), "${1}_{${2},j}");
            let conversion = self.notation.convert(&indexed)?;
            result.extend(self.math(
                conversion.latex.clone(),
                false,
                Some(serde_json::to_value(conversion)?),
            )?);
            end = found.end();
        }
        if end == 0 {
            return Ok(vec![value]);
        }
        if end < source.len() {
            result.push(json!({"t":"Str","c":&source[end..]}));
        }
        Ok(result)
    }

    fn link(&mut self, href: &str) -> Result<String> {
        if let Some(anchor) = href.strip_prefix('#') {
            self.links.push(anchor.into());
            return Ok(href.into());
        }
        if href.starts_with("https://")
            || href.starts_with("http://")
            || href.starts_with("mailto:")
        {
            return Ok(href.into());
        }
        if href.contains(':') || href.starts_with('/') {
            return Err(Failure::new("PDF-LINK", "Unsupported link scheme"));
        }
        let (path, fragment) = href.split_once('#').unwrap_or((href, ""));
        let target = self.local_path(path)?;
        let relative = target
            .strip_prefix(&self.root)
            .map_err(|_| Failure::new("PDF-LINK", "Link leaves the repository"))?;
        Ok(format!(
            "https://github.com/hobby-eng/mhfe-spec/blob/{}/{}{}",
            self.commit,
            relative.display(),
            if fragment.is_empty() {
                String::new()
            } else {
                format!("#{fragment}")
            }
        ))
    }

    fn local_path(&self, path: &str) -> Result<PathBuf> {
        let path = percent_decode(path)?;
        let parent = self
            .source_path
            .parent()
            .ok_or_else(|| Failure::new("PDF-PATH", "Source has no parent directory"))?;
        let candidate = parent.join(path).canonicalize()?;
        if !candidate.starts_with(&self.root) {
            return Err(Failure::new("PDF-PATH", "Resource leaves the repository"));
        }
        Ok(candidate)
    }

    fn image(&mut self, mut value: Value) -> Result<Vec<Value>> {
        let target = string(&value["c"][2][0])?;
        if target.starts_with("https://img.shields.io/")
            || target.starts_with("https://zenodo.org/")
        {
            return Ok(vec![
                json!({"t":"Span","c":[["",[],[]],value["c"][1].clone()]}),
            ]);
        }
        if target.contains(':') || target.starts_with('/') {
            return Err(Failure::new(
                "PDF-IMAGE",
                "Remote or absolute image is not allowed",
            ));
        }
        let path = self.local_path(&target)?;
        if !matches!(
            path.extension().and_then(|x| x.to_str()),
            Some("png" | "jpg" | "jpeg")
        ) {
            return Err(Failure::new("PDF-IMAGE", "Unsupported local image format"));
        }
        let relative = path
            .strip_prefix(&self.root)
            .map_err(|_| Failure::new("PDF-IMAGE", "Image leaves the repository"))?;
        value["c"][2][0] = format!("/{}", relative.display()).into();
        Ok(vec![value])
    }

    fn html(&mut self, value: Value) -> Result<Vec<Value>> {
        if value["c"][0] != "html" {
            return Err(Failure::new(
                "PDF-RAW",
                "Raw non-HTML markup is not allowed",
            ));
        }
        let html = string(&value["c"][1])?;
        if html.trim().starts_with("<!--") && html.trim().ends_with("-->") {
            return Ok(Vec::new());
        }
        match html.trim() {
            "<p align=\"center\">" => return Ok(vec![raw("RawBlock", "#align(center)[")]),
            "</p>" => return Ok(vec![raw("RawBlock", "]")]),
            "<br>" | "<br/>" | "<br />" => return Ok(vec![json!({"t":"LineBreak"})]),
            _ => (),
        }
        if Regex::new(r"^<img\s")?.is_match(&html) && html.trim_end().ends_with('>') {
            let attribute = |name: &str| -> Result<String> {
                let regex = Regex::new(&format!(r#"\b{name}="([^"]*)""#))?;
                Ok(regex
                    .captures(&html)
                    .map(|c| c[1].to_owned())
                    .unwrap_or_default())
            };
            let target = attribute("src")?;
            if target.is_empty() {
                return Err(Failure::new("PDF-HTML", "HTML image needs a quoted source"));
            }
            let width = attribute("width")?;
            let attrs = if width.is_empty() {
                json!([])
            } else {
                let pixels: f64 = width
                    .parse()
                    .map_err(|_| Failure::new("PDF-HTML", "Invalid image width"))?;
                json!([["width", format!("{}pt", pixels * 0.75)]])
            };
            return self.image(json!({"t":"Image","c":[["",[],attrs],[{"t":"Str","c":attribute("alt")?}],[target,""]]}));
        }
        Err(Failure::new(
            "PDF-HTML",
            "Unsupported raw HTML element or attributes",
        ))
    }
}

pub(crate) fn raw(kind: &str, source: &str) -> Value {
    json!({"t":kind,"c":["typst",source]})
}

pub(crate) fn string(value: &Value) -> Result<String> {
    value
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| Failure::new("PDF-AST", "Expected text in Pandoc AST"))
}

pub(crate) fn plain(value: &Value) -> String {
    match value["t"].as_str() {
        Some("Str") => value["c"].as_str().unwrap_or_default().into(),
        Some("Code") => value["c"][1].as_str().unwrap_or_default().into(),
        Some("Space" | "SoftBreak" | "LineBreak") => " ".into(),
        Some("RawBlock" | "RawInline" | "Math" | "Image") => String::new(),
        _ => match value {
            Value::Array(values) => values.iter().map(plain).collect(),
            Value::Object(values) => values.get("c").map(plain).unwrap_or_default(),
            _ => String::new(),
        },
    }
}

fn percent_decode(source: &str) -> Result<String> {
    let mut bytes = Vec::new();
    let input = source.as_bytes();
    let mut i = 0;
    while i < input.len() {
        if input[i] == b'%' {
            let hex = input
                .get(i + 1..i + 3)
                .ok_or_else(|| Failure::new("PDF-URL", "Incomplete URL escape"))?;
            let hex = std::str::from_utf8(hex)
                .map_err(|_| Failure::new("PDF-URL", "Invalid URL escape"))?;
            bytes.push(
                u8::from_str_radix(hex, 16)
                    .map_err(|_| Failure::new("PDF-URL", "Invalid URL escape"))?,
            );
            i += 3;
        } else {
            bytes.push(input[i]);
            i += 1;
        }
    }
    let decoded =
        String::from_utf8(bytes).map_err(|_| Failure::new("PDF-URL", "Invalid UTF-8 URL"))?;
    if Path::new(&decoded)
        .components()
        .any(|c| matches!(c, Component::RootDir | Component::Prefix(_)))
    {
        return Err(Failure::new(
            "PDF-URL",
            "Absolute local resource path is not allowed",
        ));
    }
    Ok(decoded)
}
