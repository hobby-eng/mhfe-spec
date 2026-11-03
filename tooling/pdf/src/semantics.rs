use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::layout::{counts, normalized};
use crate::process::{Toolchain, json_file, text};
use roxmltree::Node;
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::Path;

#[derive(Default, Debug, PartialEq, Eq, Serialize)]
struct Features {
    glyphs: String,
    order: String,
    attachments: Vec<(String, String, String)>,
    fractions: Vec<(String, String)>,
    decorations: Vec<(String, String, String)>,
}

/// Cross-checks the compiled Typst math trees against a separate MathML writer.
pub(crate) fn verify(
    document: &Document,
    metadata: &[Value],
    tools: &Toolchain,
    directory: &Path,
    name: &str,
) -> Result<()> {
    let blocks: Vec<_> = document.expressions.iter().map(|expression| json!({"t":"Para","c":[{"t":"Math","c":[{"t":if expression.display {"DisplayMath"} else {"InlineMath"}},expression.source]}]})).collect();
    let mut ast = document.ast.clone();
    ast["blocks"] = blocks.into();
    let html = text(tools.pandoc(
        &[
            "--from",
            "json",
            "--to",
            "html5",
            "--math-method=mathml",
            "--fail-if-warnings",
        ],
        &serde_json::to_vec(&ast)?,
    )?)?;
    let source = format!("<root>{html}</root>");
    let xml = roxmltree::Document::parse(&source)
        .map_err(|e| Failure::new("PDF-MATHML", e.to_string()))?;
    let mathml: Vec<_> = xml
        .descendants()
        .filter(|node| node.has_tag_name("math"))
        .collect();
    if mathml.len() != document.expressions.len() {
        return Err(Failure::new(
            "PDF-MATHML",
            "MathML expression inventory is incomplete",
        ));
    }
    let mut native = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut current = "";
    let mut tail = String::new();
    let mut display = false;
    let mut promoted = false;
    let modes: BTreeMap<_, _> = document
        .expressions
        .iter()
        .map(|e| (e.id.as_str(), e.display))
        .collect();
    for record in metadata {
        if record["kind"] == "math-start" {
            current = record["id"].as_str().unwrap_or_default();
            tail.clear();
            display = *modes
                .get(current)
                .ok_or_else(|| Failure::new("PDF-MATH-LAYOUT", "Unknown expression mode"))?;
            if record["display"] != display {
                return Err(Failure::new(
                    "PDF-MATH-LAYOUT",
                    format!("Canonical display metadata changed for {current}"),
                ));
            }
            promoted = false;
        }
        if record["kind"] == "math-promoted" {
            tail = crate::math_content::glyphs(&record["tail"]);
            promoted = true;
        }
        if record["kind"] == "native-math" && seen.insert(current) {
            if record["block"] != (display || promoted) {
                return Err(Failure::new(
                    "PDF-MATH-LAYOUT",
                    format!("Inline/display mode changed for {current}"),
                ));
            }
            let mut body = record["body"].clone();
            if !tail.is_empty() {
                let children = body["children"]
                    .as_array_mut()
                    .ok_or_else(|| Failure::new("PDF-MATHML", "Missing promoted equation body"))?;
                if children
                    .last()
                    .is_none_or(|v| v["func"] != "text" || v["text"] != tail)
                {
                    return Err(Failure::new(
                        "PDF-MATHML",
                        "Promoted sentence punctuation was lost or changed",
                    ));
                }
                children.pop();
            }
            native.push(body);
        }
    }
    if native.len() != mathml.len() {
        return Err(Failure::new(
            "PDF-MATHML",
            "Compiled math tree inventory is incomplete",
        ));
    }
    let mut evidence = Vec::new();
    for ((expression, xml), typst) in document.expressions.iter().zip(mathml).zip(native) {
        let mut expected = Features::default();
        ml_features(xml, &mut expected);
        expected.glyphs = ml_text(xml);
        expected.order = ml_order(xml);
        let mut actual = Features::default();
        native_features(&typst, &mut actual);
        actual.glyphs = native_text(&typst);
        actual.order = native_order(&typst);
        expected.attachments.sort();
        actual.attachments.sort();
        expected.fractions.sort();
        actual.fractions.sort();
        expected.decorations.sort();
        actual.decorations.sort();
        let equal = expected.order == actual.order
            && counts(&expected.glyphs) == counts(&actual.glyphs)
            && expected.attachments == actual.attachments
            && expected.fractions == actual.fractions
            && expected.decorations == actual.decorations;
        evidence.push(json!({"id":expression.id,"mathml":expected,"typst":actual,"pass":equal}));
    }
    json_file(
        &directory.join(format!("{name}-math-semantics.json")),
        &evidence,
    )?;
    if evidence.iter().any(|value| value["pass"] != true) {
        return Err(Failure::new(
            "PDF-MATHML",
            "Typst glyphs, scripts or fractions differ from the independent MathML representation",
        ));
    }
    crate::legacy_oracle::verify(name, document, &evidence, directory)?;
    Ok(())
}

fn ml_text(node: Node<'_, '_>) -> String {
    let mut text = String::new();
    for child in node.descendants().filter(|child| {
        matches!(child.tag_name().name(), "mi" | "mn" | "mo" | "mtext")
            && !child.ancestors().any(|a| a.has_tag_name("annotation"))
    }) {
        for text_node in child.descendants().filter(Node::is_text) {
            let glyphs = text_node.text().unwrap_or_default();
            if child.has_tag_name("mo")
                && child.attribute("accent") == Some("true")
                && matches!(glyphs, "⏟" | "⏞")
            {
                continue;
            }
            // TeX's mathematical asterisk is U+002A in this MathML writer and
            // U+2217 in Typst. Quoted/textual asterisks retain their literal code point.
            if child.has_tag_name("mo") {
                text.push_str(&glyphs.replace('*', "∗"));
            } else {
                text.push_str(glyphs);
            }
        }
    }
    normalized(&text)
}

fn ml_base(node: Node<'_, '_>) -> String {
    if matches!(
        node.tag_name().name(),
        "msub" | "msup" | "msubsup" | "munder" | "mover" | "munderover"
    ) && let Some(child) = node.children().find(Node::is_element)
    {
        return ml_base(child);
    }
    let children: Vec<_> = node
        .children()
        .filter(Node::is_element)
        .filter(|child| !child.has_tag_name("annotation"))
        .collect();
    if matches!(node.tag_name().name(), "mrow" | "mstyle" | "semantics") && children.len() == 1 {
        return ml_base(children[0]);
    }
    ml_text(node)
}

fn ml_features(node: Node<'_, '_>, features: &mut Features) {
    ml_features_with_base(node, features, None);
}

fn ml_features_with_base(
    node: Node<'_, '_>,
    features: &mut Features,
    grouped_base: Option<String>,
) {
    let children: Vec<_> = node.children().filter(Node::is_element).collect();
    let name = node.tag_name().name();
    if matches!(name, "munder" | "mover") && children.len() == 2 {
        let inner: Vec<_> = children[0].children().filter(Node::is_element).collect();
        let marker = |node: Node<'_, '_>| match node.text() {
            Some("⏟") if node.attribute("accent") == Some("true") => Some("underbrace"),
            Some("⏞") if node.attribute("accent") == Some("true") => Some("overbrace"),
            _ => None,
        };
        if inner.len() == 2
            && matches!(children[0].tag_name().name(), "munder" | "mover")
            && let Some(kind) = marker(inner[1])
        {
            features
                .decorations
                .push((ml_text(inner[0]), kind.into(), ml_text(children[1])));
            ml_features(inner[0], features);
            ml_features(children[1], features);
            return;
        }
        if let Some(kind) = marker(children[1]) {
            features
                .decorations
                .push((ml_text(children[0]), kind.into(), String::new()));
            ml_features(children[0], features);
            return;
        }
    }
    if children.len() >= 2 {
        let base = grouped_base.unwrap_or_else(|| ml_base(children[0]));
        match name {
            "msub" | "munder" => {
                features
                    .attachments
                    .push((base, "sub".into(), ml_text(children[1])))
            }
            "msup" | "mover" => {
                features
                    .attachments
                    .push((base, "super".into(), ml_text(children[1])))
            }
            "msubsup" | "munderover" if children.len() >= 3 => {
                features
                    .attachments
                    .push((base.clone(), "sub".into(), ml_text(children[1])));
                features
                    .attachments
                    .push((base, "super".into(), ml_text(children[2])));
            }
            "mfrac" => features
                .fractions
                .push((ml_text(children[0]), ml_text(children[1]))),
            _ => (),
        }
    }
    for (index, child) in children.iter().enumerate() {
        if child.has_tag_name("annotation") {
            continue;
        }
        let scripted: Vec<_> = child.children().filter(Node::is_element).collect();
        let close = scripted
            .first()
            .filter(|base| {
                matches!(child.tag_name().name(), "msub" | "msup" | "msubsup")
                    && base.has_tag_name("mo")
            })
            .and_then(Node::text);
        let base = close.and_then(|close| {
            enclosed_prefix(
                index,
                close,
                |i| {
                    let previous = children[i];
                    if previous.has_tag_name("mo") {
                        previous.text().map(str::to_owned)
                    } else {
                        None
                    }
                },
                |i| ml_text(children[i]),
            )
        });
        ml_features_with_base(*child, features, base);
    }
}

fn native_text(value: &Value) -> String {
    normalized(&crate::math_content::glyphs(value))
}

fn native_base(value: &Value) -> String {
    match value["func"].as_str() {
        Some("attach") => native_base(&value["base"]),
        Some("styled") => native_base(&value["child"]),
        Some("sequence")
            if value["children"]
                .as_array()
                .is_some_and(|items| items.len() == 1) =>
        {
            native_base(&value["children"][0])
        }
        _ => native_text(value),
    }
}

fn native_features(value: &Value, features: &mut Features) {
    native_features_with_base(value, features, None);
}

fn native_features_with_base(value: &Value, features: &mut Features, grouped_base: Option<String>) {
    if matches!(value["func"].as_str(), Some("underbrace" | "overbrace")) {
        features.decorations.push((
            native_text(&value["body"]),
            value["func"].as_str().unwrap_or_default().into(),
            native_text(&value["annotation"]),
        ));
    }
    if value["func"] == "sequence"
        && let Some(children) = value["children"].as_array()
    {
        for pair in children.windows(2) {
            if pair[1]["func"] == "primes" {
                features.attachments.push((
                    native_base(&pair[0]),
                    "super".into(),
                    native_text(&pair[1]),
                ));
            }
        }
        for (index, child) in children.iter().enumerate() {
            native_features_with_base(child, features, parenthesized_base(children, index));
        }
        return;
    }
    if value["func"] == "attach" {
        for (field, kind) in crate::math_content::SCRIPTS {
            if let Some(script) = value.get(field) {
                features.attachments.push((
                    grouped_base
                        .clone()
                        .unwrap_or_else(|| native_base(&value["base"])),
                    kind.into(),
                    native_text(script),
                ));
            }
        }
    }
    if value["func"] == "frac" {
        features
            .fractions
            .push((native_text(&value["num"]), native_text(&value["denom"])));
    }
    match value {
        Value::Array(values) => {
            for child in values {
                native_features(child, features);
            }
        }
        Value::Object(values) => {
            for (key, child) in values {
                if key != "styles" {
                    native_features(child, features);
                }
            }
        }
        _ => (),
    }
}

fn parenthesized_base(children: &[Value], index: usize) -> Option<String> {
    let child = &children[index];
    if child["func"] != "attach" || child["base"]["func"] != "symbol" {
        return None;
    }
    let close = child["base"]["text"].as_str()?;
    enclosed_prefix(
        index,
        close,
        |start| {
            let previous = if children[start]["func"] == "attach" {
                &children[start]["base"]
            } else {
                &children[start]
            };
            if previous["func"] == "symbol" {
                previous["text"].as_str().map(str::to_owned)
            } else {
                None
            }
        },
        |start| native_text(&children[start]),
    )
}

fn enclosed_prefix(
    index: usize,
    close: &str,
    symbol: impl Fn(usize) -> Option<String>,
    text: impl Fn(usize) -> String,
) -> Option<String> {
    let open = match close {
        ")" => "(",
        "]" => "[",
        "}" => "{",
        "⌋" => "⌊",
        "⌉" => "⌈",
        _ => return None,
    };
    let mut nesting = 1;
    for start in (0..index).rev() {
        let Some(previous) = symbol(start) else {
            continue;
        };
        if previous == close {
            nesting += 1;
        }
        if previous == open {
            nesting -= 1;
        }
        if nesting == 0 {
            // Escaped parentheses are separate symbols in Typst's tree. A power
            // placed on the closing symbol still applies to the delimited group.
            return Some((start..index).map(&text).collect::<String>() + close);
        }
    }
    None
}

fn ml_order(node: Node<'_, '_>) -> String {
    if matches!(node.tag_name().name(), "mi" | "mn" | "mo" | "mtext") {
        return ml_text(node);
    }
    let children: Vec<_> = node.children().filter(Node::is_element).collect();
    let name = node.tag_name().name();
    if matches!(
        name,
        "msub" | "msup" | "msubsup" | "munder" | "mover" | "munderover"
    ) {
        let base = children.first().map(|n| ml_order(*n)).unwrap_or_default();
        let brace = children.iter().take(2).any(|node| {
            node.descendants().any(|n| {
                n.attribute("accent") == Some("true") && matches!(n.text(), Some("⏟" | "⏞"))
            })
        });
        if brace {
            return base;
        }
        let mut scripts = Vec::new();
        if matches!(name, "msub" | "msubsup" | "munder" | "munderover") && children.len() >= 2 {
            scripts.push(("sub", ml_text(children[1])));
        }
        if matches!(name, "msup" | "msubsup" | "mover" | "munderover") {
            let index = if matches!(name, "msubsup" | "munderover") {
                2
            } else {
                1
            };
            if let Some(child) = children.get(index) {
                scripts.push(("super", ml_text(*child)));
            }
        }
        return base + &script_order(scripts);
    }
    children
        .into_iter()
        .filter(|n| !n.has_tag_name("annotation"))
        .map(ml_order)
        .collect()
}

fn native_order(value: &Value) -> String {
    match value["func"].as_str() {
        Some("attach") => {
            let scripts = crate::math_content::SCRIPTS
                .iter()
                .filter_map(|(field, kind)| value.get(*field).map(|v| (*kind, native_text(v))))
                .collect();
            native_order(&value["base"]) + &script_order(scripts)
        }
        Some("primes") => script_order(vec![("super", native_text(value))]),
        Some("styled") => native_order(&value["child"]),
        Some("underbrace" | "overbrace") => native_order(&value["body"]),
        Some("frac") => native_order(&value["num"]) + &native_order(&value["denom"]),
        Some("sequence") => native_order(&value["children"]),
        Some("lr") => native_order(&value["body"]),
        Some("op") => native_order(&value["text"]),
        Some("text" | "symbol") => normalized(value["text"].as_str().unwrap_or_default()),
        _ => match value {
            Value::Array(items) => items.iter().map(native_order).collect(),
            Value::Object(items) => items
                .iter()
                .filter(|(k, _)| k.as_str() != "styles")
                .map(|(_, v)| native_order(v))
                .collect(),
            _ => String::new(),
        },
    }
}

fn script_order(mut scripts: Vec<(&str, String)>) -> String {
    scripts.sort();
    scripts
        .into_iter()
        .map(|(kind, text)| format!("«{kind}:{text}»"))
        .collect()
}
