use serde_json::Value;

pub(crate) const SCRIPTS: [(&str, &str); 6] = [
    ("b", "sub"),
    ("br", "sub"),
    ("bl", "left-sub"),
    ("t", "super"),
    ("tr", "super"),
    ("tl", "left-super"),
];

/// Reads visible mathematical content in rendering order, including prime nodes.
pub(crate) fn glyphs(value: &Value) -> String {
    match value["func"].as_str() {
        Some("text" | "symbol") => value["text"].as_str().unwrap_or_default().into(),
        Some("primes") => "′".repeat(value["count"].as_u64().unwrap_or(0) as usize),
        Some("attach") => {
            glyphs(&value["base"])
                + &SCRIPTS
                    .iter()
                    .map(|(field, _)| glyphs(&value[*field]))
                    .collect::<String>()
        }
        Some("frac") => glyphs(&value["num"]) + &glyphs(&value["denom"]),
        Some("op") => glyphs(&value["text"]),
        Some("styled") => glyphs(&value["child"]),
        Some("lr") => glyphs(&value["body"]),
        Some("sequence") => glyphs(&value["children"]),
        Some("underbrace" | "overbrace") => glyphs(&value["body"]) + &glyphs(&value["annotation"]),
        _ => match value {
            Value::Array(values) => values.iter().map(glyphs).collect(),
            Value::Object(values) => values
                .iter()
                .filter(|(key, _)| key.as_str() != "styles")
                .map(|(_, child)| glyphs(child))
                .collect(),
            _ => String::new(),
        },
    }
}

/// Decorations are drawn as curves, but also have PDF extraction characters.
pub(crate) fn pdf_decorations(value: &Value) -> String {
    let own = match value["func"].as_str() {
        Some("underbrace") => "⏟",
        Some("overbrace") => "⏞",
        _ => "",
    };
    own.to_owned()
        + &match value {
            Value::Array(items) => items.iter().map(pdf_decorations).collect::<String>(),
            Value::Object(items) => items
                .iter()
                .filter(|(k, _)| k.as_str() != "styles")
                .map(|(_, v)| pdf_decorations(v))
                .collect(),
            _ => String::new(),
        }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn includes_explicit_corner_prime_attachments() {
        let expression = serde_json::json!({"func":"attach","base":{"func":"symbol","text":"G"},"tr":{"func":"primes","count":2}});
        assert_eq!(glyphs(&expression), "G′′");
    }
}
