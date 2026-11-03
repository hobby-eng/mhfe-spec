use crate::document::plain;
use crate::failure::{Failure, Result};
use serde_json::{Value, json};

/// Gives prose columns room while keeping short labels and numeric fields compact.
pub(crate) fn columns(table: &mut Value) -> Result<()> {
    let cells = table["c"][3][1][0][1]
        .as_array()
        .ok_or_else(|| Failure::new("PDF-TABLE", "A table needs a header row"))?;
    let headings: Vec<_> = cells.iter().map(|cell| plain(&cell[4])).collect();
    let first = headings.first().map(String::as_str).unwrap_or_default();
    let second = headings.get(1).map(String::as_str).unwrap_or_default();
    // These presentation profiles are keyed by header text, never by volatile block IDs.
    // Other tables use Typst's content measurements, not Markdown separator lengths.
    let widths: &[f64] = match (first, second, headings.len()) {
        ("Symbol", "Meaning", 2) => &[0.22, 0.78],
        ("Component", "Value", 2) => &[0.25, 0.75],
        ("Supplied with the container", _, 2) => &[0.30, 0.70],
        ("Original seed phrase", "Recovery", 3) => &[0.17, 0.42, 0.41],
        ("Code", "Section", 3) => &[0.12, 0.54, 0.34],
        ("Result", "Source lengths", 4) => &[0.17, 0.17, 0.34, 0.32],
        ("Result", "Information available to the adversary", 4) => &[0.16, 0.37, 0.25, 0.22],
        ("Password", "Bits", 5) => &[0.25, 0.07, 0.22, 0.22, 0.24],
        ("Source", "Search", 3) => &[0.14, 0.56, 0.30],
        ("Check", "What it confirms", 3) => &[0.23, 0.37, 0.40],
        ("What leaked", "Explicit test of a guess", 3) => &[0.36, 0.38, 0.26],
        ("Source words", "ENT", 5) => &[0.10, 0.07, 0.07, 0.43, 0.33],
        ("Source words", _, 4) if second.starts_with("Original BIP39 checksum") => {
            &[0.14, 0.43, 0.28, 0.15]
        }
        ("Environment", "Recovery", 3) => &[0.52, 0.20, 0.28],
        // The combined Early_P term is an indivisible parenthesized formula.
        ("Term", "Event", 2) if plain(table).contains("(12·p_1·k_A") => &[0.40, 0.60],
        ("Term", "Event", 2) => &[0.29, 0.71],
        _ => &[],
    };
    let columns = table["c"][2]
        .as_array_mut()
        .ok_or_else(|| Failure::new("PDF-TABLE", "Invalid table columns"))?;
    for (index, column) in columns.iter_mut().enumerate() {
        column[1] = match widths.get(index) {
            Some(width) => json!({"t":"ColWidth","c":width}),
            None => json!({"t":"ColWidthDefault"}),
        };
    }
    Ok(())
}
