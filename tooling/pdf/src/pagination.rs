use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::layout::position;
use serde_json::Value;

/// Enforces whole-table and whole-code-block pagination, not just whole rows.
pub(crate) fn verify(document: &Document, metadata: &[Value]) -> Result<()> {
    for block in &document.blocks {
        let (kind, stage) = match block.kind.as_str() {
            "Table" => ("table", "PDF-TABLE"),
            "CodeBlock" => ("code", "PDF-CODE"),
            _ => continue,
        };
        let start_kind = format!("{kind}-start");
        let end_kind = format!("{kind}-end");
        let start = metadata
            .iter()
            .position(|v| v["kind"] == start_kind && v["id"] == block.id)
            .ok_or_else(|| Failure::new(stage, "Missing atomic-block start"))?;
        let end = metadata
            .iter()
            .enumerate()
            .skip(start + 1)
            .find(|(_, v)| v["kind"] == end_kind && v["id"] == block.id)
            .map(|(i, _)| i)
            .ok_or_else(|| Failure::new(stage, "Missing atomic-block end"))?;
        let page = position(&metadata[start]["pos"])?.page;
        for record in &metadata[start..=end] {
            if position(&record["pos"])?.page != page {
                return Err(Failure::new(
                    stage,
                    format!("{} crosses a page boundary", block.id),
                ));
            }
        }
    }
    Ok(())
}
