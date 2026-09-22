# Audit records

Audit files use one repository-wide chronological sequence for the `mhfe_spec` repository, independent of the implementation repository and other projects. Markdown and JSON files with the same number belong to the same review and must agree on metadata, finding IDs, severities, statuses, and results. Reports record the reviewer model and reasoning-effort level; an unknown value is marked unknown or `null` rather than inferred.

Reports follow the audit report standard and full audit guide of the wallet-tools project (`docs/audits/AUDIT_STANDARD.md`, `docs/audits/AUDIT_TEMPLATE.md`, `docs/FULL_AUDIT_GUIDE.md`, `docs/audit-report.schema.json` there). Finding IDs carry a category, for example `AUD-001-DOC001`; severity and remediation status are separate fields. `CHECK-*` identifiers are checklist tasks, not findings.

1. [AUD-001](audit-01-2026-09-22.md) · [JSON](audit-01-2026-09-22.json) — 2026-09-22 — Specification v0.3.0 correctness and citation audit (reviewed commit `4e7d03a1e1cbf68b407c3affd93c786884cd6ed1`; finding remediated in first published specification commit `b3f64306563d15832c846601d16fd20236a0ea75`)

Historical findings describe only the reviewed snapshot.
