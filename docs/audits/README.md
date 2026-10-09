# Audit records

Audit files use one repository-wide chronological sequence for the `mhfe_spec` repository,
independent of the implementation repository and other projects. Markdown and JSON files with the
same number belong to the same review and must agree on metadata, finding IDs, severities, statuses,
and results. Reports record the reviewer model and reasoning-effort level; an unknown value is
marked unknown or `null` rather than inferred.

Reports follow the audit report standard and full audit guide of the wallet-tools project
(`docs/audits/AUDIT_STANDARD.md`, `docs/audits/AUDIT_TEMPLATE.md`, `docs/FULL_AUDIT_GUIDE.md`,
`docs/audit-report.schema.json` there). Finding IDs carry a category, for example `AUD-001-DOC001`;
severity and remediation status are separate fields. `CHECK-*` identifiers are checklist tasks, not
findings.

1. [AUD-001](audit-01-2026-09-22.md) · [JSON](audit-01-2026-09-22.json) — 2026-09-22 — Specification
   v0.3.0 correctness and citation audit (reviewed commit
   `e87eb5cdbd02b41c15aa512cd32055d56d3bd760`; finding remediated in first published specification
   commit `61033431380c7d5e8ad58f493ebc22a4ff8e69b4`)
2. [AUD-002](audit-02-2026-09-29.md) · [JSON](audit-02-2026-09-29.json) ·
   [import provenance](AUD-002-import.md) — 2026-09-29 — External specification and suite-3
   conformance review (Codex/OpenAI) of specification commit
   `588e5fbdda0425c42d97aac6a49ae17970aa7e20`; imported unchanged on 2026-09-30. Historical finding
   statuses are preserved.
3. [AUD-003](audit-03-2026-09-30.md) · [JSON](audit-03-2026-09-30.json) ·
   [harness scripts](AUD-003-harnesses/) — 2026-09-30 — Specification v0.4.0 (draft 0.3.1) notation,
   formula and wording audit (reviewed commit `588e5fbdda0425c42d97aac6a49ae17970aa7e20`; six low
   findings, remediated and verified in the 2026-09-30 addendum)

4. [AUD-004](audit-04-2026-09-30.md) · [JSON](audit-04-2026-09-30.json) ·
   [harness scripts](AUD-004-harnesses/) — 2026-09-30 — Complete README and appendix audit,
   utilities excluded (reviewed dirty source based on `240dab04de227938914de0a350f26a46cb0391cc`;
   five low documentation findings, all corrected and verified in the authorized working-tree
   addendum)

5. [AUD-005](audit-05-2026-09-30.md) · [JSON](audit-05-2026-09-30.json) ·
   [record metadata harness](AUD-005-harnesses/) — 2026-09-30 — Final document-only reread of README
   and both supplement parts at `8e65639917e8c88aeaf43ff9d5c99d3c42ba9c13`. Two low wording findings
   (recurrence of AUD-004-DOC001 and new AUD-005-DOC001) were corrected and textually verified in
   the authorized addendum. The other four AUD-004 corrections remain present. No program checks or
   vector computation were run.

## Evidence and harness scripts

Since 2026-09-30, audit evidence (command logs and records, snapshots, checksums, validation output
and diffs) is kept only locally by the maintainer and is not published here; each report states the
commands, counts, results and hashes a reader needs, and its links into an `AUD-NNN-evidence/`
folder point to that local evidence. The audit-only scripts are published, one folder per audit,
each with a README that explains what the scripts check and how to run them:
[AUD-003](AUD-003-harnesses/), [AUD-004](AUD-004-harnesses/) and [AUD-005](AUD-005-harnesses/)
(report metadata only).

Historical findings describe only the reviewed snapshot. The AUD-004 snapshot and its manifest
precede the subsequent AUD-002 report and suite-3 vector imports; their publication does not repeat
the original audit or change its recorded results. The
[publication record](AUD-004-publication.json) retains reverse patches and hashes for reconstructing
the three subsequently edited documents at the verified AUD-004 snapshot, including after a Git
amend.

The [AUD-005 publication record](AUD-005-publication.json) pins the later release-document and
corpus update and retains a reverse patch to the verified AUD-005 remediation text. This publication
work does not replace the original reviewed snapshot or claim another cryptographic audit.

## Record edits after an audit

After the audit this record was edited; recorded findings, outcomes and reviewed-source hashes are
unchanged; this is not a new audit.
