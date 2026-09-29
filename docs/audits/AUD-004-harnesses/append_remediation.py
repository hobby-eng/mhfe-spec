"""Append the authorized source remediation without rewriting baseline findings."""

import datetime
import json
from pathlib import Path


EVIDENCE = Path(__file__).resolve().parents[1]
AUDITS = EVIDENCE.parent
snapshot = json.loads((EVIDENCE / "remediation-snapshot.json").read_text())
assert (EVIDENCE / "remediation-review.md").exists(), "Independent cross-review is required"
report_path = AUDITS / "audit-04-2026-09-30.json"
markdown_path = report_path.with_suffix(".md")
report = json.loads(report_path.read_text())
assert "remediationSnapshot" not in report, "Do not append the same phase twice"
now = datetime.datetime.now(datetime.timezone.utc).isoformat()

fixes = [
    "Replaced the universal single-line claim with the exact CR/LF rationale; retained accepted controls, separators and all existing normalization/byte limits.",
    "Identified RustCrypto argon2 0.5.3 and OpenSSL-backed Python measurements; preserved the numbers and removed the unsupported universal threading multiplier.",
    "Limited the 3 TiB comparison to ordinary personal recovery computers; retained all memory mappings and the Argon2-derived upper bound.",
    "Separated the total cycle-walk permutation from its partial rejecting wrapper, and limited the theorem attribution to the core before rejection; preserved the historical refusal rule.",
    "Restricted the exact image-cardinality statement to deterministic lossless encodings, matching the selected packing while excluding randomized representations.",
]
common_evidence = [
    "AUD-004-evidence/remediation.diff",
    "AUD-004-evidence/remediation-snapshot.json",
    "AUD-004-evidence/remediation-checks.log",
    "AUD-004-evidence/remediation-format-check.log",
    "AUD-004-evidence/remediation-review.md",
]
for row, fix in zip(report["remediation"], fixes, strict=True):
    row.update(
        status="verified",
        verifiedAt=now,
        sourceFingerprint=snapshot["sourceFingerprint"],
        fixSummary=fix,
        evidence=common_evidence + [
            "AUD-004-evidence/agent-protocol-remediation.md"
            if row["id"].endswith("001")
            else "AUD-004-evidence/agent-appendix-remediation.md"
        ],
        commitLimitation="No commit was requested or created; verification identifies the exact dirty source snapshot by SHA-256 instead.",
    )
report["remediationSnapshot"] = snapshot
report["remediationCompletedAt"] = now
report["remediationChecks"] = []
for path in sorted(EVIDENCE.glob("remediation-*.command.json")):
    check = json.loads(path.read_text())
    assert check["exitCode"] == 0, path
    check["outcome"] = "passed"
    check["evidence"] = "AUD-004-evidence/" + check["log"]
    report["remediationChecks"].append(check)
report["remediationCoverage"] = [
    {
        "checkId": check_id,
        "outcome": "passed",
        "sourceFingerprint": snapshot["sourceFingerprint"],
        "scope": "Reverification of the documented baseline defects and edited wording only",
        "evidence": common_evidence,
    }
    for check_id in ("CHECK-ARC-003", "CHECK-DOC-001", "CHECK-DOC-002")
]
report["remediationAssessment"] = {
    "verifiedFindings": 5,
    "remainingOpenFindings": 0,
    "newFindingEstablished": False,
    "cryptographicDefinitionChanged": False,
    "applicationContractClarified": True,
    "implementationConformanceVerified": False,
    "releaseAcceptance": "Not assessed or granted; publication, benchmarking and specialist-analysis gaps remain.",
    "remainingPriorities": [
        "Publish suite-3 vectors and generator/verifier provenance; the expanded requirements are now written but the corpus was not produced or verified.",
        "Measure complete attack costs with reproducible hardware/software context; rates remain explicit assumptions and extrapolations.",
        "Define and analyze construction-specific security games with independent specialist review; no proof or lower bound was obtained.",
        "Check clarified recovery-result and Unicode contracts in utilities in a separately authorized implementation review.",
        "Consider an expanded authenticated format only if requirements change; suite 3 remains unchanged.",
    ],
}
report_path.write_text(json.dumps(report, indent=2) + "\n")

markdown = markdown_path.read_text()
notice = (
    "**Remediation update, 2026-09-30:** All five findings were corrected and verified in the "
    "authorized working-tree follow-up. The baseline register remains unchanged; see the "
    "[remediation addendum](#authorized-remediation-addendum--2026-09-30) for current status "
    "and exact source hashes. No implementation or release acceptance is implied.\n\n"
)
first_paragraph = markdown.index("\n\n") + 2
markdown = markdown[:first_paragraph] + notice + markdown[first_paragraph:]
markdown = markdown.replace(
    "No source, vector, utility or dependency remediation was applied; no commit or push was made.",
    "During the baseline, no source, vector, utility or dependency remediation was applied. "
    "The later authorized documentation edits are recorded separately below; no commit or push was made.",
)
markdown = markdown.replace(
    "This is a review-only baseline. All proposed changes await a separate remediation request; source was preserved. No owner risk acceptance is inferred.",
    "The following table preserves the review-only baseline before the user's separate request "
    "to fix all issues. The authorized follow-up is recorded in the addendum below; no owner risk acceptance is inferred.",
)
markdown = markdown.replace(
    "The final integrity manifest covers retained evidence and the paired reports/index, excluding itself and final validation artifacts to avoid self-referential hashes; the exact manifest scope is recorded during final validation.",
    "The final SHA256SUMS manifest covers the two remediated source documents, paired reports, "
    "audit index and every retained evidence file, including report-validation.json. It excludes "
    "only SHA256SUMS itself and final-integrity.log/final-integrity.command.json to avoid "
    "self-referential hashes. Paths are relative to the mhfe_spec repository root.",
)
addendum = f"""

## Authorized remediation addendum — 2026-09-30

The user explicitly requested that all issues be fixed after the review. The coordinator and source
reviewers edited only README.md and docs/DESIGN-NOTES.md, preserving the pre-existing work. The
editorial reviewer independently cross-reviewed the resulting source within the same AI workflow.
Verification completed at **{now}**. No utility, implementation, vector, dependency or CHANGELOG
edit belongs to this follow-up. No commit or push was requested or made; both commit fields remain
null, and the verified working-tree fingerprint is
`{snapshot['sourceFingerprint']}`.

| Verified source | SHA-256 |
| --- | --- |
"""
for path, digest in snapshot["sourceHashes"].items():
    addendum += f"| `{path}` | `{digest}` |\n"
addendum += """

### Current remediation status

The five original Low findings are now verified as corrected. The original findings, source hashes,
severity and coverage ledger above continue to describe the baseline, not the remediated bytes.

| Finding ID | Status | Fix commit | Verification commit | Evidence |
| --- | --- | --- | --- | --- |
"""
for row in report["remediation"]:
    addendum += (
        f"| {row['id']} | verified | None; working tree | None; source hashes above | "
        "[Scoped diff](AUD-004-evidence/remediation.diff), "
        "[cross-review](AUD-004-evidence/remediation-review.md) |\n"
    )
addendum += "\n"
for row in report["remediation"]:
    addendum += f"- **{row['id']}:** {row['fixSummary']}\n"
addendum += """

### Additional improvements and verification

The same-format editorial improvements now recommend retaining the original word count with
suite/PIM/MEM, require an explicit unverified status for every 24-word recovery unless checked
against a wallet reference, and distinguish a short verifier match from wallet identity. Rehearsal
rules now clearly separate temporary sensitive computation from display, clipboard, export and
persistent storage. Vector requirements now include normalized byte boundaries, accepted Unicode
separators, normalization contraction and expansion, mode-specific negative outcomes, round-input
bytes and generator/verifier revisions.

The supplement now identifies the source and limitations of the PBKDF2 extrapolation, labels the
MHFE rate as unmeasured, shows sensitivity to assumed rates and states the hypothetical farm's
bandwidth assumption. It also clarifies salt repetition/collision exceptions, side-channel/model
limits, historical reading routes and the distinct security questions requiring further research.

The complete README fenced blocks, suite parameter table, packing definition and permutation
definition compare byte-for-byte with the captured baseline. All nine Rationale answers remain.
The accepted password domain, primitives, rounds, domain strings and numerical parameters are
unchanged. New or clarified application-facing requirements do require future implementation
conformance review; no assertion about existing utilities is made here.

| Follow-up check | Result | Evidence |
| --- | --- | --- |
| Baseline reconstruction and current snapshot | Both original source hashes reproduced in memory; current hashes and scoped remediation diff retained | [Snapshot command](AUD-004-evidence/remediation-snapshot.command.json), [snapshot](AUD-004-evidence/remediation-snapshot.json), [diff](AUD-004-evidence/remediation.diff) |
| Frozen definitions, references and navigation | Passed; nine Rationale answers, 57 local links, 45 consecutive references | [Checks](AUD-004-evidence/remediation-checks.log), [command](AUD-004-evidence/remediation-checks.command.json) |
| Pinned source formatter | Passed for both edited documents | [Formatting](AUD-004-evidence/remediation-format-check.log), [command](AUD-004-evidence/remediation-format-check.command.json) |
| Independent editorial cross-review | All five corrections verified; no additional defect established within scope | [Cross-review](AUD-004-evidence/remediation-review.md) |
| Reverification of CHECK-ARC-003, CHECK-DOC-001 and CHECK-DOC-002 | Passed for the remediated defects; baseline ledger is preserved | [README contribution](AUD-004-evidence/agent-protocol-remediation.md), [appendix contribution](AUD-004-evidence/agent-appendix-remediation.md), [cross-review](AUD-004-evidence/remediation-review.md) |
| Audit pair/schema, evidence links and integrity | Final acceptance results retained separately | [Validation](AUD-004-evidence/report-validation.json), [validation command](AUD-004-evidence/validate-report.command.json), [final integrity](AUD-004-evidence/final-integrity.log) |

The finite baseline algebra and Unicode results are retained as baseline evidence, not relabelled as
fresh implementation tests. Re-running their unchanged formulas would add no evidence about the
edited prose. Current source syntax, references, frozen definitions and the five corrections were
verified separately as recorded above.

### Remaining proposals

Publishing and independently reproducing the suite-3 corpus, obtaining measured attacker costs and
performing independent construction-specific cryptanalysis remain substantive future work. The
relevant requirements and caveats are clearer; their completion is not claimed. The optional idea
of a larger authenticated, self-describing format remains a separate requirements trade-off, not
a repair to the existing 24-word suite. No source compatibility change or arbitrary cryptographic
parameter change is justified by this audit. There are zero remaining open findings among these
five documentation defects; the experimental limitations and excluded implementation checks remain.
"""
markdown_path.write_text(markdown + addendum)
index_path = AUDITS / "README.md"
index = index_path.read_text()
assert "audit-04-2026-09-30.md" not in index
index = index.replace(
    "\nHistorical findings describe only the reviewed snapshot.",
    "\n4. [AUD-004](audit-04-2026-09-30.md) · [JSON](audit-04-2026-09-30.json) · "
    "[evidence](AUD-004-evidence/) — 2026-09-30 — Complete README and appendix audit, "
    "utilities excluded (reviewed dirty source based on `f46758874c92e91f5658028217f7c121229b0b36`; "
    "five low documentation findings, all corrected and verified in the authorized working-tree addendum)\n"
    "\nHistorical findings describe only the reviewed snapshot.",
)
index_path.write_text(index)
print("Appended authorized remediation, exact source snapshot and five verified dispositions; baseline findings preserved; index updated.")
