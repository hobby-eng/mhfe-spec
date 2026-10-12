"""Build the workspace audit companion from the completed source-review evidence."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import jsonschema


ROOT = Path(__file__).resolve().parents[3]
AUDIT = "AUD-008"
EVIDENCE = ROOT / "docs/audits/AUD-008-evidence"
STEM = ROOT / "docs/audits/AUD-008-2026-10-12"
REVIEWED_CHECKS = {
    "CHECK-SEC-001", "CHECK-SEC-004", "CHECK-SEC-005", "CHECK-SEC-007",
    "CHECK-FUN-001", "CHECK-FUN-006", "CHECK-API-004", "CHECK-BLD-003",
    "CHECK-ARC-001", "CHECK-ARC-002", "CHECK-ARC-003",
    "CHECK-DOC-001", "CHECK-DOC-002", "CHECK-DOC-003",
}


# Any home directory other than the neutral /home/user is replaced, so no account name is published.
PRIVATE_HOME = re.compile(r"/home/(?!user\b)[^/\s\"]+")


def anonymize(value):
    return json.loads(PRIVATE_HOME.sub("/home/user", json.dumps(value)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scan_directory", type=Path)
    args = parser.parse_args()
    snapshot = json.loads((EVIDENCE / "snapshot.json").read_text())
    architecture = json.loads((args.scan_directory / "artifacts/architecture-review.json").read_text())
    baseline = json.loads((args.scan_directory / "artifacts/baseline-review.json").read_text())
    vectors = json.loads((args.scan_directory / "artifacts/vector-review.json").read_text())
    for review in (baseline["initial"], baseline["ancillary"], vectors):
        if review.get("findings"):
            raise AssertionError("Report builder must be updated to retain confirmed findings")
    procedure = ROOT.parent / "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md"
    checks = []
    for check, title in re.findall(r"^### (CHECK-[A-Z]+-\d+) — (.+)$", procedure.read_text(), re.M):
        applicable = check in REVIEWED_CHECKS
        checks.append({
            "checkId": check, "title": title,
            "outcome": "passed" if applicable else "not-applicable",
            "method": "Static specification/data review and scoped checks" if applicable else "Applicability assessment",
            "evidence": "Current normative text, reviewer dispositions and command records; this does not claim implementation execution."
            if applicable else "This specification repository has no executable wallet/browser/provider/build deployment for this check; implementation verification is a separate scan.",
        })
    if len(checks) != 32:
        raise AssertionError("Shared procedure check inventory changed")
    commands = [json.loads(path.read_text()) | {"record": path.name}
                for path in sorted(EVIDENCE.glob("*.command.json"))]
    limitations = [
        "Standard security/design scan with targeted verification, not a full release audit or independent cryptographic certification.",
        "No new full-cost Argon2 replay, GPU/ASIC benchmark, side-channel experiment, PRP/SPRP proof or optimal attack-cost proof was performed.",
        "Historical audit reports were checked for schema and paired IDs, not for the truth of every historical finding, source hash or claimed test result.",
        "External citations, release publication and remote vulnerability-reporting settings were not checked; source reviewers stayed offline.",
        "Recorded-key replay verifies packing, salt/mask messages, Feistel equations and encodings, but cannot establish the recorded Argon2 outputs.",
        "The optional-profile probes use Python Unicode 16 on stable public inputs; the vector investigator separately checks the frozen Unicode-17 cases with the pinned Node runtime.",
    ]
    recommendations = [
        "Obtain independent cryptographic analysis of state-derived salts, reduced-call filters, multi-target attacks and the narrower Suite 4 state; no exploit was established here.",
        "Treat deniability as conditional on the stated synthetic experiment; real ledger correlations, source conditioning, related containers and side channels need separate analysis.",
        "Prefer an independently held receiving address when actual wallet identity matters; the 16-bit source predicate and 32-bit fingerprint have stated probabilistic limits.",
        "Keep repair cards and password-check material private as specified; their disclosed entropy losses are deliberate tradeoffs, not new findings.",
        "Verify the current mhfe implementation against current recovery/re-encryption rules; the specification already documents the v0.6.0 ambiguous-rehearsal difference.",
    ]
    report = anonymize({
        "schemaVersion": 1, "auditId": AUDIT, "auditNumber": 8, "date": "2026-10-12",
        "title": "Codex Security specification and protocol-design scan",
        "completedAt": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "reviewer": {"name": "Codex Security coordinator with independent baseline, architecture and vector reviewers",
                     "model": "gpt-6.1-sol", "reasoningEffort": "ultra"},
        "snapshot": {"commit": snapshot["head"], "commitComplete": False,
                     "workingTree": snapshot["preExistingStatus"], "sourceFingerprint": snapshot["fingerprint"]},
        "scope": {"repository": "mhfe_spec", "mode": "standard-security-scan",
                  "sourceFilesAtStart": snapshot["files"], "threatModel": architecture["threatModel"],
                  "runtimeStatus": "Targeted Python/data probes only; no product runtime exists here."},
        "procedureHashes": json.loads((EVIDENCE / "procedure-hashes.json").read_text()),
        "checks": checks, "executedCommands": commands, "findings": [], "observations": [],
        "remediation": [], "informationalRecommendations": recommendations, "limitations": limitations,
        "harnessCorrections": [
            "Initial AUD-008 transcript wrapper expected schema v1; actual public schema is v2. The failed log is retained, the wrapper was corrected, and the corrected run passed.",
            "An initial ad hoc historical-schema attempt included a publication-provenance JSON, which is not an audit envelope, and failed with: 'schemaVersion' is a required property. The corrected history.py targets seven audit-report companions, all passing. No production defect was inferred.",
        ],
        "localEvidence": "AUD-008-evidence/ is ignored local evidence; original command bytes are not published or silently anonymized.",
        "pluginArtifacts": "The separately generated Codex Security report is the canonical plugin result; this pair follows the workspace audit envelope.",
    })
    schema = json.loads((ROOT.parent / "multi-chain-wallet-tools/docs/audit-report.schema.json").read_text())
    jsonschema.validate(report, schema)
    STEM.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    lines = [
        "# AUD-008 — Codex Security specification and protocol-design scan", "",
        "## Record metadata", "",
        "- **Audit number:** 8.", "- **Completed (UTC):** " + report["completedAt"] + ".",
        "- **Reviewer:** Codex Security coordinator with independent baseline, architecture and vector reviewers.",
        "- **Model:** gpt-6.1-sol.", "- **Reasoning effort:** ultra for substantive review; earlier registration performed no source review.",
        "- **Reviewed commit:** `" + snapshot["head"] + "`.",
        "- **Working tree:** Pre-existing untracked `AGENTS.md` and `docs/drafts/` were included and preserved.",
        "- **Source fingerprint:** `" + snapshot["fingerprint"] + "` (116 initial files; audit-owned additions excluded).", "",
        "## Finding register", "", "No confirmed reportable security vulnerability was identified.", "",
        "## Review evidence", "", "### Scope and methodology", "",
        "This is a Standard Codex Security scan of the current specification, subordinate design notes, public corpora, archive boundaries and local scripts. Independent reviewers checked the protocol and its stated attack model. All 32 shared procedure tasks have an applicability disposition; implementation, browser and release execution is a separate stage. Historical checks were not counted as newly run checks.", "",
        "### Coverage ledger", "",
        "| Check ID | Area | Method | Outcome | Evidence / gap |",
        "| --- | --- | --- | --- | --- |",
    ]
    for item in checks:
        lines.append("| " + " | ".join([item["checkId"], item["title"], item["method"], item["outcome"], item["evidence"]]) + " |")
    lines += ["", "### Checks", "", "| Command record (local evidence) | Exit | Output SHA-256 |",
              "| --- | ---: | --- |"]
    for command in report["executedCommands"]:
        lines.append(f"| `{command['record']}`: `{' '.join(command['command'])}` | {command['exitCode']} | `{command['logSha256']}` |")
    lines += ["", "Current results: document checks **15 PASS / 0 FAIL**; analytical checks **64 PASS / 0 FAIL**; Suite 3 **17** and archived Suite 2 **9** recorded-key transcripts; Suite 4 **10 transcripts / 240 round records**, **67** admission/domain cases and two deliberately corrupted fields refused; **16 repair cards**, three bounded repair examples, four password vectors and **24 erased positions**; seven historical report envelopes. These overlapping counts are not added into one test total.",
              "", "### Findings", "", "None. No remediation was applied.", "",
              "### Informational observations and recommendations", ""]
    lines += ["- " + value for value in recommendations]
    lines += ["", "### Assessment and limitations", ""] + ["- " + value for value in limitations]
    lines += ["", "### Harness corrections", ""] + ["- " + value for value in report["harnessCorrections"]]
    lines += ["", "### Procedure hashes", "", "| Procedure | SHA-256 |", "| --- | --- |"]
    lines += [f"| `{name}` | `{digest}` |" for name, digest in report["procedureHashes"].items()]
    lines += ["", "Evidence is local in the ignored `AUD-008-evidence/` folder. Reusable scripts are in `AUD-008-harnesses/`. The source was not modified to make a check pass, and no commit, push or release was performed.", ""]
    markdown = "\n".join(lines)
    if PRIVATE_HOME.search(markdown) or PRIVATE_HOME.search(json.dumps(report)):
        raise AssertionError("published report contains a private home path")
    STEM.with_suffix(".md").write_text(markdown)
    print(json.dumps({"auditId": AUDIT, "findings": 0, "procedureChecks": len(checks), "outcome": "written"}))


if __name__ == "__main__":
    main()
