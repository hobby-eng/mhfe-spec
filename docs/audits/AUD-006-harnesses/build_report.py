"""Build docs/audits/audit-06-2026-10-09.md and .json from findings.py and the local evidence.

Run from the repository root after run.py: python3 -B docs/audits/AUD-006-harnesses/build_report.py
Home-directory paths in recorded commands are written as /home/user.
"""

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from findings import BASE, FINDINGS, FIXED_BY_HARNESS, OBSERVATIONS  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-006-evidence"
STEM = "audit-06-2026-10-09"
DATE = "2026-10-09"
REVIEWED = [
    "README.md", "docs/DESIGN-NOTES.md", "CHANGELOG.md", "CITATION.cff", "vectors/README.md",
    "vectors/suite3/README.md", "vectors/suite4/README.md", "vectors/profiles/README.md",
    "docs/audits/README.md", "docs/audits/AUD-004-publication.json", "docs/audits/AUD-005-publication.json",
]
CHECKS = [
    ("check-spec-documents", "python3 -B scripts/check-spec.py documents <BIP39 english.rs>", "15 PASS, 0 FAIL"),
    ("check-spec-analysis", "python3 -B scripts/check-spec.py analysis <english.rs> <mhfe zero-12.json>",
     "64 PASS, 0 FAIL"),
    ("aud005-record-validate", "python3 -B docs/audits/AUD-005-harnesses/record.py validate", "passed"),
    ("prettier-check", "npx --no-install prettier --check <eight Markdown files>", "clean"),
    ("sha256sums-suite3", "sha256sum -c SHA256SUMS (vectors/suite3)", "18 OK"),
    ("sha256sums-suite4", "sha256sum -c SHA256SUMS (vectors/suite4)", "11 OK"),
    ("sha256sums-suite2", "sha256sum -c SHA256SUMS (vectors/archive/suite-2)", "10 OK"),
    ("git-diff-check", "git diff --check", "no whitespace errors"),
]
NOT_APPLICABLE = "The specification repository has no application, browser, network or build surface."
LEDGER = [
    ("CHECK-SEC-001", "Threat model and secret ownership", "passed", "Secrets named by every rule; SEC001, SEC003."),
    ("CHECK-SEC-002", "Secret Vault, CSP, sandbox, and transport", "not-applicable", NOT_APPLICABLE),
    ("CHECK-SEC-003", "Network egress and secret guards", "passed", "Normative network ban reviewed; SEC003."),
    ("CHECK-SEC-004", "Randomness, encryption, and authentication", "passed",
     "All formulas, domain strings, verifier and profile vectors recomputed; no defect."),
    ("CHECK-SEC-005", "Secret lifecycle and exceptional paths", "passed", "Sensitive-memory list; SEC003."),
    ("CHECK-SEC-006", "Browser injection, persistence, and sensitive APIs", "not-applicable", NOT_APPLICABLE),
    ("CHECK-SEC-007", "Read-only guarantees and availability bounds", "passed",
     "Setting bounds, memory levels and refusals recomputed."),
    ("CHECK-FUN-001", "BIP39, entropy, and seed interpretation", "passed",
     "Packing, checksums, NFKD and the seed check recomputed for every vector."),
    ("CHECK-FUN-002", "HD derivation and every coin/profile", "not-applicable", "MHFE defines no HD derivation."),
    ("CHECK-FUN-003", "BIP85, BIP38, messages, and Silent Payments", "not-applicable", "Not defined by MHFE."),
    ("CHECK-FUN-004", "Scripts, descriptors, Miniscript, and multisig", "not-applicable", "Not defined by MHFE."),
    ("CHECK-FUN-005", "Transactions, PSBT version context, and commitments", "not-applicable", "Not defined by MHFE."),
    ("CHECK-FUN-006", "Recovery and backup formats", "failed",
     "Recovery, rehearsal and re-encryption rules traced case by case; FUN001-FUN004."),
    ("CHECK-FUN-007", "Discovery, providers, proofs, and accounting", "not-applicable", "Not defined by MHFE."),
    ("CHECK-API-001", "Actual dependency call contracts", "not-applicable", NOT_APPLICABLE),
    ("CHECK-API-002", "Async state, cancellation, and revisions", "not-applicable", NOT_APPLICABLE),
    ("CHECK-API-003", "Public export schema and monetary fidelity", "not-applicable", NOT_APPLICABLE),
    ("CHECK-API-004", "Encoding and import/export interoperability", "passed",
     "Byte layouts of suites 3 and 4 and the three profiles recomputed from the vectors."),
    ("CHECK-BLD-001", "Manifest, flags, and feature composition", "not-applicable", NOT_APPLICABLE),
    ("CHECK-BLD-002", "Matrix depth and runtime sampling", "not-applicable", NOT_APPLICABLE),
    ("CHECK-BLD-003", "Lockfiles, source provenance, and licenses", "passed",
     "Corpus byte identity with the pinned implementation revisions and source hashes; DOC021."),
    ("CHECK-BLD-004", "Canonical WASM and Docker bytes", "not-applicable", NOT_APPLICABLE),
    ("CHECK-BLD-005", "Artifacts, CI, and release workflows", "failed", "Release metadata; BLD001."),
    ("CHECK-UI-001", "Real files and representative viewports", "not-applicable", NOT_APPLICABLE),
    ("CHECK-UI-002", "Navigation, inputs, and state preservation", "not-applicable", NOT_APPLICABLE),
    ("CHECK-UI-003", "Secret visibility, help, QR, and accessibility", "not-applicable", NOT_APPLICABLE),
    ("CHECK-ARC-001", "Ownership, imports, and composition seams", "not-applicable", NOT_APPLICABLE),
    ("CHECK-ARC-002", "Dead code, duplication, and false positives", "passed",
     "Repeated rules across the two documents listed and reduced; DOC004, DOC005, DOC010, DOC019."),
    ("CHECK-ARC-003", "Comments, tests, and production-path fidelity", "passed",
     "Implementation alignment of the new rules compared with the reference implementation; FUN005."),
    ("CHECK-DOC-001", "User-facing capability and safety descriptions", "failed",
     "Both documents read in full; DOC001-DOC016."),
    ("CHECK-DOC-002", "Commands, metadata, links, and legal materials", "passed",
     "Every in-repository link and anchor resolves; citations numbered 1-64 by first mention."),
    ("CHECK-DOC-003", "Audit records and evidence consistency", "failed", "Record chain validates; DOC017, DOC018."),
]
PROCEDURE = [
    "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md",
    "multi-chain-wallet-tools/docs/audits/AUDIT_STANDARD.md",
    "multi-chain-wallet-tools/docs/audits/AUDIT_TEMPLATE.md",
    "multi-chain-wallet-tools/docs/audit-report.schema.json",
    "AGENTS.md",
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def anonymize(text):
    return re.sub(r"/home/[^/\s\"]+", "/home/user", text)


def manifest(paths):
    files = {}
    for path in paths:
        data = (ROOT / path).read_bytes()
        files[path] = {"sha256": sha(data), "sizeBytes": len(data), "lineCount": data.count(b"\n")}
    fingerprint = sha("".join(f"{p}\0{f['sha256']}\n" for p, f in files.items()).encode())
    return files, fingerprint


def baseline_manifest():
    lines = (EVIDENCE / "source-manifest.sha256").read_text().splitlines()
    hashes = {name: digest for digest, name in (line.split("  ", 1) for line in lines)}
    return {p: hashes[p] for p in REVIEWED if p in hashes}


def check_records():
    records = []
    for name, shown, counts in CHECKS:
        meta = json.loads((EVIDENCE / f"{name}.command.json").read_text())
        records.append({
            "name": name,
            "command": anonymize(shown),
            "outcome": "passed" if meta["exitCode"] == 0 else "failed",
            "count": counts,
            "evidence": f"Local only: AUD-006-evidence/{name}.log (SHA-256 {meta['logSha256']}), "
                        f"run {meta['startedAt']}",
        })
    broken = json.loads((EVIDENCE / "link-check.json").read_text())["broken"]
    records.append({
        "name": "link-check",
        "command": "run.py link check: every relative Markdown link and #anchor outside the archive and drafts",
        "outcome": "passed" if not broken else "failed",
        "count": f"{len(broken)} broken",
        "evidence": "Local only: AUD-006-evidence/link-check.json. " + FIXED_BY_HARNESS,
    })
    return records


def build():
    files, fingerprint = manifest(REVIEWED)
    procedure = {}
    workspace = ROOT.parent
    for path in PROCEDURE:
        procedure[path] = sha((workspace / path).read_bytes())
    findings = FINDINGS
    report = {
        "schemaVersion": 1,
        "auditId": "AUD-006",
        "auditNumber": 6,
        "date": DATE,
        "title": "Release audit of the MHFE specification, its supplement, vectors notes and records",
        "reviewer": {"name": "Claude (coordinator) with five document reviewers and one fix verifier",
                     "model": "claude-opus-5-5", "reasoningEffort": None},
        "reviewerPhases": [
            {"name": "R1 normative correctness", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "README formulas, vectors, profiles, recovery and re-encryption rules"},
            {"name": "R2 specification and supplement", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "Consistency of README.md and docs/DESIGN-NOTES.md"},
            {"name": "R3 supplement arithmetic", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "Every quantitative claim and proof step of the supplement"},
            {"name": "R4 narrative and repetition", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "Order, repetition, terms, citations and the CHANGELOG"},
            {"name": "R5 vectors, records and release", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "Corpus notes, audit records, release metadata and implementation alignment"},
            {"name": "Coordinator and verifier", "model": "claude-opus-5-5", "reasoningEffort": None,
             "scope": "Challenge of findings, authorized remediation and its independent verification"},
        ],
        "snapshot": {
            "commit": BASE,
            "commitComplete": False,
            "branch": "main",
            "workingTree": "Uncommitted edits to the specification, supplement, CHANGELOG, corpus notes and "
                           "publication records on top of the commit; untracked AGENTS.md and docs/drafts/.",
            "preExistingChanges": "The reviewed baseline is the uncommitted tree; its file hashes are below.",
            "sourceFiles": {p: {"sha256": h} for p, h in baseline_manifest().items()},
            "fingerprintMethod": "SHA-256 of each file of the local baseline manifest.",
        },
        "scope": {
            "included": REVIEWED + ["vectors/suite3/*.json", "vectors/suite4/*.json", "SHA256SUMS files"],
            "excluded": ["docs/archive/ (historical)", "docs/drafts/ (untracked)", "the reference implementation, "
                         "except where its working tree was compared with the new rules"],
            "executionClass": "Document review with recomputation of formulas and vectors; no full-size Argon2id",
            "baselineOnly": False,
            "remediationAddendum": "Owner-authorized correction of the findings on 2026-10-09.",
        },
        "procedureHashes": procedure,
        "checks": check_records(),
        "coverageLedger": [
            {"checkId": c, "category": c.split("-")[1], "logicalGroup": g, "scope": "Specification repository",
             "method": "Document review and recomputation", "outcome": o, "evidence": e, "snapshot": BASE}
            for c, g, o, e in LEDGER
        ],
        "findings": findings,
        "observations": OBSERVATIONS,
        "remediation": [
            {"id": f["id"], "status": f["status"], "fixCommit": None, "verificationCommit": None,
             "evidence": "Uncommitted working tree bound by the remediated file hashes below."
             if f["status"] in ("fixed", "verified") else "Not fixed in this audit."}
            for f in findings + OBSERVATIONS
        ],
        "recommendations": [
            {"title": "Release as 0.6.0 after the corpus import",
             "detail": "Import the stated-24-words record (FUN001), then set version 0.6.0 (BLD001) and name the "
                       "implementation release (DOC016)."},
        ],
        "limitations": [
            "No full-size Argon2id was run; transcripts were recomputed from their recorded Argon2id outputs.",
            "The reviewers belong to one model family; this is not an independent cryptographic review.",
            "The run logs of the baseline were overwritten by the rerun after remediation; the baseline result "
            "(all checks passed except the link-check false positive) is recorded here.",
            "The verifier confirmed every fix and reported six follow-up wording gaps in the new text (three "
            "outcomes of the rehearsal check, suite 3 scope of its length question, the derived rehearsal "
            "reference, two unlinked references, the suite in the recovery plan, and four CHANGELOG gaps). "
            "They were corrected afterwards and checked by the coordinator only.",
        ],
        "remediationAddendum": {
            "date": DATE,
            "authorization": "Owner's instruction of 2026-10-09 to fix all findings.",
            "sourceFiles": files,
            "sourceFingerprint": fingerprint,
        },
        "assessment": "",
    }
    open_blocking = [f["id"] for f in findings if f["releaseBlocking"] and f["status"] == "open"]
    report["assessment"] = (
        "No formula, bound, vector or proof step is wrong. The baseline had four functional, three security, "
        "one build and eighteen documentation findings, all in the application rules and their wording. "
        "Release blockers remaining: " + (", ".join(open_blocking) or "none") + "."
    )
    return report


def md(report):
    out = [f"# {report['auditId']} — {report['title']}", "", "## Record metadata", "",
           f"- **Audit number:** {report['auditNumber']}.",
           f"- **Completed (UTC):** {report['date']}.",
           f"- **Reviewer:** {report['reviewer']['name']}.",
           f"- **Model:** {report['reviewer']['model']}.",
           "- **Reasoning effort:** unknown.",
           "- **Reviewer phases:** " + "; ".join(f"{p['name']}: {p['scope']}" for p in report["reviewerPhases"]) + ".",
           f"- **Reviewed commit:** `{report['snapshot']['commit']}` plus the uncommitted tree.",
           f"- **Working tree:** {report['snapshot']['workingTree']}",
           "- **Artifacts:** not applicable; no release artifact was built.",
           "", "## Finding register", "",
           "| Finding / record ID | Category | Kind | Severity | Recorded status | Title |",
           "| --- | --- | --- | --- | --- | --- |"]
    for f in report["findings"] + report["observations"]:
        out.append(f"| {f['id']} | {f['category']} | {f['kind']} | {f['severity']} | {f['status']} | {f['title']} |")
    out += ["", "## Review evidence", "", "### Scope and methodology", "",
            "Five reviewers with distinct scopes read the specification and the supplement in full, recomputed "
            "every formula, bound and vector they could without full-size Argon2id, and compared the new rules "
            "with the reference implementation's working tree. The coordinator challenged each finding against "
            "the text before accepting it and merged duplicates. A separate verifier checked every fix.", "",
            "Included: " + ", ".join(f"`{p}`" for p in report["scope"]["included"]) + ".", "",
            "Excluded: " + "; ".join(report["scope"]["excluded"]) + ".", "",
            "Procedure files (SHA-256):", ""]
    out += [f"- `{p}`: `{h}`" for p, h in report["procedureHashes"].items()]
    out += ["", "### Coverage ledger", "",
            "| Check ID | Category / logical group | Tool / build scope | Method | Outcome | Evidence / gap reason |",
            "| --- | --- | --- | --- | --- | --- |"]
    for c in report["coverageLedger"]:
        out.append(f"| {c['checkId']} | {c['category']} / {c['logicalGroup']} | {c['scope']} | {c['method']} | "
                   f"{c['outcome']} | {c['evidence']} |")
    out += ["", "### Checks", "", "| Check / command | Outcome | Counts / environment | Evidence |",
            "| --- | --- | --- | --- |"]
    for c in report["checks"]:
        out.append(f"| `{c['command']}` | {c['outcome']} | {c['count']} | {c['evidence']} |")
    out += ["", "### Findings", ""]
    for f in report["findings"] + report["observations"]:
        out += [f"#### {f['id']} — {f['severity'].capitalize()} — {f['title']}", "",
                f"- **Category:** {f['category']}.", f"- **Kind:** {f['kind']}.",
                f"- **Severity:** {f['severity']}.", f"- **Status:** {f['status']}.",
                f"- **Release blocking:** {str(f['releaseBlocking']).lower()}; {f['releaseBlockingReason']}",
                "- **Affected files:** " + "; ".join(f["affected"]) + ".",
                f"- **Reproduction:** {f['reproduction']}", f"- **Expected behavior:** {f['expected']}",
                f"- **Observed behavior:** {f['observed']}", f"- **Impact:** {f['impact']}",
                f"- **Evidence:** {' '.join(f['evidence'])}", f"- **Recommended fix:** {f['recommendedFix']}",
                f"- **Required verification:** {f['requiredVerification']}", ""]
    out += ["### Remediation and follow-up", "",
            "| Finding ID | Status | Fix commit | Verification commit | Evidence |", "| --- | --- | --- | --- | --- |"]
    for r in report["remediation"]:
        out.append(f"| {r['id']} | {r['status']} | Not committed | Not committed | {r['evidence']} |")
    out += ["", "Remediated files (SHA-256 of the working tree after the fixes):", ""]
    out += [f"- `{p}`: `{v['sha256']}`" for p, v in report["remediationAddendum"]["sourceFiles"].items()]
    out += ["", f"Fingerprint: `{report['remediationAddendum']['sourceFingerprint']}`.", "",
            "### Informational observations and recommendations", ""]
    out += [f"- **{r['title']}.** {r['detail']}" for r in report["recommendations"]]
    out += ["", "### Assessment and limitations", "", report["assessment"], ""]
    out += [f"- {x}" for x in report["limitations"]]
    return anonymize("\n".join(out) + "\n")


def main():
    report = build()
    text = anonymize(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    (ROOT / f"docs/audits/{STEM}.json").write_text(text)
    (ROOT / f"docs/audits/{STEM}.md").write_text(md(report))
    print(f"wrote docs/audits/{STEM}.md and .json")


main()
