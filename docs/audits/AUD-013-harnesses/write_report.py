#!/usr/bin/env python3
"""Assemble the comparison and later-state verification only from completed matching evidence."""

import ast
import datetime
import hashlib
import json
from pathlib import Path
import re

import jsonschema


HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
WORKSPACE = HERE.parents[3]
EVIDENCE = AUDITS / "AUD-013-evidence"
NOTES = WORKSPACE / "tmp/proof-comparison-audit-2026-11-12"


def read(path):
    """Load retained JSON evidence, without constructing missing results."""
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def redact(text):
    return re.sub(r'/home/[^/\s"<>]+/', '/home/user/', text)


def verify_inputs():
    """Bind new EC checks, unchanged Lean inputs and historical comparisons to their bytes."""
    current = read(EVIDENCE / "current-easycrypt-snapshot.json")
    lean = read(AUDITS / "AUD-012-evidence/snapshot.json")
    old = read(AUDITS / "AUD-011-evidence/snapshot.json")
    semantic = read(EVIDENCE / "semantic-source-inputs.json")
    inputs = {item["path"]: item["sha256"] for item in current["files"] + lean["files"]}
    inputs.update(semantic)
    inputs.update({
        "tmp/easycrypt-mhfe-2026-11-09/LEAN-COMPARISON.md": "db3c45d66d008cbb5d9e1ca4ca9a20d3138466fa630a59a657800e7e7aed3502",
        "tmp/lean-review-2026-11-11/PORT-v4.35.md": "98f458f581d1eba79871eb18f0672765d941fc7ce7aed785d08b7ca354bfc526",
    })
    for item in read(EVIDENCE / "toolchain-identities.json")["toolchains"]:
        inputs[str(Path(item["binary"]).relative_to(WORKSPACE))] = item["binarySha256"]
        inputs[str(Path(item["why3Config"]).relative_to(WORKSPACE))] = item["configSha256"]
    for name, digest in inputs.items():
        assert sha(WORKSPACE / name) == digest, name
    old_hash = {item["path"]: item["sha256"] for item in old["files"]}
    recovery = []
    for filename, intervals in {
        "Selection.ec": [(763, 803), (939, 1040)],
        "Theorem5.ec": [(1280, 1334), (1374, 1427)],
    }.items():
        name = "tmp/easycrypt-mhfe-2026-11-09/src/" + filename
        lines = (WORKSPACE / name).read_bytes().splitlines(keepends=True)
        recovered = b"".join(line for index, line in enumerate(lines, 1)
                             if not any(first <= index <= last for first, last in intervals))
        digest = hashlib.sha256(recovered).hexdigest()
        assert digest == old_hash[name], (name, digest)
        recovery.append({"file": filename, "removedInclusiveRanges": intervals,
                         "recoveredAud011Sha256": digest})
    package = WORKSPACE / "tmp/easycrypt-mhfe-2026-11-09"
    assert not list((package / "src").glob("*.eco"))
    for source in (package / "src").glob("*.ec"):
        assert not re.search(r"\b(admit|admitted)\b|Proofs:weak", source.read_text()), source.name
    for line in (package / "SHA256SUMS").read_text().splitlines():
        digest, filename = line.split(maxsplit=1)
        assert sha(package / "src" / filename.lstrip("*")) == digest, filename
    manifest = {"capturedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "files": inputs, "additionsOnlyRecovery": recovery}
    (EVIDENCE / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return current, lean, manifest


def applicability():
    """Preserve every canonical CHECK ID while adapting the procedure to proof comparison."""
    guide = (AUDITS / "AUD-011-evidence/procedure/FULL_AUDIT_GUIDE.md").read_text()
    tasks = re.findall(r"^### (CHECK-[A-Z]+-\d+) — (.+)$", guide, re.M)
    adapted = {
        "CHECK-SEC-001": "Compared secret/view independence and non-comparable real-record kernels; no runtime memory claim.",
        "CHECK-SEC-004": "Compared ideal-function models, event predicates and numerical constants; concrete primitive security excluded.",
        "CHECK-SEC-007": "Compared query budgets, termination and cap failure; resource records cover the admitted checks only.",
        "CHECK-FUN-001": "Compared entropy/seed/checksum widths and abstract phrase bridges; no concrete parser or normalization verification.",
        "CHECK-API-001": "Traced batch/selection/query interfaces, actual final games and upstream finite-answer migration.",
        "CHECK-BLD-001": "Baseline proof checks retained separately; four current EC modules checked on two toolchains; no new full-suite total claimed.",
        "CHECK-BLD-003": "Input/tool/source hashes recorded; dependency pins reused from AUD-012; clean installation/license decisions not run.",
        "CHECK-BLD-005": "Current checker failure/cache self-tests verified; original adapter failure retained; remote CI/release not run.",
        "CHECK-ARC-001": "Reviewed actual definition/context changes and complete current/historical chapter sets, beyond raw headers.",
        "CHECK-ARC-002": "Challenged claimed absence of batch/selection/no-wallet coverage and intentional K5 helper removals.",
        "CHECK-ARC-003": "Checked parser limitations, source-preserving additions and actual verification paths; no source gate weakened.",
        "CHECK-DOC-001": "Reviewed with DOC001: full comparison, hypotheses, exactness, model restrictions and publication scope.",
        "CHECK-DOC-002": "Reviewed with DOC002: tool counts, patch/path freshness, current check commands and provenance.",
        "CHECK-DOC-003": "Paired schema/privacy/input/log evidence validation and final independent review recorded separately.",
    }
    assert len(tasks) == 32
    result = []
    for identifier, title in tasks:
        result.append({"id": identifier, "title": title,
                       "status": "failed" if identifier in {"CHECK-DOC-001", "CHECK-DOC-002"}
                       else "passed" if identifier in adapted else "not-applicable",
                       "evidence": adapted.get(identifier, "The named browser/provider/transaction/export/runtime/WASM operation is absent from this proof-comparison target; excluded, not tested as secure.")})
    return result


def main():
    current, lean, snapshot = verify_inputs()
    proof_runs = {}
    for directory, label in [("current-proofs", "release r2026.10"), ("current-main-proofs", "main ce19cb6")]:
        records = read(EVIDENCE / directory / "compile-summary.json")
        assert len(records) == 4 and {item["name"] for item in records} == {"Selection", "Theorem5", "W5W6", "W7"}
        assert all(item["exitCode"] == 0 for item in records)
        proof_runs[label] = records
    controls = read(EVIDENCE / "current-checker-selftest-corrected.command.json")
    assert controls["exitCode"] == 0
    control_log = (EVIDENCE / "current-checker-selftest-corrected.log").read_text()
    assert len(re.findall(r"^ok      ", control_log, re.M)) == 4
    main_controls = read(EVIDENCE / "current-checker-selftest-main.command.json")
    assert main_controls["exitCode"] == 0
    assert len(re.findall(r"^ok      ", (EVIDENCE / "current-checker-selftest-main.log").read_text(), re.M)) == 4
    port = EVIDENCE / "port-tools-final"
    counts = ast.literal_eval((port / "diff.log").read_text())
    assert counts == {"same": 2582, "changed": 13, "removed": 3, "added": 30}
    probes = read(port / "parser-probes.json")
    assert len(probes) == 12
    assert next(row for row in probes if row["case"] == "named_argument_regression")["comparison"]["changed"] == 1
    findings = read(HERE / "findings.json")
    baselines = {}
    for number in ["011", "012"]:
        validation = read(AUDITS / f"AUD-{number}-evidence/report-validation.json")
        base = AUDITS / f"AUD-{number}-2026-11-12.md"
        assert sha(base) == validation["reportSha256"]
        assert sha(base.with_suffix(".json")) == validation["jsonSha256"]
        baselines[number] = {"markdownSha256": sha(base), "jsonSha256": sha(base.with_suffix(".json"))}
    now = datetime.datetime.now(datetime.timezone.utc)
    commands = [read(path) for path in sorted(EVIDENCE.rglob("*.command.json"))]
    procedures = read(AUDITS / "AUD-011-evidence/procedure-hashes.json")
    prior_ids = ["AUD-011-BLD001", "AUD-011-BLD002", "AUD-011-DOC001", "AUD-011-DOC002"]
    data = {
        "schemaVersion": 1, "auditId": "AUD-013", "auditNumber": 13, "date": now.date().isoformat(),
        "completedUtc": now.isoformat(), "title": "Independent EasyCrypt/Lean comparison and current EasyCrypt follow-up",
        "reviewer": {"name": "Codex coordinator with three distinct read-only specialist scopes", "model": None, "reasoningEffort": None},
        "snapshot": {"commit": "98620cce3d75a011e751cb2d3c1c315b7c23669d", "commitComplete": True,
                     "workingTree": "Specification/proof sources unchanged by this audit. Later EC changes by a separate session checked at current artifact hashes.",
                     "inputManifest": snapshot},
        "scope": {"included": ["Full existing comparison and port account", "Current versus historical models, statements, hypotheses and core bounds", "Port textual-tool reproduction and context/definition review", "Later EC additions, dependent proofs and verifier remediation"],
                  "excluded": ["Rust/browser implementation audit", "Formal cross-language/cross-toolchain equivalence proof", "Whole upstream kernel/solver/library implementation review", "Clean installation/cache download/remote CI/release" ]},
        "procedureHashes": procedures,
        "checks": {"baselines": baselines, "targetedCurrentEasyCrypt": proof_runs,
                   "toolchains": read(EVIDENCE / "toolchain-identities.json"),
                   "checkerSelftests": {"release": controls, "main": main_controls},
                   "headerCounts": counts, "parserProbes": probes,
                   "gnuChapterDiff": read(port / "gnu-diff-stats.json"),
                   "applicability": applicability(), "commands": commands,
                   "currentInputsUnchanged": True, "baselineLeanInputs": len(lean["files"])},
        "findings": findings, "observations": [],
        "remediation": [{"id": item["id"], "status": "open", "fixCommit": None, "verificationCommit": None,
                         "evidence": "Comparison/port text not edited by this read-only audit."} for item in findings] +
                       [{"id": identifier, "status": "verified", "fixCommit": None, "verificationCommit": None,
                         "evidence": "Later EC artifact hashes, current README scope/provenance, checked additions and real verifier self-tests; baseline historical record preserved."} for identifier in prior_ids],
        "limitations": ["No literal unrestricted equivalence; final genuine-record kernels incomparable", "EC finite passphrases and lossless programs; general adaptive expectation not a final source-game endpoint", "Lean finite W5-W7, narrower record kernel and missing ancillary assemblies", "Header tool is heuristic textual comparison, not elaborated/semantic identity", "Current EC proof checks targeted, not a new full18 replay; original baselines remain separate", "No concrete primitive/runtime/clean-machine certification"],
        "verdict": "CORE_BOUNDS_CONFIRMED_WITH_SCOPE_AND_PUBLICATION_CORRECTIONS",
    }
    text = (HERE / "REPORT_TEMPLATE.md").read_text().replace("{{COMPLETED_UTC}}", data["completedUtc"])
    text += "\n## Executed evidence and artifact identity\n\n| Toolchain | Module | Exit | Seconds | Log SHA-256 |\n| --- | --- | --- | --- | --- |\n"
    for label, records in proof_runs.items():
        for item in records:
            text += f"| {label} | {item['name']} | {item['exitCode']} | {item['elapsedSeconds']} | `{item['logSha256']}` |\n"
    text += "\nRelease and main checker self-tests each produced expected case statuses **1, 2, 1, 0**, with overall exit0. The original adapter attempt exit1 is retained and explained above.\n\n"
    for number, digests in baselines.items():
        text += f"- AUD-{number} Markdown: `{digests['markdownSha256']}`; JSON: `{digests['jsonSha256']}`.\n"
    text += "\n| Current EC input | Lines | SHA-256 |\n| --- | --- | --- |\n"
    for item in current["files"]:
        text += f"| `{item['path'].split('easycrypt-mhfe-2026-11-09/', 1)[-1]}` | {item['lines']} | `{item['sha256']}` |\n"
    text += "\nExact argv, cwd, UTC times, statuses and log hashes are in the paired JSON. Raw logs, complete input manifests, generated snippets/TSVs and resources are retained only in ignored **machine-local** AUD-013-evidence; they are not public downloadable evidence.\n\n"
    text += "## Confirmed findings\n\n"
    for item in findings:
        text += f"### {item['id']} — {item['severity'].capitalize()} — {item['title']}\n\n"
        for key in ["affected", "reproduction", "expected", "observed", "impact", "evidence", "recommendedFix", "requiredVerification"]:
            text += f"- **{key}:** {item[key]}\n"
        text += "- **Rules:** " + ", ".join(item["rules"]) + ".\n\n"
    text += "## Detailed independent comparison and source reviews\n\nThe static new-EC note predates execution; its conditional acceptance language is superseded only by the matching completed checks above. Reviewer notes do not claim to have run the coordinator's proof checks.\n\n"
    for filename in ["denial-g.md", "model-w.md", "port-tools.md", "new-easycrypt.md"]:
        note = (NOTES / filename).read_text()
        text += re.sub(r"^(#{1,4}) ", r"##\1 ", note, flags=re.M) + "\n\n"
    text += "## Procedure and explicit applicability\n\n"
    for name, digest in procedures.items():
        text += f"- `{name}`: `{digest}`.\n"
    text += "\n| Canonical check | Outcome | Comparison-scope evidence / exclusion |\n| --- | --- | --- |\n"
    for item in data["checks"]["applicability"]:
        text += f"| {item['id']} — {item['title']} | {item['status']} | {item['evidence']} |\n"
    text += "\nNot run: clean-machine installation, Mathlib cache download, whole-library/kernel/solver implementation audit, independent external Lean checker, per-solver EC isolation, Rust/browser/vector/release suites, remote CI and publication. Future repository/license/layout choices do not become executed checks. No remaining scope qualification is silently called a fixed proof.\n"
    published = redact(json.dumps(data, indent=2)) + "\n"
    text = redact(text)
    jsonschema.Draft202012Validator(read(AUDITS / "AUD-011-evidence/procedure/audit-report.schema.json")).validate(json.loads(published))
    assert not re.search(r"/home/(?!user/)[^/]+/|[А-Яа-яЁё]", text + published)
    base = AUDITS / f"AUD-013-{data['date']}"
    base.with_suffix(".md").write_text(text)
    base.with_suffix(".json").write_text(published)
    print(json.dumps({"report": base.name, "bytes": len(text.encode()), "findings": len(findings)}))


if __name__ == "__main__":
    main()
