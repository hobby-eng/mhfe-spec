#!/usr/bin/env python3
"""Assemble the independent Lean proof-audit report from completed, retained evidence."""

import datetime
import hashlib
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
WORKSPACE = HERE.parents[3]
EVIDENCE = AUDITS / "AUD-012-evidence"
NOTES = WORKSPACE / "tmp/lean-audit-2026-11-12"


def load(name):
    """Load one completed record rather than inferring a pending result."""
    return json.loads((EVIDENCE / name).read_text())


def anonymize(text):
    """Redact owner home paths in published text only."""
    return re.sub(r'/home/[^/\s"<>]+/', '/home/user/', text)


def main():
    """Require all source, kernel and control evidence before writing acceptance conclusions."""
    snapshot = load("snapshot.json")
    source, kernel, probes = (load(name + "-summary.json") for name in ["compile", "kernel", "probe"])
    assert len(source) == len(kernel) == 40
    assert all(item["exitCode"] == 0 for item in source + kernel)
    expected = {"MhfeLean"} | {
        "MhfeLean.Chapters." + Path(item["path"]).stem
        for item in snapshot["files"]
        if "/Chapters/" in item["path"] and item["path"].endswith(".lean")
    }
    assert len(expected) == 40
    assert {item["module"] for item in source} == {item["module"] for item in kernel} == expected
    assert load("lake-build.command.json")["exitCode"] == 0
    assert len(probes) == 3 and all(item["exitCode"] == 1 and item["gateRejected"]
                                   and item["markerFound"] for item in probes)
    inventory = load("checkpoint-inventory.json")
    assert len(inventory["roots"]) == 6036 and inventory["theorems"] == 3888
    assert set(inventory["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    assert not inventory["local_axioms"]
    for item in snapshot["files"]:
        assert hashlib.sha256((WORKSPACE / item["path"]).read_bytes()).hexdigest() == item["sha256"]
    for path, digest in {
        "README.md": "debbc9169b1a792f4f46f98de6d328672643183f07c430a12629d5e90a49f485",
        "docs/DESIGN-NOTES.md": "50affa7d36c43e10af0cff1e6aabaeb304cf3838e081bcb1317575bc94026346",
    }.items():
        assert hashlib.sha256((AUDITS.parents[1] / path).read_bytes()).hexdigest() == digest
    findings = json.loads((HERE / "findings.json").read_text())
    procedures = json.loads((AUDITS / "AUD-011-evidence/procedure-hashes.json").read_text())
    command_records = [json.loads(path.read_text()) for path in sorted(EVIDENCE.glob("*.command.json"))]
    now = datetime.datetime.now(datetime.timezone.utc)
    data = {
        "schemaVersion": 1, "auditId": "AUD-012", "auditNumber": 12, "date": now.date().isoformat(),
        "completedUtc": now.isoformat(), "title": "Lean proof validity, exact specification correspondence and publication readiness",
        "reviewer": {"name": "Codex coordinator with three read-only specialist scopes and independent skeptical follow-ups", "model": None, "reasoningEffort": None},
        "snapshot": {"commit": snapshot["specCommit"], "commitComplete": True,
                     "workingTree": "Specification proof texts unchanged. Only audit records/harnesses/index added. Reviewed Lean artifact is outside the specification Git tree.",
                     "sourceFingerprint": snapshot["sourceFingerprint"]},
        "scope": {"included": ["All 39 current Lean chapters and package entry", "Deniability and appendix A correspondence, models, statements and critical proof paths", "Toolchain/dependency identity, axiom gate, fresh elaboration and kernel replay", "Public proof-check instructions and provenance"],
                  "excluded": ["Rust/browser implementation audit", "Concrete primitive security/side channels/costs", "Whole Lean/kernel/compiler and dependency-internal audit", "Clean installation/cache download/full release checks", "Independent final comparison, next separate report"]},
        "procedureHashes": procedures,
        "checks": {"compile": source, "kernel": kernel, "probes": probes,
                   "axiomInventory": {"roots": len(inventory["roots"]), "theorems": inventory["theorems"], "axioms": inventory["axioms"], "localAxioms": []},
                   "static": load("static.json"), "dependencies": load("dependencies.json"),
                   "freshArtifacts": load("fresh-artifacts.json"),
                   "kernelBatch": load("kernel-batch-manifest.json"),
                   "toolchainBinaries": load("toolchain-binaries.json"),
                   "commands": command_records, "sourceUnchanged": True},
        "findings": findings, "observations": [],
        "remediation": [{"id": item["id"], "status": "open", "fixCommit": None,
                         "verificationCommit": None, "evidence": "Read-only audit; proposed proof/README changes not applied."} for item in findings],
        "limitations": ["Theorem2 real-record kernel excludes realized decoy-dependent records", "W5/W6/W7 finite passphrase endpoints", "Total oracle programs and independent strategy PMFs, no universal partial-program representation theorem", "Missing fractional-optimum/full-cost-expectation/bracket/capped-failure final assemblies", "Concrete primitives and production implementation excluded", "No clean-machine dependency installation or Mathlib cache download"],
        "verdict": "PUBLICATION_CHANGES_RECOMMENDED",
        "verdictReason": "Fresh source checks and kernel replay pass with only three permitted axioms, but full-game correspondence and proof-check instructions require the listed corrections or explicit qualifications.",
    }
    text = (HERE / "REPORT_TEMPLATE.md").read_text()
    for key, value in {"COMPLETED_UTC": data["completedUtc"], "SOURCE_FINGERPRINT": snapshot["sourceFingerprint"]}.items():
        text = text.replace("{{" + key + "}}", value)
    text += executions(source, kernel, probes)
    text += "\n## Confirmed findings\n\n"
    for item in findings:
        text += f"### {item['id']} — {item['severity'].capitalize()} — {item['title']}\n\n"
        for key in ["affected", "reproduction", "expected", "observed", "impact", "evidence", "recommendedFix", "requiredVerification"]:
            text += f"- **{key}:** {item[key]}\n"
        text += f"- **Applicable rules:** {', '.join(item['rules'])}.\n\n"
    text += qualifications()
    text += "## Detailed per-result correspondence\n\n"
    for filename in ["denial-g.md", "known-pair.md", "w-family.md", "challenge-k-records.md"]:
        note = (NOTES / filename).read_text()
        note = re.sub(r"^(#{1,4}) ", r"##\1 ", note, flags=re.M)
        text += note + "\n\n"
    text += "## Source and dependency identity\n\n| Source | Lines | SHA-256 |\n| --- | --- | --- |\n"
    for item in snapshot["files"]:
        name = item["path"].split("port-v4.35/", 1)[-1]
        text += f"| `{name}` | {item['lines']} | `{item['sha256']}` |\n"
    text += "\nAll thirteen dependency revisions matched the locked commits and had clean tracked status.\n\n| Dependency | Full revision |\n| --- | --- |\n"
    for item in load("dependencies.json"):
        text += f"| `{item['name']}` | `{item['actual']}` |\n"
    text += "\n## Procedure, applicability and remaining checks\n\n"
    for name, digest in procedures.items():
        text += f"- `{name}`: `{digest}`.\n"
    mapping = (NOTES / "applicability.md").read_text().split("| Canonical check |", 1)[1]
    mapping = "| Canonical check |" + mapping.split("\n\nAll 32 original IDs", 1)[0]
    mapping = mapping.replace(
        "Final schema/privacy/evidence checks and independent final review must be completed by the coordinator/reviewer. Until their artifacts exist this is pending (`not-run`), not a pass supplied by this note.",
        "The paired schema/privacy/evidence validation is retained in machine-local report-validation.json. The final independent review record identifies its exact snapshot; these checks do not certify the production implementation."
    )
    text += (
        "\nThe following table preserves all 32 canonical procedure IDs. Reviewed mathematical "
        "subcases are distinguished from application operations that are not applicable and "
        "release/installation operations that were not run. These rows are not additional tests.\n\n"
        + mapping + "\n"
    )
    text += (
        "\nThe procedure's SEC/FUN/API/ARC/DOC concerns are applied to ideal models, query interfaces, "
        "statement meaning, dependencies and claims; BLD concerns cover actual proof checking. "
        "Browser UI, wallet exports, network providers, transaction protocols, WASM reproduction "
        "and application secret cleanup are not applicable to this proof-only target. Those "
        "checks are not represented as passed. Runtime implementation and release suites are not run.\n\n"
        "No source correction or release action was performed. The standalone package still needs "
        "the owner's repository/license/publication-layout decisions. LegacyPMF retains its "
        "upstream attribution; a public distribution must carry the intended notices. This report "
        "is an audit of proofs and correspondence, not an independent cryptographic certification.\n"
    )
    basename = AUDITS / f"AUD-012-{data['date']}"
    basename.with_suffix(".md").write_text(anonymize(text))
    basename.with_suffix(".json").write_text(anonymize(json.dumps(data, indent=2)) + "\n")
    print(json.dumps({"report": basename.name, "bytes": len(text.encode()), "findings": len(findings)}))


def executions(source, kernel, probes):
    """List every unique checked module without conflating compile/replay/control totals."""
    text = "\n## Executed checks\n\n| Module | Source exit / seconds | Kernel exit / seconds |\n| --- | --- | --- |\n"
    for item in source:
        name = item["module"]
        compilation = load("compile-" + name + ".command.json")
        replay = next(row for row in kernel if row["module"] == name)
        record = load(replay.get("record", "kernel-" + name) + ".command.json")
        duration = "shared exact-module batch" if "record" in replay else str(record["elapsedSeconds"])
        text += f"| `{name}` | {compilation['exitCode']} / {compilation['elapsedSeconds']} | {record['exitCode']} / {duration} |\n"
    text += "\n| Axiom control | Expected / observed exit | Gate recognized | Marker |\n| --- | --- | --- | --- |\n"
    for item in probes:
        text += f"| {item['name']} | 1 / {item['exitCode']} | {item['gateRejected']} | {item['markerFound']} |\n"
    lake = load("lake-build.command.json")
    text += f"\n`lake --no-cache build` exit: {lake['exitCode']}; {lake['elapsedSeconds']} seconds. "
    text += "This checks ordinary package usability; the fresh source and kernel rows provide separate source-elaboration and kernel-replay evidence.\n"
    text += (
        "\nThe checkpoint's fresh sentinel is `MHFE_COMPLETE_AXIOM_INVENTORY|6036|3888|standard`; "
        "the full 6,036-root list and axiom closure are retained in the local JSON inventory. "
        "No positive proof row is replaced by a previously reported result. Negative axiom controls "
        "are not extra successful proofs, and compilation and kernel totals are not added together "
        "as distinct mathematical results. All exact command/log hashes are in the paired JSON.\n\n"
        "The synthetic README loop returned zero and printed both failed modules. This proves "
        "status masking, not that actual current modules fail. Source compilation may emit "
        "warnings; the report does not claim warning-free checking. A diagnostic direct checker "
        "help call before setting PATH could not find lean; actual replays explicitly use the "
        "pinned bin directory. A final progress-only ps diagnostic returned 1 because the "
        "Lean process had already completed successfully; it is retained as a diagnostic race, "
        "not a failed proof check. No source assertion, gate or parameter was weakened.\n"
    )
    return text


def qualifications():
    """Keep scope limits and informal bridges separate from false-proof allegations."""
    return """## Exactness limits, improvements and publication decision

| Topic | Checked result | Remaining distinction |
| --- | --- | --- |
| Genuine record | Theorem2 bounds the actual narrower Lean game | Extend realRecords to realized Q/disclosed state/U record for the full textual experiment. |
| Passphrase domain | Main Theorem5 and W2 support arbitrary PMFs/labels | W5/W6/W7 final source endpoints remain finite; no countable corollary lift is exported. |
| Uniform top2 | Exact saturated finite-uniform formula is proved | This is stronger literal coverage than EasyCrypt's named upper inequality; do not describe it as absent. |
| Fractional top | Exact formula and necessary universal upper bound are proved | No optimizer witness/general real-x floor-ceiling/lower-floor endpoint was found. |
| Adaptive costs | General pair-counting lemma and full uniform-cost source result are proved | The general-prior expected-top2 source-game expression is not assembled. |
| W7 comparison | Actual attacks, lower bounds, every mode and budgets are proved | The final upper/lower bracket is a direct mathematical consequence; no exported final source-game bracket assembly was found. |
| Capped generation | Option-search and finite fallback/closeness laws are proved | A no-container-on-failure success-domination wrapper is not exported. Failure and fallback are different experiments. |
| G7 | Final bound uses proved exact batch serialization | Stronger batch-Early intermediate prose assertions are not separate named results; README already notes this. |
| Known-pair depth | Query counts and exact eleven-call filter are proved | The six-level scheduling remark is intentionally informal. |
| G10 phrase encoding | Bit regrouping/checksum-dependent composition and its G-query cost are proved | It is not a verified English wordlist/parser or Unicode implementation. |
| Private randomness | Explicit independent PMF strategy mixtures are proved | No universal encoding theorem for all partial probabilistic executable programs. |

The record-kernel distinction is observable: condition on a genuine context and distinct genuine/
disclosed phrases; choose U as a fresh fair Boolean. A real record copying that realized U agrees
with it with probability one. Any real record drawn independently before the fair U agrees with
probability one half. This separates the experiment schemas without asserting that the numerical
advantage bound fails. The final averaged theorem keeps usage outside Setup, so an outer common
parameter does not encode this missing fresh correlation. Existing pointwise clean-run equalities
suggest a future broader proof, but that future endpoint is not credited here.

For a public scoped research artifact, the successful bounds can be retained with these precise
limitations, corrected check commands and honest provenance. For a claim of complete equivalence
to the unrestricted prose, finish the domain/game/assembly extensions first. No rewrite of the
successful K5/W5 numerical bounds is indicated. The existing comparison's broad equivalence claim
needs an independent assessment in the next report.

All findings remain open; proposed changes have not been applied or called verified. No fix commit
or verification commit exists. Read-only review and synthetic audit controls do not authorize a push.

"""


if __name__ == "__main__":
    main()
