#!/usr/bin/env python3
"""Assemble the proof-specific audit from retained checks and reviewed English notes."""

import datetime
import hashlib
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
WORKSPACE = REPO.parent
EVIDENCE = HERE.parent / "AUD-011-evidence"
NOTES = WORKSPACE / "tmp/easycrypt-audit-2026-11-12"


def read_json(name):
    """Read retained evidence without substituting an earlier run."""
    return json.loads((EVIDENCE / name).read_text())


def findings():
    """Return coordinator-validated findings; mathematical coverage gaps are separate."""
    return [
        {
            "id": "AUD-011-BLD001", "category": "BLD", "kind": "finding",
            "title": "The documented proof-check loop returns success after a compiler failure",
            "severity": "medium", "status": "open", "releaseBlocking": True,
            "releaseBlockingReason": "Correct the advertised automated verification command before publication acceptance.",
            "affected": "EasyCrypt README.md:118; applies to both documented toolchains.",
            "reproduction": "Replace easycrypt by a shell function returning 7 and run the exact README loop over two synthetic filenames.",
            "expected": "The first failed proof stops checking and propagates a nonzero exit status.",
            "observed": "The loop prints FAILED: First.ec, skips Second.ec and exits 0. A version using exit 1 exits 1.",
            "impact": "Automation can accept an incomplete or failed proof run. This does not make the current checked proofs false.",
            "evidence": "Local static-inventory.json/readmeLoop; static.log; independent publication challenge.",
            "recommendedFix": "Ship a verifier that exits nonzero on a failed compile, preserves the failing filename and compiles every source strictly.",
            "requiredVerification": "Stub failure must produce a nonzero verifier status; successful checking must cover all 18 sources. Keep this separate from the positive proof run.",
            "rules": ["CORE-28", "CORE-43", "DOC-06", "DOC-07"],
        },
        {
            "id": "AUD-011-BLD002", "category": "BLD", "kind": "finding",
            "title": "The no-cache checking recipe can accept an unchanged false theorem from a weak cache",
            "severity": "medium", "status": "open", "releaseBlocking": True,
            "releaseBlockingReason": "The advertised fresh-source proof check must refuse or independently exclude existing root caches.",
            "affected": "EasyCrypt README.md:114-118; installed EasyCrypt ce19cb6 src/ec.ml:660-664,936 and src/ecEco.ml:225-273.",
            "reproduction": "On an isolated false synthetic theorem, create a cache with compile -pragmas Proofs:weak; run the documented compile -no-eco unchanged; deactivate only that synthetic cache and repeat.",
            "expected": "A strict fresh-source check rejects the false theorem regardless of an existing weak-check cache.",
            "observed": "Weak creation exits 0; strict -no-eco replay exits 0 with an empty log; the same source without its active cache exits 1 with cannot prove goal (strict).",
            "impact": "The recipe can skip actual proof checking and reuse results not established strictly. Current audited src has no .eco, and its fresh positive runs remain valid.",
            "evidence": "Local cache-create-weak, cache-strict-replay and cache-without-cache command/log records; synthetic source/cache retained locally; independent source and digest challenge.",
            "recommendedFix": "Refuse existing root .eco files before a claimed fresh check, or document a verified safe cache-isolation procedure. Do not delete user caches silently. The audit harness now refuses cached roots.",
            "requiredVerification": "The synthetic weak-cache case must be refused before acceptance; a cache-free false theorem must fail; all current cache-free sources must pass.",
            "rules": ["CORE-28", "CORE-43", "DOC-06", "DOC-07"],
        },
        {
            "id": "AUD-011-DOC001", "category": "DOC", "kind": "finding",
            "title": "The broad result-index claim obscures exact forms that are not formalized",
            "severity": "low", "status": "open", "releaseBlocking": False,
            "affected": "EasyCrypt README.md:38-39 and INDEX.md introduction; compare DESIGN.md:254-259 and Theorem5.ec:1303,1408.",
            "reproduction": "Compare the exact uniform-top2 identity and adaptive expectation bound in current supplement A.6 with the named EasyCrypt signatures.",
            "expected": "A claim that every result is indexed distinguishes exact statements from weaker consequences and informal lifts.",
            "observed": "top2_uniform proves only an upper inequality; theorem5_cost uses a constant pointwise envelope. The new capped-failure lift has no encoded public game/theorem.",
            "impact": "Readers can infer sentence-by-sentence formal coverage that the source does not establish. No proved inequality is contradicted.",
            "evidence": "Independent W-family review and skeptical challenge; exact signatures reproduced in this report.",
            "recommendedFix": "Qualify complete-coverage wording and list exactness limits prominently, or add the missing exact forms. Keep the already disclosed finite-passphrase qualification.",
            "requiredVerification": "Each claimed exact assertion must point to a signature with matching quantifiers, event and formula; the table must mark weaker/narrower variants explicitly.",
            "rules": ["DOC-06", "DOC-07"],
        },
        {
            "id": "AUD-011-DOC002", "category": "DOC", "kind": "finding",
            "title": "Unqualified independence wording can imply blind independence of statements",
            "severity": "low", "status": "open", "releaseBlocking": False,
            "affected": "EasyCrypt README.md:142-143; SCOPE.md:25-27; LEAN-COMPARISON.md:719-721.",
            "reproduction": "Read the public-facing independently wording against the explicit prior review of Lean statements in SCOPE and the comparison limitations.",
            "expected": "Describe separate proof systems without implying independently derived blind statements.",
            "observed": "The README says independently, while retained provenance explicitly says the EasyCrypt author had read the Lean statements first.",
            "impact": "The wording can overstate the independence evidence. This review found no basis to allege copied proofs or invalid verification.",
            "evidence": "Independent publication challenge; cited documents and their retained hashes.",
            "recommendedFix": "Say separately implemented in two proof systems and disclose prior access to the Lean statements in the same paragraph.",
            "requiredVerification": "The introduction and comparison limitations must give a consistent provenance account.",
            "rules": ["DOC-06", "DOC-07"],
        },
    ]


def main():
    """Generate the paired audit only after every planned current proof check has completed."""
    snapshot = read_json("snapshot.json")
    inventory = read_json("static-inventory.json")
    compiles = read_json("compile-summary.json")
    compiles.append({"name": "Model", **read_json("compile-Model-escalated.command.json")})
    assert len(compiles) == 18 and all(x["exitCode"] == 0 for x in compiles)
    controls = read_json("controls/compile-summary.json")
    expected = {"Positive": 0, "NegativeFalse": 1, "NegativeK5": 1, "NegativeW5": 1}
    assert {x["name"]: x["exitCode"] for x in controls} == expected
    changed = []
    for item in snapshot["files"]:
        if hashlib.sha256((WORKSPACE / item["path"]).read_bytes()).hexdigest() != item["sha256"]:
            changed.append(item["path"])
    assert not changed, changed
    now = datetime.datetime.now(datetime.timezone.utc)
    date = now.date().isoformat()
    records = findings()
    procedures = read_json("procedure-hashes.json")
    result = {
        "schemaVersion": 1, "auditId": "AUD-011", "auditNumber": 11, "date": date,
        "title": "EasyCrypt proof validity, exact specification correspondence and publication readiness",
        "completedUtc": now.isoformat(),
        "reviewer": {"name": "Codex coordinator with three distinct read-only specialist scopes and skeptical follow-ups", "model": None, "reasoningEffort": None},
        "snapshot": {"commit": snapshot["specCommit"], "commitComplete": True,
                     "workingTree": "Specification source clean at baseline. Only this audit's report, harnesses and index are added; unrelated workspace changes are preserved. EasyCrypt sources are a pre-existing artifact outside the specification Git tree.",
                     "sourceFingerprint": snapshot["sourceFingerprint"]},
        "procedureHashes": procedures,
        "scope": {"included": ["Current EasyCrypt src: all 18 files", "Deniability and appendix A: all numbered results and rigorous supporting claims", "Current normative README/model interpretation", "Assumptions, public claims, build instructions and source identity"],
                  "excluded": ["Lean source audit, deferred to the next separate report", "Current Rust/browser implementation correctness", "Primitive security and physical costs", "SMT/EasyCrypt implementation soundness", "Full release reproducibility, licensing decision and publication"]},
        "checks": {"strictCompiles": compiles, "controls": controls,
                   "static": {"files": 18, "lines": 19223, "namedLemmaDeclarations": 799,
                              "namedEquivalenceDeclarations": 104, "directAxioms": 109,
                              "sectionHypotheses": 73, "bypassDirectives": 0, "checksums": "18/18 matched"},
                   "sourceUnchanged": True, "proofCoverage": "Per-result semantic correspondence and final critical proof paths reviewed; every current source checked strictly. Not an independent handwritten rederivation of every tactic or a full program audit."},
        "findings": records, "observations": [],
        "remediation": [{"id": x["id"], "status": "open", "fixCommit": None,
                         "verificationCommit": None, "evidence": "Read-only baseline; no source or publication correction applied."} for x in records],
        "limitations": ["Finite passphrases instead of the text's countable domain", "Lossless adversaries/continuations; no formal general partial-adversary lift", "Weaker uniform-top2 and adaptive-cost forms", "No public capped-failure dominance game", "Abstract BIP39/normalization/record interpretation", "Fresh checking uses EasyCrypt main ce19cb6; r2026.10 compatibility not freshly rerun", "Positive/negative controls are sanity checks, not a soundness proof of the trusted base"],
        "verdict": "PUBLICATION_CHANGES_RECOMMENDED",
        "verdictReason": "All current proof sources check and no false final bound was identified under their stated premises. Literal unrestricted correspondence is not established; repair the verification command and qualify publication claims before acceptance.",
    }
    reviewed = read_json("review-snapshot.json")
    result["independentReview"] = {
        "reviewedDiffSha256": reviewed["diffSha256"],
        "reviewedReportSha256": reviewed["files"]["docs/audits/AUD-011-2026-11-12.md"],
        "result": "No material findings in final independent report review.",
        "recordAddedAfterReview": True,
        "checks": "18 successful current-source checks; static/hash checks; positive/negative controls; cache diagnostic; report/schema/privacy/log validation.",
        "notRun": "Fresh r2026.10, single-solver-only replay, clean installation, Rust/browser/release suites, Lean checks.",
    }
    # Published records anonymize paths; exact unredacted commands remain local evidence.
    result = json.loads(re.sub(r'/home/[^/\s"<>]+/', '/home/user/', json.dumps(result)))
    report = heading(result, inventory, compiles, controls)
    report += finding_sections(records)
    report += correspondence()
    report += inventory_sections(inventory, procedures)
    report += (
        "\n## Independent final review record\n\n"
        f"Reviewed diff against the recorded base: `{reviewed['diffSha256']}`. "
        f"Reviewed report SHA-256: `{result['independentReview']['reviewedReportSha256']}`.\n"
        "The independent reviewer matched all 12 artifact hashes, all 18 passing proof logs and "
        "the cache diagnostic; no material report defect was found. The four findings remain open.\n"
        "Checks run: strict proofs, source/hash/bypass inventory, controls, cache reproduction and "
        "schema/privacy/evidence validation. Not run: fresh r2026.10, isolated single-solver replay, "
        "clean installation, implementation/release suites or Lean. This short record and its JSON "
        "counterpart were appended after that reviewed snapshot; proof sources and conclusions did not change.\n"
    )
    report = re.sub(r'/home/[^/\s"<>]+/', '/home/user/', report)
    (HERE.parent / f"AUD-011-{date}.md").write_text(report)
    (HERE.parent / f"AUD-011-{date}.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"report": f"AUD-011-{date}.md", "bytes": len(report.encode()), "findings": len(records)}))


def heading(result, inventory, compiles, controls):
    """Write the proof-oriented main assessment and reproducibility evidence."""
    text = (HERE / "REPORT_TEMPLATE.md").read_text()
    values = {"COMPLETED_UTC": result["completedUtc"], "SPEC_COMMIT": result["snapshot"]["commit"],
              "SOURCE_FINGERPRINT": result["snapshot"]["sourceFingerprint"]}
    for key, value in values.items():
        text = text.replace("{{" + key + "}}", value)
    for item in sorted(compiles, key=lambda x: x["name"]):
        text += f"| `{item['name']}.ec` | {item['exitCode']} | {item['elapsedSeconds']} | `{item['logSha256']}` |\n"
    text += """
| Control | Expected / observed exit | Meaning |
| --- | --- | --- |
| Positive | 0 / 0 | A true elementary SMT statement is checked. |
| NegativeFalse | 1 / 1 | `false` is rejected in strict mode. |
| NegativeK5 | 1 / 1 | Halving the leading term of the imported K5 loss is rejected. |
| NegativeW5 | 1 / 1 | Replacing generation budget 0 by -1 to reduce `deltagen` is rejected. |

A separate cache diagnostic deliberately weak-checked a new false synthetic theorem outside the
reviewed source. It created a cache (exit 0); the documented strict `-no-eco` replay returned 0
with an empty log; after retaining that own synthetic cache under an inactive suffix, the same
source failed strictly (exit 1). This is diagnostic evidence for AUD-011-BLD002, not an accepted
proof or a weak mode applied to the reviewed development. The current-source passes have full
progress logs and no root caches.

These controls are small sanity checks of the active checking path, not strengthened end-to-end
versions of the entire K5/W5 theorem. Existing historical tailored controls and r2026.10 logs were
read as context but not counted as fresh execution. Release r2026.10 compatibility, a clean-machine
installation and individual single-solver replay were not freshly rerun.

Static checks returned 0: 18/18 source checksums match the package manifest; no active bypass
directive was found; the README failure loop defect and corrected nonzero behavior were both
reproduced with synthetic filenames. The command is a probe of status handling, not a claim that
the current compiler actually rejected a current proof.

Execution exceptions are retained rather than erased. The first Model invocation failed because
the sandbox denied the systemd user bus (exit 1); the approved rerun passed. Initial fetch failed
on sandbox SSH configuration and succeeded with approval. A diagnostic config call placed its
option before the subcommand and exited 1; corrected `easycrypt config -why3 ...` exited 0.
An exploratory checksum invocation used the package directory instead of `src/` and could not
open files; the recorded correct invocation uses `src/` with `../SHA256SUMS`. These are harness/
environment mistakes, not proof failures. No assertion or source was weakened to obtain a pass.

## Finding register

| ID | Severity | Status | Publication blocking | Result |
| --- | --- | --- | --- | --- |
| AUD-011-BLD001 | Medium | Open | Yes: advertised verifier status | Failed compilation can return overall success. |
| AUD-011-BLD002 | Medium | Open | Yes: fresh-source check | `-no-eco` can accept an unchanged false theorem through an existing weak cache. |
| AUD-011-DOC001 | Low | Open | No | Broad index coverage wording needs explicit exactness distinctions. |
| AUD-011-DOC002 | Low | Open | No | Separate proof systems must not imply blind statement independence. |

No confirmed Critical or High finding and no counterexample to a proved final numerical bound
was identified. That is a finding count for this scope, not a guarantee that no defect exists.

"""
    return text


def finding_sections(records):
    """Preserve substantive findings and distinguish remediation from review."""
    text = "## Confirmed findings\n\n"
    for item in records:
        text += f"### {item['id']} — {item['severity'].capitalize()} — {item['title']}\n\n"
        for key in ["affected", "reproduction", "expected", "observed", "impact", "evidence", "recommendedFix", "requiredVerification"]:
            text += f"- **{key}:** {item[key]}\n"
        text += f"- **Applicable rules:** {', '.join(item['rules'])}.\n\n"
    text += """## Exactness qualifications and proposed extensions

| Issue | Current formal claim | Relationship to the text | Action for literal full coverage |
| --- | --- | --- | --- |
| Passphrases | `PpT` is finite, with lossless `dQ` | A.6 permits a countable ranked domain. Already disclosed in ASSUMPTIONS/README. | Prove a countable/finite-approximation lift or explicitly retain finite scope. Do not silently narrow the normative input contract. |
| Adversary termination | Final bounds assume lossless attackers and continuations against permitted lossless interfaces | Prose says when the adversary halts. A general partial-adversary limit lift is not exported. | State the termination convention or prove the lift. |
| Uniform `top2` | `top2_uniform` proves `top2 m n <= min(n,m*N2)/(N1*N2)` | The text states the saturated equality with `min(m,N1)`. The upper consequence is valid. | Add exact equality and finite-support form if claimed. |
| Adaptive cost | `theorem5_cost` uses a constant `T` bounding every feasible allocation | The text's expected `top2` term can be smaller. Uniform final cost bound does match. | Export the expected-value game theorem, or label the constant-envelope scope. |
| Capped generation | Internal `Seq` returns its last trial after `2^80`; final theorems transfer to covered rules | It is not a failure-returning generation API. The text's unconditional failure/no-win coupling is mathematically valid but informal here. | Add an optional-result game and domination lemma. Do not infer a bound conditioned on successful creation. |
| BIP39 representation | Abstract injections/packing, realized by synthetic bit-word/tagged models | Entropy-to-valid-phrase facts are an interpretation bridge, not verified parser/encoder code. | Name that bridge or instantiate the concrete encoding separately. |
| G7 batches | Formal interface batches A calls | Current text supplies A-first sequentialization for general mixed batches. | Export the scheduling reduction if all prose bridges must be mechanized. |
| Known-pair depth | MatchK proves query counts | The six-step schedule is not a formal depth theorem. | Keep it outside checked-result claims or formalize the schedule. |
| `averaging` | Public monitored form includes Early | Text equation (2) is written before charging Early; internal eager steps give the exact route. | Label the index entry as the monitored form or export the eager identity. |
| `r=0` G10 matching attack | Named attack still makes G calls, budget `qG<=m` | Removing the unused verifier read would give the natural `qG=0` attack. | Optional optimization lemma; existing upper G10 already permits zero G budget. |
| Candidate cardinality | Top matching forms need enough distinct passwords | Finite distributions saturate; arbitrary m cannot demand nonexistent candidates. | State saturation/cardinality explicitly in prose. |
| Zero decoy mass | Simulation uses a zero subdistribution | Explicit common failure is not encoded; the bound is then the trivial one. | Optional explicit failure wrapper; no false numerical bound identified. |

For example, with `N1=2,N2=3,m=4,n=12`, exact uniform `top2` is 1 while the named formal upper
right-hand side is 2. This shows why the inequality is weaker, not why it is wrong. Likewise an
expectation is not a permitted choice of the constant envelope T unless it independently bounds
every possible allocation; replacing one by the other requires proof.

## Publication and remediation decision

The source can be presented as machine-checked finite-domain forms of the security bounds, with
the explicit assumptions and trust base in this report. I recommend fixing AUD-011-BLD001/002 before
advertising the verification instructions, clarifying AUD-011-DOC001/002, and regenerating the
result/count metadata. No rewrite of the successful K5 or W5 proof is indicated by this audit.

If the intended publication claim is literally every rigorous sentence of the unrestricted prose,
the finite/countable and missing-exact-form extensions are necessary for that claim. They are
research/formalization completion work, not evidence that the existing checked inequalities fail.
Changing the text to match a weaker result is an owner decision, not something done silently.

The proof package currently has no standalone tracked repository/package identity in this checkout.
Choose the intended distribution layout and license before publication, retain source revision and
toolchain pins, and keep internal local paths/development weak-check outputs out of the public
package. This is packaging preparation, not a legal-license conclusion or an authorization to push.

| Finding ID | Status | Fix commit | Verification commit | Evidence |
| --- | --- | --- | --- | --- |
| AUD-011-BLD001 | Open | Not fixed | Not run | Original synthetic status reproduction. |
| AUD-011-BLD002 | Open | Not fixed | Not run | False-theorem cache replay diagnostic; actual sources unaffected. |
| AUD-011-DOC001 | Open | Not fixed | Not run | Signature/text comparison and independent challenge. |
| AUD-011-DOC002 | Open | Not fixed | Not run | Publication/provenance wording comparison. |

The report/index/harness additions are audit artifacts only. No reviewed proof, specification,
production code, dependency, fixture or workflow was changed. No paid remote CI was dispatched.

"""
    return text


def correspondence():
    """Embed reviewed detailed correspondence so the report stands alone."""
    text = "## Detailed correspondence annexes\n\n"
    for filename, title in [
        ("denial-g.md", "Deniability and one-container results"),
        ("known-pair.md", "Known-pair results and the revised K5"),
        ("w-family.md", "Passphrase, selection, W1-W7 and the revised W5"),
    ]:
        note = (NOTES / filename).read_text()
        note = re.sub(r"^# .*\n", "", note, count=1)
        note = re.sub(r"^(#{2,5}) ", r"#\1 ", note, flags=re.M)
        text += f"### {title}\n\n{note.strip()}\n\n"
    return text


def inventory_sections(inventory, procedures):
    """Retain every direct axiom and explain application-check non-applicability."""
    text = """## Direct assumption inventory

The following lists all 109 syntactic direct `axiom`/`declare axiom` statements in current sources:
36 theory/model declarations and 73 section hypotheses. It is not the transitive assumption
count: `FinType` clones also introduce enumeration assumptions, and subtype constants such as
positive lambda introduce premises. `ASSUMPTIONS.md` and the model annex describe these as well.
No listed declaration assumes an attacker-success security conclusion. Budget/termination axioms
are conditional attacker/rule premises, not universal claims that every program has that behavior.

| File:line | Declaration | Kind |
| --- | --- | --- |
"""
    for item in inventory["axioms"]:
        kind = "section hypothesis" if item["sectionHypothesis"] else "abstract theory/model"
        text += f"| `{item['file']}:{item['line']}` | `{item['name']}` | {kind} |\n"
    text += """
Suite3 realizes fixed widths/XOR/distributions; Instances realizes Source at five lengths and
Denial at five suite-3/four suite-4 lengths. These are consistency witnesses for the abstract
theories. Actual normalized passwords, finite passphrases and their distributions remain abstract;
arbitrary record distributions remain parameters of the general deniability theorem. Unit-record
instances do not mean real wallet-record behavior was implemented or tested.

## Source hashes

| Source | Lines | SHA-256 |
| --- | --- | --- |
"""
    for item in inventory["files"]:
        text += f"| `{item['file']}` | {item['lines']} | `{item['sha256']}` |\n"
    text += "\n## Procedure identity and legacy-check applicability\n\n"
    text += "The canonical procedure files were read from the GitHub main branch because the local\nwallet-tools checkout is absent. Their exact bytes are retained as local evidence. Hashes:\n\n"
    for name, digest in procedures.items():
        text += f"- `{name}`: `{digest}`.\n"
    guide = (EVIDENCE / "procedure/FULL_AUDIT_GUIDE.md").read_text()
    checks = re.findall(r"^### (CHECK-[A-Z]+-\d+) — (.+)$", guide, re.M)
    assert len(checks) == 32
    mapping = {
        "CHECK-SEC-001": "Reviewed: ideal threat model, secret interfaces and non-leakage assumptions; no runtime secret lifecycle claim.",
        "CHECK-SEC-004": "Reviewed: ideal functions, permutation, guesses and collision constants; real primitive security excluded.",
        "CHECK-SEC-007": "Reviewed: oracle budgets and termination premises; no application availability test.",
        "CHECK-FUN-001": "Reviewed abstract widths/entropy/seed interpretation; concrete BIP39 conversion excluded.",
        "CHECK-API-001": "Reviewed: module/oracle interfaces and restrictions, game views and win events.",
        "CHECK-BLD-001": "Passed: every actual proof source checked directly in strict mode.",
        "CHECK-BLD-003": "Partial: source/binary/config hashes and pins recorded; full clean installation/licensing decision not executed.",
        "CHECK-BLD-005": "Failed: README verification status propagation; remote CI/release outside scope.",
        "CHECK-ARC-001": "Reviewed: theory dependency/instantiation structure and ownership of game ghosts.",
        "CHECK-ARC-003": "Reviewed: actual final paths, no active bypass pragmas, assumptions and comments/claims.",
        "CHECK-DOC-001": "Reviewed with findings: numerical claims, limitations and exact correspondence.",
        "CHECK-DOC-002": "Reviewed with findings: verifier command and provenance; packaging remains future work.",
        "CHECK-DOC-003": "Reviewed: report pair, immutable IDs, source/evidence hashes and index; final schema validation retained separately.",
    }
    text += "\n| Legacy check | Proof-audit disposition |\n| --- | --- |\n"
    for check, title in checks:
        reason = mapping.get(check, "Not applicable to this proof-only scope: the named application, runtime, export, transport or artifact operation is absent from the formal source under review.")
        text += f"| {check} — {title} | {reason} |\n"
    text += """
## Evidence retention and final limits

Local `AUD-011-evidence/` contains snapshot, command records, original logs, five-second memory
samples, inventory, procedure hashes and final report validation. `AUD-011-harnesses/` contains
the retained tools and rerun instructions. The detailed source reviews were consolidated above;
their working notes and independent challenges remain local rather than being presented as public
downloadable evidence.

This is a completed proof-scope audit with explicit exactness gaps. It is not a fully executed
program/release audit. It supports the checked formal bounds under their recorded premises and
the publication recommendations stated above; it does not certify all defects absent.
"""
    return text


if __name__ == "__main__":
    main()
