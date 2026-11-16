#!/usr/bin/env python3
"""Assemble the trial-count correspondence audit from exact local verification evidence."""

import datetime
import hashlib
import json
from pathlib import Path
import re
import shlex


HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
WORKSPACE = HERE.parents[3]
EVIDENCE = AUDITS / "AUD-016-evidence"


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(headers, rows):
    def cell(value):
        return str(value).replace("|", "\\|").replace("\n", "<br>")
    return "\n".join(["| " + " | ".join(headers) + " |",
                      "| " + " | ".join("---" for _ in headers) + " |",
                      *("| " + " | ".join(map(cell, row)) + " |" for row in rows)])


def main():
    snapshot = read("snapshot.json")
    lean, ec = read("lean-summary.json"), read("ec-summary.json")
    kernel, inventory, checkpoint = read("kernel-summary.json"), read("audit-inventory.json"), read("checkpoint-inventory.json")
    assert len(lean) == len(kernel["requested"]) == 42 and all(r["exitCode"] == 0 for r in lean)
    assert kernel["requested"] == kernel["observed"] and kernel["exitCode"] == 0
    assert len(ec) == 23 and all(r["exitCode"] == 0 for r in ec)
    assert len(checkpoint["roots"]) == 6185 and checkpoint["theorems"] == 4003
    assert len(inventory["roots"]) == 6193 and len(inventory["theoremAxioms"]) == 4004
    controls = read("control-summary.json")
    assert all(r["exitCode"] == 1 and r["markerFound"] and r["gateRejected"] for r in controls)
    commands = []
    for p in sorted(EVIDENCE.glob("*.command.json")):
        record = json.loads(p.read_text())
        assert sha(p.with_name(p.name.replace(".command.json", ".log"))) == record["logSha256"]
        commands.append({"name": p.name.removesuffix(".command.json"), **record})
    baseline = json.loads((AUDITS / "AUD-014-2026-11-13.json").read_text())
    findings = [
        {"id": "AUD-016-DOC001", "category": "DOC", "kind": "finding",
         "title": "The general disclosed-trials claim needs explicit secret-independent selection and scheduling coins",
         "severity": "medium", "status": "open", "releaseBlocking": True,
         "blockingReason": "Blocks the unrestricted literal general-rule disclosure claim. It does not block the correctly scoped sequential formal result; an explicit independence qualification resolves the gap.",
         "affected": "Specification DESIGN-NOTES.md:4703-4712 and4738-4761, specifically applying the first three selection conditions to the disclosed-trials extension.",
         "reproduction": "Take a uniform binary password P and a singleton passphrase alphabet. Let C be the fair bit identifying P, independent of the iid entropy draws and the random functions. Stop at the first passing draw when C=0 and the second passing draw when C=1. Under the literal stated independence condition C is independent of trial values, and the rule uses only order/outcomes/C and terminates almost surely on nonempty U.",
         "expected": "The ideal disclosed transcript can be simulated independently of the secrets/functions. Selection/scheduling randomness for a disclosed-trial rule must be jointly sampled independently of secrets, functions and underlying entropy draws, with no extra hidden inputs to the policy.",
         "observed": "The selected entropy is uniform on U for either password, so hidden-trial source equivalence survives. But the disclosed number of PASS outcomes is one or two and identifies P. The pair attacker uses no oracle queries. On successful generation it wins with probability1 rather than approximately1/2; the ideal expected count is1.5*2^16, so the proposed2^-136*n addition remains tiny. Empty-U exceptional mass does not remove that gap.",
         "impact": "The broad general-rule sentence is not valid under its literal marginal-independence reading. Conventional fresh private coins exclude this countermodel, but that stronger intended hypothesis needs to be explicit. No checked Lean/EasyCrypt sequential theorem permits this policy or is refuted by it, and no implementation leak is alleged.",
         "evidence": "Independent wording scope proposed the missing hypothesis; an independent Lean scope challenged and confirmed the first-versus-second-pass countermodel, including the empty-U qualification. The original selection clause only names independence from trial values, while the timing clause names secrets/functions too. Detailed argument in annexes.",
         "recommendedFix": "Add the explicit fresh joint-independence condition to A.6's number-of-trials disclosure paragraph. Keep the earlier hidden-trial selection rule separate: it need not be strengthened merely to support this extension. Retain the sequential/general/workers formal-coverage distinctions.",
         "requiredVerification": "The revised statement excludes the P-correlated selection bit, permits independent randomized scheduling, and does not demand conditional independence after observing stopping/outcomes. Preserve all sequential endpoint hypotheses and constants. No general-worker formal theorem should be claimed until proved.",
         "rules": ["DOC-06", "DOC-07"]},
        {"id": "AUD-016-DOC002", "category": "DOC", "kind": "finding",
         "title": "Timing summaries do not consistently state the permitted postprocessing condition",
         "severity": "low", "status": "open", "releaseBlocking": False,
         "affected": "Specification README.md:805-806; DESIGN-NOTES.md:506-508,3963-3965 consistency; EasyCrypt README.md:114-115.",
         "reproduction": "Read the elapsed-time permission literally: delaying each trial by an encoding of the MHFE password depends neither on the trial value nor the passphrase, yet reveals the password. Compare with A.6's stricter outcomes-plus-independent-coins condition.",
         "expected": "Timing is a common postprocessing of the allowed outcome/count transcript and randomness jointly independent of secrets, functions and trial values, at fixed public settings. It has no additional hidden dependence.",
         "observed": "The specification README excludes only trial value and passphrase, leaving password/function dependence unexcluded. The two DESIGN-NOTES phrases saying only on these are narrower deterministic shorthands, not independent unsafe permissions; adding independent coins makes them consistent. The EasyCrypt README names only secret-independence rather than the full list.",
         "impact": "A reader can overestimate which timer is covered. The actual sequential formal interfaces support the stricter A.6 condition, and real hardware/BIP39/OS timing has not been proved to satisfy it. This is a wording mismatch, not a false checked bound or evidence of an implemented timing attack.",
         "evidence": "Three source-first scopes agree on the README counterexample and shared-kernel interpretation. Lean samples a strategy PMF outside the whole generation; EC exposes only the actual outcomes and the adversary's own coins under its global restrictions.",
         "recommendedFix": "Apply the three proposed specification replacements in PROPOSED-WORDING.md, and align the EasyCrypt README or link to the central condition. Say no additional dependence rather than unconditional independence of the duration itself, since the allowed outcomes already depend on S/T/Q.",
         "requiredVerification": "All summaries agree with A.6, allow outcome-derived duration plus independent noise, exclude the password-delay witness, and do not claim that arbitrary measured wall-clock time or capped-and-revealed generation has been verified.",
         "rules": ["DOC-06", "DOC-07"]},
    ]
    applicability = []
    for row in baseline["checks"]["applicability"]:
        applicability.append({"id": row["id"], "title": row["title"],
                              "status": row["status"],
                              "scope": row["evidenceOrReason"] if row["status"] == "not-applicable" else
                              "Proof/specification model, exact trial-disclosure experiments, hypotheses, freshness and documentation; no native/application certification."})
    limitations = [
        "Sequential first-success rule only; general2^-136*n, workers and capped generation exposing attempts are not final formal endpoints.",
        "Finite full passphrase alphabet, independent priors/functions, idealized cryptography, total-program/losslessness classes and hard budgets retain the development's stated scope.",
        "The2^-120 addend is verified, not claimed optimal; Lean need not state the sharper strict variance/deviation formula used in the prose or EC proof.",
        "Lean finite prefixes/survival/capped_close characterize the unbounded law on nonempty passing sets; no separate named Tendsto/uniqueness theorem is declared.",
        "Empty passing sets use exceptional completion/nontermination conventions; their mass is included in bounds, not asserted to terminate physically.",
        "No implementation clock, PBKDF2 timing, OS scheduler, random-generator/runtime cost, native Rust/WASM/CLI/browser or concrete cryptographic primitive audit.",
        "Dependencies reused at13 pinned clean Git revisions; no clean install/cache download, release artifact, full-cost Argon2/vector execution or remote CI.",
        "Two initial KnownPair strict SMT failures were preserved; final successful run used more available CPU/memory. No proof, assertion, timeout or solver configuration was weakened.",
        "Prior review hashes are historical: current Lean TrialCount and EC TrialCount differ from its first hash table; this audit uses its own exact snapshot and fresh checks.",
        "Specification and proof sources were not edited; wording is proposed only, with no commit or push.",
    ]
    data = {"schemaVersion": 1, "auditId": "AUD-016", "auditNumber": 16, "date": "2026-11-14",
            "completedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "title": "Sequential trial-count disclosure: Lean/EasyCrypt proof correspondence and timing-scope audit",
            "reviewer": {"name": "Codex coordinator with three independent read-only scopes", "model": None, "reasoningEffort": None},
            "snapshot": {"commit": snapshot["specCommit"], "commitComplete": True,
                         "workingTree": "Specification/proof sources unchanged; existing audit work preserved. Both proof packages are machine-local outside this repository Git tree.",
                         "sourceFingerprint": snapshot["fingerprint"], "inputManifest": snapshot},
            "scope": {"included": ["All current41 Lean chapters plus root and23 EasyCrypt sources for fresh validity", "Source-first semantic review of new trial proofs and dependencies", "Same generation/source/refusal/budgets, exact2^-120, loop law and both-system correspondence", "All supplied documentation/review claims and exact proposed timing changes"], "excluded": limitations},
            "procedureHashes": baseline["procedureHashes"],
            "checks": {"commands": commands, "applicability": applicability, "lean": lean, "easycrypt": ec,
                       "kernel": kernel, "checkpointInventory": {"declarations": 6185, "theorems": 4003, "axioms": checkpoint["axioms"]},
                       "fullSourceInventory": {"declarations": 6193, "theorems": 4004, "axioms": inventory["axioms"], "localAxioms": inventory["localAxioms"],
                           "extraNames": sorted(set(inventory["roots"]) - set(checkpoint["roots"]))},
                       "leanControls": controls, "ecCheckerControls": "four self-test cases passed", "dependencies": read("dependencies.json"),
                       "leanEnvironment": read("lean-environment.json"), "ecEnvironment": read("toolchain-identities.json")},
            "findings": findings, "observations": [],
            "remediation": [{"id": r["id"], "status": "open", "fixCommit": None, "verificationCommit": None,
                             "evidence": "Read-only audit; proposed wording has not been applied."} for r in findings],
            "limitations": limitations,
            "verdict": "SEQUENTIAL_FORMAL_RESULTS_CONFIRMED_WITH_GENERAL_RULE_AND_TIMING_WORDING_QUALIFICATIONS"}
    md = ["# AUD-016 — Trial-count disclosure and timing scope", "", "## Assessment", "", """The current Lean and EasyCrypt sequential trial-disclosure results agree with the precise
first-success model and retain exactly the advertised `+2^-120` in Theorem5(a), Theorem5(b)
and W5. No false checked sequential theorem, lost query budget, incorrect refusal restriction,
independent surrogate source/count, or missing collision factor was identified.

Fresh execution accepted all42 Lean modules (41 chapters plus root), exact42-module kernel
replay, and all23 EasyCrypt roots in strict no-cache mode. The advertised namespace inventory
`6185|4003|standard` is reproduced. A broader source-origin inventory additionally checks eight
global declarations, including the mathematical lemma PMF.filter.congr_simp; it yields
`6193|4004|standard`, no local axioms, and only the same three standard axioms. All three Lean
negative controls and all four EasyCrypt checker controls behave as required.

The specification needs two distinct wording corrections. The more substantial one concerns
**general disclosed-trial selection/scheduling coins**, not the verified sequential algorithm.
The other concerns consistent elapsed-time permissions. Recommendation: apply the three proposed
timing clarifications, and add the explicit fresh independent-coin qualification to A.6's general
disclosure claim. Do not change numerical constants or broaden formal coverage on that basis.

The specification was not edited. Concrete English replacements are saved in
[PROPOSED-WORDING.md](AUD-016-harnesses/PROPOSED-WORDING.md). Publication of the correctly scoped
sequential proofs is supported; advertising the unrestricted general-rule claim under a literal
weak coin-independence reading is blocked until qualified. No native timing or whole-utility
verification follows from these results.""", "", "## Record metadata", "",
          table(["Field", "Value"], [["Audit / UTC completion", "AUD-016 / " + data["completedUtc"]],
              ["Reviewer / exact model / effort", data["reviewer"]["name"] + "; unknown / unknown"],
              ["Specification HEAD / origin main", snapshot["specCommit"] + " / " + snapshot["specOriginMain"]],
              ["Lean artifact", "tmp/lean-review-2026-11-11/port-v4.35/"],
              ["EasyCrypt artifact", "tmp/easycrypt-mhfe-2026-11-09/"],
              ["Input identity", str(len(snapshot["files"])) + " files; " + snapshot["fingerprint"]],
              ["Companion / tools", "[JSON](AUD-016-2026-11-14.json) / [rerun harnesses](AUD-016-harnesses/README.md)"]]), "",
          "## Procedure, scope and method", "",
          table(["Canonical procedure file", "SHA-256"], data["procedureHashes"].items()), "", """The retained canonical wallet-tools guide/standard/template/schema are reused with all32 CHECK
identifiers below. Proof-specific report sections are owner-authorized. One coordinator owns
execution and final judgment; three read-only scopes inspect Lean, EasyCrypt and specification/
documentation respectively. Source interfaces and proof routes were read before using the prior
TRIALS-REVIEW verdict. Candidate findings were independently challenged across scopes.

Current source identity governs: the prior review's initial Lean TrialCount hash caf543c0… and
EC TrialCount fbedcec5… differ from current9757b61e… and4c8c7248…. Its later review is useful
history, but its initial table is not an exact-snapshot certificate for current files. Current
source/root/kernel/solver evidence was collected here rather than inferred from author logs.

This is a complete check of the supplied trial-count work and its claimed correspondence, not a
new semantic audit of every unchanged older theorem or a release audit of the utility. Previous
finite-domain/idealization/model limitations remain visible; no earlier unrelated finding is
silently closed. Both proof artifacts remain outside the specification repository's Git tree.
No copy/clone of a project, dependency installation or source remediation was performed.""", "",
          "## Finding register", "",
          table(["ID", "Severity", "Status", "Release blocking", "Title"], [[r["id"], r["severity"].capitalize(), r["status"], "General disclosure claim only" if r["releaseBlocking"] else "No", r["title"]] for r in findings]), ""]
    for r in findings:
        md += [f"### {r['id']} — {r['severity'].capitalize()} — {r['title']}", "",
               table(["Field", "Assessment"], [[key, r[field]] for key, field in [("Affected", "affected"), ("Reproduction", "reproduction"), ("Expected", "expected"), ("Observed", "observed"), ("Impact / limits", "impact"), ("Evidence", "evidence"), ("Recommended fix", "recommendedFix"), ("Required verification", "requiredVerification")]]), "",
               "Status: open. Rules: " + ", ".join(r["rules"]) + ".", ""]
    md += ["## Exact correspondence and limits", "", """For a successful sequential search, the revealed transcript is N failures followed by one pass.
The Lean count N is zero-based; the ordinary number of attempts is N+1. EasyCrypt exposes the
actual outcome list. These encode the same successful sequential information, not two different
notions of trials.

Lean's WalletCount.real is tied to the actual owner queries on the same S/T tables and selected
source by stationary, finish_loop and completed_loop. survival proves the actual exhausted-prefix
probability `(1-p_U)^c`; capped_close bounds every after-cut continuation by that tail on nonempty
passing sets. Because p_U>0 there, the tail vanishes: this justifies the operational interpretation
of the unbounded law. No separate named Tendsto/uniqueness theorem is declared. When U is empty
the unbounded owner does not return; completion/fallback conventions are charged in the averaged
bound, not asserted to describe a real returned container.

Both systems preserve the actual source and table in the scored seed/pair game and the creation
refusal. Lean's transfer compares the whole count-indexed game, including arbitrary refusal
responses. EC's Rf has the same {-Gen} restriction as base Theorem5/W5. Its refusal-as-win
continuations are proof devices: setup_seed establishes the winning response's precondition,
and final adversary/events/budgets are not narrowed to that always-winning response.

Lean derives geometric-count distance through the ideal-rate denominator and averages true
passing-set moments, including S collisions, to obtain2^-120. EC uses a sharper average deviation
and an internal finite cutoff: slack2^-138 absorbs both2^-256 cutoff tails. Both final inequalities
retain exactly one2^-120 addition and the original main terms/error terms. This asserts the
stated addend, not optimality of the constant.

All six Lean deterministic/randomized endpoints and the three EC final endpoints retain their
finite alphabet, independent-prior/table, program/losslessness and hard-budget premises. In
particular, the full passphrase alphabet is finite, including queried zero-prior labels; finite
support alone is not the same premise. Budgets hold for every revealed count/strategy. Neither
an expected query budget nor arbitrary physical execution is silently substituted.

Independent randomized strategies justify duration computed from the revealed transcript and
independent randomness through a common postprocessing kernel. The duration itself need not be
unconditionally independent of secrets/functions: its permitted transcript input already has a
small table/passphrase dependence, and the statistical error pays for it. Extra dependence on
password, function entries, rejected values or passphrase/phrase lengths is excluded. Measured
wall-clock time is not automatically such a synthetic observation.

The general2^-136*n, workers and a capped search exposing attempts remain outside the final formal
endpoints. A fixed-table cutoff-law lemma is not a final capped source-game security theorem.
The general scheduling countermodel above does not apply to the actual first-pass sequential
interfaces. Restrict the new coin condition to the disclosure extension; hidden-trial uniform
selection can remain valid with weaker coins because no count is exposed.""", "",
          "## Executed checks", "", """Direct Lean source compilation writes freshlib under ignored evidence and excludes the old
project build directory from LEAN_PATH, reusing only pinned external dependencies. A dependency
DAG admits two independent source jobs within the measured machine-wide budget. The exact42
modules are replayed via the installed Lean replayFromImports API and the retained sequential
adapter; requested/observed success markers agree. Both the package's namespace gate and a
broader source-module-origin inventory run. The extra inventory names are listed in JSON; seven
are ProofInventory metaprogram declarations and one is PMF.filter.congr_simp.

Every EasyCrypt source is compiled as the main root with -no-eco, the pinned main executable and
Why3 configuration. Existing/generated .eco caches are forbidden, sources are checked for admit
or weak-proof pragmas, and no cached proof is used. The checker self-test rejects compiler failure,
a weak-cache false theorem, and the uncached false theorem, then accepts a true theorem. Lean
controls reject an unused axiom, sorry and native_decide with their actual expected markers.

Initial KnownPair.ec:365 twice returned `cannot prove goal (strict)` under a shared approximately
3GiB/two-CPU scope. The first run also omitted the prover-bin PATH; correcting PATH alone did not
remove the failure. After Lean's source/kernel work completed, the same unmodified proof passed
under a4GiB/five-CPU scope, with unchanged prover configuration/timeouts. All later roots passed.
The precise cause is not asserted beyond that observed resource/configuration sensitivity.
Successful earlier strict roots were reused only after rehashing all85 inputs; both initial
failed summaries/command logs remain retained. A failed SMT attempt is not evidence of a false
theorem, and the final pass does not erase the earlier reproducibility limitation.

All sustained jobs use measured machine-wide admission with at least5% physical RAM reserve,
MemorySwapMax=0, dynamic CPU budgets and five-second pressure sampling. The special thermal-board
rule does not apply to this machine. No cryptographic parameters were reduced. Lean4.35.0 and
13 pinned Git dependencies are recorded; all dependency HEADs match and tracked trees are clean.
EasyCrypt main ce19cb6, Why3 and prover identities/config hashes are recorded. Release r2026.10
identities are inventoried as context, not claimed as a second fresh23-file run.""", "",
          table(["Verification", "Result"], [["Fresh Lean sources / kernel", "42/42 exit0 /42 exact markers, exit0"], ["Package inventory", "6185 declarations /4003 theorems /standard"], ["Broader origin inventory", "6193 declarations /4004 theorems /standard; no local axioms"], ["Lean negative controls", "3 rejected, each exit1+marker; runner exit0"], ["EasyCrypt roots", "23/23 strict final successes, with two earlier KnownPair failures retained"], ["EasyCrypt checker controls", "4 expected behaviors; runner exit0"]]), "",
          "### Commands and retained log identities", "",
          table(["Record", "UTC start", "Exit", "Seconds", "Log SHA-256"], [[r["name"], r["startedUtc"], r["exitCode"], r["elapsedSeconds"], r["logSha256"]] for r in commands]), ""]
    for r in commands:
        md += ["**" + r["name"] + "** — cwd `" + r["cwd"] + "`", "", "```text", shlex.join(r["command"]), "```", ""]
    md += ["Raw original logs, resource samples, inventories and command records are local-only in ignored AUD-016-evidence. Published path redaction never changes that evidence.", "",
           "## Recommended action on the open wording question", "", """Yes: make the three specification clarifications as a reviewed text-only change, using the
precise A.6 postprocessing condition rather than the looser per-trial exclusion. Also add the
explicit selection/scheduling-coin condition to the general disclosed-trials paragraph. These
are concrete coverage qualifications; they do not require altering the sequential proof bounds.

Use [the proposed replacements](AUD-016-harnesses/PROPOSED-WORDING.md), align the EasyCrypt README,
and refer other shorthand passages to the same central condition. Do not label the two existing
DESIGN-NOTES deterministic shorthands as independent secret-leak permissions: they are narrower,
while the README's omission of P/function dependence is the substantive overpermission.

For the checked sequential rule, a trial counter does not justify arbitrary real elapsed-time
display. Nor does it establish formal coverage of an implementation that combines a hard cutoff
with disclosed attempts. Keep those distinctions in publication text. Specification sources
remain untouched here; no approval to commit or publish is inferred from an audit request.""", "",
           table(["Finding ID", "Status", "Fix commit", "Verification commit", "Evidence"], [[r["id"], r["status"], "None", "None", r["evidence"]] for r in data["remediation"]]), "",
           "## Canonical32-check coverage ledger", "",
           table(["ID", "Task", "Disposition", "Scoped evidence / reason"], [[r["id"], r["title"], r["status"], r["scope"]] for r in applicability]), "",
           "## Limitations and unexecuted checks", "", *("- " + line for line in limitations), ""]
    for title, name in [("Independent Lean source review", "lean-review.md"), ("Independent EasyCrypt source review", "easycrypt-review.md"), ("Independent wording and documentation review", "wording-review.md")]:
        p = WORKSPACE / "tmp/trial-count-audit-2026-11-14" / name
        md += ["## Annex — " + title, "", "Embedded source-first supporting review; coordinator findings and fresh execution above govern the final verdict.", "", re.sub(r"^(#{1,4}) ", r"##\1 ", p.read_text(), flags=re.M), ""]
    md += ["## Frozen input manifest", "", table(["Workspace-relative input", "Bytes", "SHA-256"], [[r["path"], r["bytes"], r["sha256"]] for r in snapshot["files"]]), "",
           "## Final review record", "", "Pending independent review of this exact report/harness snapshot.", ""]
    def redact(value):
        return re.sub(r"/home/[^/\s]+/", "/home/user/", value)
    target = AUDITS / "AUD-016-2026-11-14.json"
    target.write_text(redact(json.dumps(data, indent=2)) + "\n")
    target.with_suffix(".md").write_text(redact("\n".join(md)))
    print({"findings": len(findings), "commands": len(commands), "markdownBytes": target.with_suffix(".md").stat().st_size})


if __name__ == "__main__":
    main()
