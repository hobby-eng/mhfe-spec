#!/usr/bin/env python3
"""Assemble the proof-audit record from retained local evidence and independent review notes."""

import collections
import datetime
import hashlib
import json
from pathlib import Path
import re
import shlex


HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
WORKSPACE = HERE.parents[3]
EVIDENCE = AUDITS / "AUD-014-evidence"
ARTIFACT = WORKSPACE / "tmp/code-proof-mhfe-core-2026-11-12"
NOTES = WORKSPACE / "tmp/code-proof-audit-2026-11-13"


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def private(value):
    """Redact published records only; original local evidence is left intact."""
    value = re.sub(r"/home/[^/\s]+/", "/home/user/", value)
    return re.sub(r"\b(all|All|both|Both|the|The|every|Every|only|Only|with|than|for|of|its)(?=\d)",
                  r"\1 ", value)


def table(headers, rows):
    def cell(value):
        return str(value).replace("|", "\\|").replace("\n", "<br>")
    return "\n".join(["| " + " | ".join(headers) + " |",
                      "| " + " | ".join("---" for _ in headers) + " |",
                      *("| " + " | ".join(map(cell, row)) + " |" for row in rows)])


def main():
    snapshot = read("snapshot.json")
    inventory = read("axiom-inventory.json")
    graph = read("module-graph.json")
    compilation = read("compile-summary.json")
    kernel = read("kernel-summary.json")
    environment = read("environment.json")
    context = read("model-context.json")
    dependencies = read("dependencies.json")
    expected = dict(re.findall(r"^'([^']+)' depends on axioms: \[([^]]*)\]$",
                               (ARTIFACT / "AXIOMS.txt").read_text(), re.M))
    actual = {row["name"]: row["axioms"] for row in inventory["theoremAxioms"]}
    named = []
    for path in sorted((ARTIFACT / "lean/MhfeCore/Proofs").glob("*.lean")):
        for match in re.finditer(r"^(?:@\[[^\n]*\]\s*)?theorem\s+(\S+)", path.read_text(), re.M):
            name = "MhfeProofs." + match.group(1)
            assert name in actual and actual[name] == expected[name].split(", ")
            named.append({"name": name, "file": path.name,
                          "line": path.read_text()[:match.start()].count("\n") + 1,
                          "axioms": actual[name]})
    assert len(named) == len(expected) == 135
    assert len(inventory["roots"]) == 2539 and len(inventory["theorems"]) == 1416
    assert len(compilation) == len(graph["order"]) == 28
    assert all(row["exitCode"] == 0 for row in compilation)
    assert kernel["requested"] == kernel["observed"] == graph["order"] and kernel["exitCode"] == 0
    classes = collections.Counter(tuple(row["axioms"]) for row in named)
    procedure = AUDITS / "AUD-011-evidence/procedure"
    procedure_hashes = {name: sha(procedure / name) for name in
                        ["FULL_AUDIT_GUIDE.md", "AUDIT_STANDARD.md", "AUDIT_TEMPLATE.md",
                         "audit-report.schema.json"]}
    findings = [
        {
            "id": "AUD-014-BLD001", "category": "BLD", "kind": "finding",
            "title": "The regeneration wrapper suppresses a failed translator and can publish partial outputs",
            "severity": "medium", "status": "open", "releaseBlocking": True,
            "blockingReason": "Blocks reliance on the advertised regeneration command as a fail-closed assurance gate; it does not invalidate the separately reproduced current mathematical artifact.",
            "affected": "Artifact tools/aeneas-std.sh:12-17; tools/splice.py:63-81,112-124; PROOF-README.md:139-140.",
            "reproduction": "Run AUD-014-harnesses/pipeline_probe.py with the actual two wrapper/splice scripts and the supplied synthetic translator. The translator emits minimal partial Funs/Types, reports an error and unconditionally exits7. The unmodified wrapper and splice return0 and create Code plus a new manifest.",
            "expected": "A nonzero translator status propagates and prevents downstream publication of a successful regeneration artifact/manifest. Full unfiltered diagnostics remain available.",
            "observed": "The pipeline ending in || true suppresses the actual Aeneas failure along with grep's no-match status. The complete wrapper returns0 after the translator's known exit7, with its error diagnostic present and synthetic Code created.",
            "impact": "A person or automation can mistake a failed/partial extraction for successful regeneration, especially when a new manifest is created from those partial files. Unsupported extraction input, interruption or output I/O failure are ordinary causes of a nonzero translator result. This is an assurance-procedure defect. The probe does not show that the full135-theorem suite accepts partial output, or that the current real translation is wrong.",
            "evidence": "pipeline-probe.json: translatorExit7, wrapperExit0, diagnosticSeen=true, downstreamCodeCreated=true; inner-log SHA256 822787ad77f087bc476b6d6163f2acabf86555630e9a50e9381e8f2c66b7a391. Independent read-only challenge confirmed actual script byte identity and the complete workflow witness. Real Charon and both real Aeneas replays separately exit0 and reproduce Funs/Types exactly.",
            "recommendedFix": "Capture the translator status without filtering it away, retain its full log, fail before splice on any translator failure, and keep an expected snapshot manifest separate from a newly generated manifest. Add the partial-output failure case to the regeneration command's regression controls.",
            "requiredVerification": "A translator failing before output and one failing after partial output both cause a nonzero wrapper exit and no successful downstream splice/publication. A diagnostic-free successful translator still passes; the real pinned extraction still reproduces the reviewed hashes and proof checks.",
            "rules": ["TOOL-02", "CORE-22", "CORE-28", "DOC-07"],
        },
        {
            "id": "AUD-014-DOC001", "category": "DOC", "kind": "finding",
            "title": "Six closure repairs contain handwritten adapters despite being described as type-only changes",
            "severity": "low", "status": "open", "releaseBlocking": False,
            "affected": "Artifact PROOF-README.md:88-90; REPORT.md:91; Assumptions/Translations.lean:338-501.",
            "reproduction": "Compare all eight R dictionary blocks with REPLACED-blocks.lean.txt and original Funs.lean, distinguishing an instance's method field from the generated lower-level method function it calls.",
            "expected": "The trusted-base description names every handwritten behavior adapter. Only changes that retain the actual dictionary method expression are called type-only.",
            "observed": "Six FnOnce/FnMut dictionary methods introduce new monadic lambdas: projection of (output,state), or reconstruction of (output,back newState). Only the two outer stack closures retain their direct generated method reference while changing the output codomain. The underlying generated method functions are retained unchanged.",
            "impact": "The public description understates the manual borrow/callback-state glue that must be trusted and reviewed. No wrong active-path adapter behavior, lost callback update or false checked theorem was found; the manifest already exposes the replacements.",
            "evidence": "Two source-first independent scopes confirmed the six adapters and two codomain repairs. Actual FnMut paths preserve the generated callback state; generated back functions here are identity. Exact full splice reconstruction gives156 E +10 T +8 R blocks.",
            "recommendedFix": "Describe six handwritten callback-entry/borrow-state adapters and two codomain repairs, delegating to unchanged generated method functions. Preserve the per-block Rust/generated references and hash manifest.",
            "requiredVerification": "Every one of the eight R blocks is classified correctly; trusted-base tables agree with Translations and the manifest. No numerical or theorem changes are needed for this documentation correction.",
            "rules": ["DOC-06", "DOC-07"],
        },
    ]
    # A separately challenged snapshot-description correction is appended only when
    # the corresponding retained note exists. It does not expand the proof target.
    snapshot_note = NOTES / "snapshot-scope-challenge.md"
    if snapshot_note.exists():
        findings.append({
            "id": "AUD-014-DOC002", "category": "DOC", "kind": "finding",
            "title": "The input table incorrectly says the newer specification changes no requirement",
            "severity": "low", "status": "open", "releaseBlocking": False,
            "affected": "Artifact PROOF-README.md:15; specification diff98620cc..3d88078 in README.md and docs/DESIGN-NOTES.md.",
            "reproduction": "Read the fetched origin/main diff against the explicitly proved specification commit98620cc. Compare the input-table parenthesis with the added disclosure permissions, leakage allowances and wallet-check restrictions.",
            "expected": "Keep the dated proof target98620cc and distinguish unchanged core cipher/vector bytes from later security-model and allowed-disclosure additions.",
            "observed": "The newer text permits qualified disclosure of generation trial outcomes/count and restricted duration, gives2^-136*n and2^-120 allowances, and adds phrase-filter restrictions/warnings. Calling this no requirement change is too broad even though the scoped cipher algorithm is unchanged.",
            "impact": "Readers may believe the old proof target automatically covers new generation-leakage and disclosure rules. This code proof supplies only a functional cipher-component bridge and does not audit or transfer those new bounds.",
            "evidence": "Read-only coordinator/specialist inspection of fetched specification diff; separate snapshot-scope-challenge.md. Current core arithmetic/domain/round rules used by the proof remain unchanged.",
            "recommendedFix": "State that the core cipher algorithm and vectors are unchanged, while the newer specification adds generation-disclosure/security qualifications not proved by this artifact. Retain exact target and newer revision hashes.",
            "requiredVerification": "The input table accurately summarizes both revisions and does not credit the code artifact with new leakage estimates or whole-game refinement. No proof-source change is necessary solely to correct this snapshot sentence.",
            "rules": ["DOC-06", "DOC-07"],
        })
    guide = (procedure / "FULL_AUDIT_GUIDE.md").read_text()
    tasks = re.findall(r"^### (CHECK-[A-Z]+-\d+) — (.+)$", guide, re.M)
    disposition = {
        "SEC-001": ("reviewed", "Value ownership/workspace/secret invariants and explicit OS/erasure boundary; not physical memory certification."),
        "SEC-002": ("not-applicable", "No browser Vault/CSP/sandbox surface in this proof artifact; OS protection is explicitly modeled."),
        "SEC-003": ("reviewed", "Audit extraction/build ran without network; no proof of application network-egress behavior is claimed."),
        "SEC-004": ("reviewed", "Cipher parameters/bytes/rounds and primitive contracts checked; primitive security and random-table sampling remain assumed."),
        "SEC-005": ("reviewed", "Logical wipe, recoverable errors, panic/divergence and callback branches checked; physical zeroization/drop effects excluded."),
        "SEC-006": ("not-applicable", "No browser injection/persistence API is part of the artifact."),
        "SEC-007": ("reviewed", "Fixed round bounds and input-before-work refusals checked; measured audit resources; no native cost/availability guarantee."),
        "FUN-001": ("reviewed", "Entropy packing/count/readings checked; actual BIP39/NFKD/PBKDF2 intentionally abstracted and excluded."),
        "FUN-002": ("not-applicable", "No HD or coin derivation code is verified here; wallet-check digest is handled separately."),
        "FUN-003": ("not-applicable", "No BIP85/BIP38/messages/Silent Payments subsystem in the artifact."),
        "FUN-004": ("not-applicable", "No descriptor/Miniscript/script/multisig subsystem."),
        "FUN-005": ("not-applicable", "No transaction or PSBT subsystem."),
        "FUN-006": ("reviewed", "Suite/count admission, exact recovery-length cascade, packing/readings and conditional round trip checked."),
        "FUN-007": ("reviewed", "The proof/refinement and axiom evidence assessed; no providers/discovery/accounting runtime is present."),
        "API-001": ("reviewed", "EngineComputes/EngineOk, external models, manual dictionaries, iterator/state contracts traced."),
        "API-002": ("reviewed", "FnMut state, callback order/Break branches inspected; full cancellation trace theorem absent; no async API."),
        "API-003": ("reviewed", "Formal exported endpoint scope and count checked; no monetary/export schema exists."),
        "API-004": ("reviewed", "BE32/byte-bit/order/domain/packing bridges checked; real word-text interoperability is external."),
        "BLD-001": ("reviewed", "Root import graph, extraction flags, two signature rewrites, opaque families and splice identity checked."),
        "BLD-002": ("reviewed", "Fresh28-module source/kernel checks and cached Lake usability; no native/WASM/clean-install matrix."),
        "BLD-003": ("reviewed", "Source hashes,16 dependency identities and tool binaries bound; no broad upstream/license certification."),
        "BLD-004": ("not-applicable", "No WASM/Docker release binary is produced or compared in this code-proof audit."),
        "BLD-005": ("reviewed", "Actual regeneration fail-open witness and successful direct regeneration; no remote CI/release execution."),
        "UI-001": ("not-applicable", "No rendered application or viewport in the proof artifact."),
        "UI-002": ("not-applicable", "No navigation/forms/browser state in the proof artifact."),
        "UI-003": ("not-applicable", "No user-facing secret/QR/accessibility UI in the proof artifact."),
        "ARC-001": ("reviewed", "Source→LLBC→generated/manual Code→byte spec→model ownership and trust seams mapped."),
        "ARC-002": ("reviewed", "Inactive raw templates/stub distinguished from the28 active modules; no proof credit for mere presence."),
        "ARC-003": ("reviewed", "Production source linkage, six adapters, manual bodies and11 exact kernel examples inspected."),
        "DOC-001": ("reviewed", "Every main advertised result compared with actual hypotheses, success behavior and exclusions."),
        "DOC-002": ("reviewed", "Commands/revisions/counts/trusted base checked; no publication license or clean-machine approval inferred."),
        "DOC-003": ("reviewed", "MD/JSON/schema/IDs/privacy/hash parity and final independent snapshot review required."),
    }
    applicability = [{"id": ident, "title": title, "status": disposition[ident.removeprefix("CHECK-")][0],
                      "evidenceOrReason": disposition[ident.removeprefix("CHECK-")][1]}
                     for ident, title in tasks]
    assert len(applicability) == 32
    commands = []
    for path in sorted(EVIDENCE.glob("*.command.json")):
        row = json.loads(path.read_text())
        log = path.with_name(path.name.replace(".command.json", ".log"))
        assert sha(log) == row["logSha256"], path
        commands.append({"name": path.name.removesuffix(".command.json"), **row})
    limitations = [
        "Hybrid extracted/manual value-model proof; no verified compiler or unmodified-Rust/native-binary equivalence theorem.",
        "Five functions, five helpers, six callback adapters and two codomain repairs remain handwritten trusted translation glue.",
        "Opaque primitives, Argon2id identity/parameters, actual BIP39/NFKD/PBKDF2, OS, allocator, zeroize/drop effects and native/WASM engines are not proved.",
        "Global EngineOk cannot be instantiated by the real native engine; successful native execution is not established even under a single valid-call resource assumption.",
        "The model bridge is pointwise functional equality, not a whole probabilistic game/query-budget/domain/error/record security transfer.",
        "WalletCheck covers digest/seed_passes only; full Seed wrappers and REC-3 host workflow are not proved.",
        "No complete callback cancellation trace or single public-call encrypt→decrypt→readings composition theorem is exported.",
        "Eleven kernel examples are not a full12-round concrete-primitive/public-vector replay.",
        "Dependency libraries were reused at pinned local revisions; no clean installation/cache download or whole upstream implementation audit.",
        "No Rust full suite, full-cost Argon2, WASM/browser/CLI/release artifact checks, remote CI, commit, push or source remediation.",
        "The dated specification target is98620cc; newer origin/main disclosure/leakage claims are not re-proved here.",
    ]
    report = {
        "schemaVersion": 1, "auditId": "AUD-014", "auditNumber": 14,
        "date": "2026-11-13", "completedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "title": "Rust-to-Lean code-proof validity, translation fidelity and specification correspondence audit",
        "reviewer": {"name": "Codex coordinator with three distinct read-only specialist scopes",
                     "model": None, "reasoningEffort": None},
        "snapshot": {"commit": snapshot["specCommit"], "commitComplete": True,
                     "workingTree": "Specification proof sources and authoritative core unchanged. Existing AUD-011/012/013 audit files/index preserved. Target artifact is machine-local and outside the repository Git tree.",
                     "coreCommit": snapshot["coreCommit"], "coreWorkingTree": "clean; equal to fetched origin/main",
                     "specOriginMain": environment["repositories"]["mhfe_spec"]["originMain"],
                     "sourceFingerprint": snapshot["inputFingerprint"], "inputManifest": snapshot,
                     "importedModelContext": context},
        "scope": {"included": ["All active28 Lean modules and135 named MhfeProofs theorems",
                               "Actual authoritative Rust, extraction harness/flags, generated output, manual translations/models and splice",
                               "Byte specification, actual API/callback/engine assumptions, success and refusal endpoints",
                               "Functional bridge to the prior Lean specification model and exact claim/trust-boundary review"],
                  "excluded": limitations},
        "procedureHashes": procedure_hashes,
        "checks": {"applicability": applicability, "commands": commands, "compilation": compilation,
                   "kernel": kernel, "inventory": {"roots": len(inventory["roots"]), "theorems": len(inventory["theorems"]),
                       "namedTheorems": named, "standardAxioms": inventory["axioms"], "localAxioms": inventory["localAxioms"]},
                   "controls": read("control-summary.json"), "charon": read("charon-result.json"),
                   "aeneasFromRetainedLLBC": read("aeneas-result.json"),
                   "aeneasFromFreshLLBC": read("fresh-aeneas-result.json"),
                   "llbcDifferences": read("llbc-differences.json"), "pipelineFailureWitness": read("pipeline-probe.json"),
                   "environment": environment, "dependencies": dependencies,
                   "provenance": read("provenance-result.json"),
                   "frozenInputsUnchanged": 116, "importedModelSourcesUnchangedAgainstAUD012": 22},
        "findings": findings, "observations": [],
        "remediation": [{"id": row["id"], "status": "open", "fixCommit": None,
                         "verificationCommit": None, "evidence": "Read-only audit; artifact/Rust/spec sources were not edited."}
                        for row in findings],
        "limitations": limitations,
        "verdict": "CHECKED_CONDITIONAL_FUNCTIONAL_PROOF_WITH_REGENERATION_AND_PUBLICATION_CORRECTIONS",
    }
    md = ["# AUD-014 — Rust-to-Lean code-proof audit", "", "## Assessment", "", """No false checked theorem or concrete mismatch in the reviewed valid-input cipher, packing and
recovery computations was identified. This is a substantial, useful **conditional functional
correctness proof of a hybrid extracted/hand-translated model**. The actual source→Charon→Aeneas
chain was rerun without network; fresh generated Types and Funs are byte-identical to the proof's
inputs. All28 active modules were freshly elaborated and independently replayed through Lean's
kernel. All135 named proof theorems have exactly the advertised standard-axiom closures.

This does not establish that every production Rust function, a native/WASM executable or the
whole utility is formally verified. The semantic correspondence of the manual translations,
external dependency models and compiler pipeline remains trusted. Actual Argon2id, BIP39 text and
seed derivation, OS/memory effects and complete probabilistic security-game transfer are outside
the checked result. These boundaries are detailed below, not inferred away from a clean axiom log.

**Publication recommendation:** keep the proof, correct the regeneration status handling and
the concrete documentation findings, and publish with its exact assumptions and exclusions.
The Medium finding blocks treating the advertised regeneration procedure as a reliable
fail-closed verification gate. It does not negate the independently successful regeneration or
the validity of the current Lean terms. Low wording findings do not independently block release.
No production/proof/specification correction was applied, and no commit or push was made.""", "", "## Record metadata", "",
          table(["Field", "Value"], [
              ["Audit / completion", "AUD-014 / " + report["completedUtc"] + " (UTC)"],
              ["Reviewer", report["reviewer"]["name"]],
              ["Exact model / reasoning effort", "Unknown / unknown; not inferred retrospectively"],
              ["Specification target / fetched newer main", snapshot["specCommit"] + " / " + report["snapshot"]["specOriginMain"]],
              ["Authoritative mhfe_core", snapshot["coreCommit"] + "; clean, equal to fetched origin/main"],
              ["Artifact", "tmp/code-proof-mhfe-core-2026-11-12/ (existing machine-local artifact, not a Git checkout in mhfe_spec)"],
              ["Frozen inputs", "116 files; fingerprint " + snapshot["inputFingerprint"]],
              ["Imported specification-model context", "22 reachable Lean sources unchanged against AUD-012; exact hashes in Annex F"],
              ["Working tree", report["snapshot"]["workingTree"]],
              ["Report pair / rerun tools", "[JSON](AUD-014-2026-11-13.json) / [harnesses](AUD-014-harnesses/README.md)"],
          ]), "", """The author supplied a progress summary and REPORT/PROOF-README. Specialist scopes first read
source, translations, model definitions and theorem bodies; only afterward were author claims
used as claims to verify. No prior author's assurance or build log substitutes for this audit's
execution. One coordinator owned execution; three non-overlapping read-only scopes covered
provenance/manual translations, byte/math/model bridges, and public API/recovery/success behavior.
Candidates were challenged across scopes, including the exact failing-wrapper witness and the
six callback adapters. Final report review is recorded separately after assembly.

This report continues the specification repository's proof-audit sequence because the proof
artifact has no publication repository. The actual implementation source is the clean authoritative
mhfe_core checkout above. It does not audit a stale copied implementation. Existing earlier audit
records are preserved; their model limitations are not silently closed by this functional proof.""", "", "## Procedure and scope", "",
          table(["Canonical procedure file", "SHA-256"], procedure_hashes.items()), "", """The canonical wallet-tools guide/standard/template/schema are the retained versioned procedure
copies used in AUD-011. Their32 CHECK identifiers are preserved in Annex A, with explicit scoped
evidence and individual not-applicable reasons. The owner authorized adapting the report's internal
sections to proof auditing. This changes presentation, not the severity/status/ID or evidence model.

The scope includes all active proof/model/code modules, real source-call paths needed for their
meaning, all manual replacements and opaque models, exact bytes/parameters/round and recovery
rules, toolchain provenance, regeneration and fresh proof validity. It excludes a fresh whole
Rust/CLI/browser/primitive/OS security audit. Scope is not expanded merely because an excluded
source file is linked into the harness or its generated name appears in Code.

The proof explicitly targets specification98620cc. Newer fetched main3d88078 preserves the scoped
cipher algorithm/vector bytes while adding generation-disclosure and security qualifications.
Its newly stated leakage allowances were not rederived or machine-checked by this code audit.
The existing later DeniabilityRecords chapter is not in this artifact's model-import graph and
receives no implementation-correspondence credit here.""", "", "## Findings and remediation register", "",
          table(["Finding ID", "Severity", "Status", "Release blocking", "Title"],
                [[r["id"], r["severity"].capitalize(), r["status"], "Yes, regeneration gate only" if r["releaseBlocking"] else "No", r["title"]] for r in findings]), ""]
    for row in findings:
        md += [f"### {row['id']} — {row['severity'].capitalize()} — {row['title']}", "",
               table(["Field", "Assessment"], [[key, row[field]] for key, field in [
                   ("Status", "status"), ("Affected", "affected"), ("Reproduction", "reproduction"),
                   ("Expected", "expected"), ("Observed", "observed"), ("Impact and limits", "impact"),
                   ("Evidence", "evidence"), ("Recommended fix", "recommendedFix"),
                   ("Required verification", "requiredVerification")]]), "",
               "Applicable rules: " + ", ".join(row["rules"]) + ".", ""]
    md += [table(["Finding ID", "Status", "Fix commit", "Verification commit", "Evidence"],
                 [[r["id"], r["status"], "None", "None", r["evidence"]] for r in report["remediation"]]), "",
           "## What the checked theorems mean", "", """The central chain is actual Rust source → a small signature-adjusted/opaque extraction harness →
Charon LLBC → Aeneas types and function bodies → exact splice with manual bodies → monadic
execution theorems → a byte specification → bit-vector Feistel and existing model ciphers.
Each arrow has a different assurance level; the kernel certifies only the Lean propositions
about the definitions presented to it.

The notation `f ⦃ r => P r ⦄` uses Aeneas total `WP.spec`/`DWP`: it excludes RustM panic/fail and
divergence. A returned Rust `Result::Err` or callback `Break` is still a normal returned value.
The base Feistel/Cipher theorems constrain a successful Continue result while allowing those
normal error/cancellation outcomes. They are not mere partial-correctness claims, nor do they
by themselves guarantee a container will be returned.

Success.lean adds real successful-return theorems. Under EngineComputes, EngineOk, continuing
callbacks and valid invariants, the round returns Ok, forward/inverse return the computed state,
and decryption of an admitted container returns a recovery. Encryption also requires that its
input is not a fixed point; the correct protocol behavior at a fixed point is refusal. An
abstract always-successful A engine can meet these premises, so these results are not globally
vacuous. An always-error engine is not a counterexample to them because it fails EngineOk.

EngineComputes is itself universal over engine states/inputs and demands return, allowing inner
Err and requiring the correct A key only on Ok. EngineOk is even stronger: every call on every
state/password/salt/memory/pass/key must succeed, including invalid or unreserved parameters.
The real native engine correctly rejects excessive memory requests and invalid parameters, so
it cannot satisfy this global contract. The Lean native placeholder always returns OutOfMemory.
Two fresh checked contract witnesses show that the placeholder satisfies EngineComputes for any
A and cannot satisfy EngineOk. Thus the generic success repair is real, but successful execution
of the native implementation has not been instantiated. A reachable-state/accepted-parameter
contract would be needed to prove that claim without demanding success on impossible requests.

Early suite/stated-length rejection and the suite4/24-word creation refusal need no engine
contract at all: they quantify over every engine, including one that diverges, because those
branches execute before engine work. This is stronger and should be credited separately.

WorkOk, SecretOk, PhraseOk and workspace geometry are explicit valid-input invariants. HostTotal
or CallbackTotal also requires callbacks to return. A summary saying no panic/always returns
from input validity alone must retain those dependency/callback conditions. Logical zero values
in into_state do not establish volatile physical erasure or absence of compiler/OS copies.""", "",
           "## Coverage and correspondence", "", """The specialist annexes below contain requirement-by-requirement and source/theorem-line tables.
Their principal conclusions are:

- Exact domain strings, no added NUL, twelve forward0..11/inverse11..0 rounds, correct geometry
  in both suites, correct entropy-field placement, BE32 serialization and MEM-level versus KiB
  distinction were checked. All valid work-factor arithmetic bounds fit U32.
- The salt is the first16 BLAKE2b bytes and the mask the first half-length HMAC bytes. The
  32-byte key's explicit64-byte padded block is correct under RFC2104 and the pinned HMAC crate;
  its internals/security remain outside Lean. No padding discrepancy was found.
- Workspace slice partitions, inverse reassembly, equal-length XOR/swap, engine mutation/error
  propagation and callback FnMut state were traced through the handwritten/generated callers.
- Packing uses the exact SHA-prefix verifier, length detection preserves [12,15,18,21] order,
  the nontrivial length cascade respects guard precedence, and both reading lists/verification
  flags and suite/count admission agree with the dated specification.
- Creation checks the computed container differs from X and its inverse equals X. The real
  English-word codec self-check is assumed by the synthetic Phrase encoding/read_text model.
- WalletCheck proves digest/seed_passes and its two-zero-byte predicate. Full Seed::derive/
  passes wrappers, NFKD/PBKDF2, generation/retries and evaluation on every24-word reading are
  not supplied as final code theorems.
- The roundtrip/original-reading facts are useful components. No single exported public-call
  Hoare theorem executes encrypt, decrypt and readings in sequence and concludes original
  membership. The same pure A contract across engine states/calls is required for composition.
- The byte/bit/model bridge is genuine pointwise functional equality for instantiated A/B/H
  tables and both suites, plus suite3 known-pair/finalize endpoints. It does not prove table
  sampling laws, full adversary/host observations, budget traces, domains, records or a transfer
  of all probabilistic security bounds to Rust. Conditional error selection also needs treatment
  before claiming equality of success-conditioned distributions.

The source-first reviews found no normal-path behavioral error in the five manual functions or
their active callback adapters. That is reviewed trusted correspondence, not a formal proof of
Rust semantics. All cryptographic and host-model exclusions are retained even when only Lean's
standard three logical axioms occur in the theorem closures.""", "",
           "## Executed verification and provenance", "", """All jobs used the installed pinned tools and existing dependencies. No package/toolchain was
downloaded or installed and no remote CI was dispatched. Real extraction and the ordinary Lake
build were run in a network namespace; Cargo extraction used --locked --offline and a separate
ignored target output directory, while reading the existing original harness in place.

Before and during sustained work, machine-wide MemAvailable was measured. Admission preserved
at least5% physical RAM; audit jobs used dynamic measured budgets, bounded systemd scopes,
MemorySwapMax=0 and five-second samples. The special thermal-board rule did not apply to this
machine. No full-cost Argon2 was needed or executed. Existing system swap occupancy was not
misreported as new swapping by this audit.

Fresh source elaboration writes separate freshlib artifacts and excludes this project's old
.lake/build/lib/lean from LEAN_PATH. External pinned dependency artifacts remain reused. The
root's actual transitive graph contains28 modules. Raw Funs/templates and the comment-only
ProofObligations stub are not secretly counted as verified obligations. Aeneas's actual generated
Code plus all active models/proofs/spec modules are checked. Kernel replay uses the installed
Lean replayFromImports API through the retained sequential adapter, checks all requested modules
in exact order and verifies the observed28 success markers; it is not the broken multi-argument
checker invocation identified in the earlier separate model audit.

The inventory selects declarations by active source-module origin, including Code/global
standard-library models, private declarations and helpers. It checks2539 declarations, including
1416 theorem constants after autogenerated helper/equation elaboration, and finds no local axiom
and only propext, Classical.choice and Quot.sound in closures. The135 explicitly named theorems
in Proofs have exactly113/all-three,14/propext+Quot.sound and8/propext-only closures, matching the
author's AXIOMS.txt. Three controls add an unused local axiom, sorry or native_decide: each actual
gate exits1 with its expected declaration/axiom marker. The control harness exits0 only when all
three are rejected. Opaque definitions/manual models are a semantic trusted boundary despite
this logical-axiom result. Local allowUnsafeReducibility changes four closure-alias transparency
settings; it is not credited as a proof bypass, and the actual resulting modules were replayed.

Ordinary `lake --no-cache build` reports3466 jobs and succeeds using existing built dependencies;
its3.786-second outer duration demonstrates local usability, not a full clean upstream rebuild.
The separate28-module fresh run is the proof-source freshness evidence. SpecTests contains11
kernel-produced exact examples (including one-round cases), not a twelve-round concrete-primitive
vector corpus. Anonymous examples are checked during source elaboration; the exported-constant
inventory is not described as persisting every anonymous example.""", "",
           table(["Check", "Observed result"], [
               ["Authoritative source/harness", "Clean core df7ea54;21 symlink entries; two rewritten files equal the six-pattern signature recipe"],
               ["Retained LLBC→pinned Aeneas", "exit0; Funs/Types byte-identical"],
               ["Current harness→pinned Charon", "exit0; has_errors=false; locked/offline"],
               ["Fresh LLBC→pinned Aeneas", "exit0; same original Funs/Types bytes"],
               ["LLBC comparison", "Three metadata differences only: output path plus two source-span deduplication references; raw JSON hashes differ"],
               ["Final splice", "164 extracted blocks;8 replaced;156 E +10 T +8 R =174 final blocks; entire Code reconstruction byte-identical"],
               ["Fresh active sources / exact kernel replay", "28/28 exit0 /28/28 markers, exit0"],
               ["Logical inventory / named proofs", "2539 declarations,1416 theorem constants,135 named; no local or prohibited axiom"],
               ["Verifier controls", "3/3 refused with exit1+marker; control harness exit0"],
               ["Engine contract witnesses", "2 Lean witnesses checked, exit0"],
               ["Cached ordinary Lake usability", "exit0,3466 jobs; dependency artifacts reused"],
               ["Wrapper failure probe", "Known translator exit7; real wrapper exit0 and real splice creates partial Code/manifest"],
               ["Final input drift", "116 frozen inputs and22 imported model sources unchanged; all16 dependency identities match"],
           ]), "", "### Interrupted and corrected audit attempts", "", """The initial Cipher compilation was stopped by the audit's own overly sensitive resource guard,
which interpreted a few background swap-ins, with no swap-out or memory PSI pressure, as sustained
pressure. The parent records exit75 and the stopped inner scope exit -15 (SIGTERM). The guard was corrected
to require swap-out or swap-in with actual memory-pressure stalls; the5% reserve and swap-free
audit scopes stayed in force. All116 frozen inputs were rehashed before reusing earlier successful
module outputs. Cipher was rerun successfully, followed by the remaining modules. Its valid
record is **compile-resume-MhfeCore.Proofs.Cipher**, not the stopped compile-Cipher attempt.

The first new inventory driver failed parsing because the local variable `name` was reserved
under imported syntax. Only the audit driver's variable was renamed to `declaration`; proof sources
and axiom rejection criteria were unchanged. Initial source/command/log artifacts are retained,
and the corrected inventory and all controls pass. Initial version discovery also tried unsupported
--version flags for Charon/Aeneas; corrected documented forms `charon version`/`aeneas -version`
return0. These tooling attempts are not concealed or counted as mathematical failures. They do
not justify saying every recorded audit command exited0.""", "",
           "### Tool and dependency identities", "",
           table(["Tool", "Version", "Binary SHA-256"], [[r["name"], r["versionOutput"].strip(), r["sha256"]] for r in environment["identities"]]), "",
           table(["Dependency", "Pinned/current identity"], [[r["name"], r.get("expected", r.get("manifestSha256"))] for r in dependencies]), "",
           "The15 Git dependencies have matching expected/current HEAD and no tracked modifications. The local MhfeLean path dependency is bound by its Lake manifest and the22 actual reachable source hashes; it is not called a clean Git dependency.", "",
           "### Actual commands and outcomes", "", """Commands below are retained argv records, not abbreviated claims. Paths are privacy-redacted
only in this published record. Raw original command/log/resource evidence stays in the ignored
local AUD-014-evidence directory. Inner systemd/Lean/Charon/Aeneas argv and wrapper commands are
both listed so failures, control exits and dependencies are reviewable. SHA256 identifies the
exact retained combined log; shell rendering is for reading, not an instruction to eval it.""", "",
           table(["Record", "UTC start", "Exit", "Seconds", "Log SHA-256"],
                 [[r["name"], r["startedUtc"], r["exitCode"], r["elapsedSeconds"], r["logSha256"]] for r in commands]), ""]
    for row in commands:
        md += ["**" + row["name"] + "** — cwd: `" + row["cwd"] + "`", "", "```text",
               shlex.join(row["command"]), "```", ""]
    md += ["## Optional improvements and next proof work", "", """These items describe stronger future results or simpler trust boundaries, separately from the
confirmed defects. They do not imply an existing theorem is false, and were not implemented.

1. Replace the global EngineOk/EngineComputes requirements by reachable-state, accepted-workfactor
   contracts, with a real engine implementation contract and explicit resource assumptions.
   Keep Argon2 settings unchanged. This makes native-success claims expressible without requiring
   success for invalid parameters or unreserved memory.
2. Add a BIP39 codec adequacy/refinement contract and prove its real implementation, then NFKD/
   UTF8 and Seed wrappers if wallet-check workflow coverage is wanted. A synthetic two-byte
   Phrase text codec cannot establish WRD/PCK/REC input-word requirements.
3. Export a composed public-call roundtrip/readings theorem and an explicit callback
   trace/stop-before-next-round theorem. Keep host workflow duties visible rather than infer
   them from the returned type alone.
4. Reduce the manual Rust→Lean boundary through behavior-preserving source refactors only in a
   separately authorized change. Until then, list the five functions, five helpers and all
   eight dictionary repairs exactly; maintain traceable source and output manifests.
5. Add a small full-twelve-round concrete-primitive vector sanity check to complement the
   universal functional proof. This checks adequacy of constants/model interpretation; it does
   not replace the proof or call for a full-cost vector campaign on each edit.
6. Treat implementation-to-security transfer as a separate refinement project: table laws,
   domains, adversary/host traces, budgets, errors/retries and final record experiments need
   matching premises/events. A pointwise permutation equality is one necessary component.
7. Adapt the artifact's resource helpers to current CORE-53 measured machine-wide admission,
   five-second pressure sampling and swap-free audit scopes rather than fixed10G/swap4G and
   a30-second conjunctive watchdog. This audit used its own measured guards; no proof defect is
   inferred from the author's historical resource script.
8. Keep the README no-panic, wallet-check and security-model summary sentences adjacent to
   their exact engine/callback/model hypotheses. A useful public claim is: the modeled
   generated/hand-translated cipher, packing and recovery core is totally correct relative to
   the byte specification under explicit dependency/engine/callback/valid-input contracts;
   success follows under the stronger success premises, subject to fixed-point refusal.

Publication packaging, a suitable license and a clean-machine dependency/bootstrap check remain
publication work. No evidence here establishes a fresh install or a native/WASM release build.
All limitations below remain operative even after the small wrapper/documentation corrections.""", "",
           "## Limitations and unexecuted checks", "", *("- " + line for line in limitations), "",
           "## Annex A — Canonical32-check applicability", "",
           table(["ID", "Canonical task", "Disposition", "Scoped evidence / reason"],
                 [[r["id"], r["title"], r["status"], r["evidenceOrReason"]] for r in applicability]), ""]
    for title, filename in [
        ("Annex B — Independent extraction, manual-translation and splice review", "provenance.md"),
        ("Annex C — Independent byte, round and mathematical-model review", "model-bridge.md"),
        ("Annex D — Independent API, recovery, creation and success review", "api-coverage.md"),
        ("Annex E.1 — Independent regeneration-failure challenge", "pipeline-challenge.md"),
        ("Annex E.2 — HMAC and engine-contract final challenge", "hmac-final-challenge.md"),
        ("Annex E.3 — Specification snapshot-description challenge", "snapshot-scope-challenge.md"),
    ]:
        path = NOTES / filename
        if path.exists():
            note = re.sub(r"^(#{1,5}) ", r"##\1 ", path.read_text(), flags=re.M)
            md += ["## " + title, "", "Retained read-only supporting review, embedded for a self-contained audit. Coordinator execution and findings above govern the final verdict.", "", note, ""]
    md += ["## Annex F — Frozen input and imported-model manifests", "",
           "Paths are workspace-relative. These hashes, not the name or modification time of a temporary directory, identify the actual reviewed snapshot.", "",
           table(["Frozen input", "Bytes", "SHA-256"], [[r["path"], r["bytes"], r["sha256"]] for r in snapshot["files"]]), "",
           table(["Imported model module", "SHA-256 (equal to AUD-012)"], [[r["module"], r["sha256"]] for r in context["files"]]), "",
           "## Annex G — Every named proof theorem and its checked logical axioms", "",
           "P = propext; C = Classical.choice; Q = Quot.sound. This135-row list is selected from actual source declarations including attributes, matched against the fresh module-origin inventory and AXIOMS.txt. Other generated/model theorem constants are included in the1416-total inventory, not miscounted as new named API results.", "",
           table(["Theorem (MhfeProofs)", "Proof source line", "Axioms"],
                 [[r["name"].removeprefix("MhfeProofs."), r["file"] + ":" + str(r["line"]),
                   ",".join({"propext": "P", "Classical.choice": "C", "Quot.sound": "Q"}[a] for a in r["axioms"])] for r in named]), "",
           "## Final review record", "", "Pending independent review of this exact report/harness snapshot. It is recorded after review; this placeholder must be replaced before completion.", ""]
    report_path = AUDITS / "AUD-014-2026-11-13.json"
    report_path.write_text(private(json.dumps(report, indent=2)) + "\n")
    report_path.with_suffix(".md").write_text(private("\n".join(md)))
    print(json.dumps({"findings": len(findings), "namedTheorems": len(named), "commands": len(commands),
                      "markdownBytes": report_path.with_suffix(".md").stat().st_size,
                      "axiomClasses": {",".join(k): v for k, v in classes.items()}}))


if __name__ == "__main__":
    main()
