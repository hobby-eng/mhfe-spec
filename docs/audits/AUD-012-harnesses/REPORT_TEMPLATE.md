# AUD-012 — Lean proofs: validity, exact correspondence and publication readiness

## Assessment

All 39 current mathematical chapters and the package entry point passed fresh direct-source
checking. The resulting 40 module artifacts passed separate kernel replay. The checkpoint found
6,036 local mathematical declarations, including 3,888 theorems, whose transitive axioms are only
`propext`, `Classical.choice` and `Quot.sound`. No false final numerical inequality was identified
under the statements' actual hypotheses. The new K5 loss and W5 generation-budget exception agree
with the current text.

**Literal full correspondence to the unrestricted specification is not established.** In particular,
the final Theorem 2 game restricts genuine-wallet records more than the specification and the
EasyCrypt experiment. Main Theorem 5 genuinely supports an arbitrary passphrase PMF, but final
W5/W6/W7 endpoints still require finite passphrase alphabets. Several exact ancillary statements
also remain unassembled or informally interpreted. These are distinguished from false checked
theorems throughout this report.

**Publication recommendation:** correct the kernel-check loop and the scope/trust descriptions
before publication. Extend the deniability game if the claim is the full experiment of the text;
otherwise identify the narrower formal experiment explicitly. The current evidence supports useful
checked formal results with stated boundaries. No proof, specification, dependency or workflow was
changed, and no commit, push or release was made.

## Record metadata

- Audit ID: AUD-012; repository sequence number 12.
- Completed UTC: {{COMPLETED_UTC}}.
- Reviewer: Codex coordinator with three distinct read-only specialist scopes and skeptical
  cross-checks. Exact model identifier/reasoning effort are unrecorded and remain null in JSON.
- Specification commit: `98620cce3d75a011e751cb2d3c1c315b7c23669d`.
- Reviewed publication port: machine-local `tmp/lean-review-2026-11-11/port-v4.35/`, denoted `<L>`.
  It is a pre-existing artifact outside the specification Git tree, not a new checkout.
- Source fingerprint: `{{SOURCE_FINGERPRINT}}`.
- Normative README SHA-256: `debbc9169b1a792f4f46f98de6d328672643183f07c430a12629d5e90a49f485`.
- Supplement SHA-256: `50affa7d36c43e10af0cff1e6aabaeb304cf3838e081bcb1317575bc94026346`.
- Source: 39 chapter files, 33,150 chapter lines, plus the package entry file and project metadata.
- Reviewed sources were rehashed before report assembly and remained unchanged. Only audit
  reports, harnesses and the audit index were added/edited in the specification repository.

The package README pins supplement commit `6161a3f`, whose stated hash is correct. This audit
compares against current HEAD, including the subsequent G7 explanation and capped-generation
guidance. The latter has no separate final no-container inheritance theorem in this port.

The proof-oriented report layout is authorized by the owner. Numbering, categorized immutable
finding IDs, English prose, paired JSON, evidence, hashes and privacy remain as prescribed by
the workspace audit standard. Shared coding/audit guides were not edited. All four procedure
hashes are retained below. Application/browser checklists are classified as outside this
proof-only scope rather than silently counted as executed.

## Scope and method

Reviewed: Deniability and appendix A, every numbered theorem/lemma/corollary/proposition, actual
oracle/game definitions, success events, hypotheses, query counters, source generation, refusal,
matching attacks, cost and selection consequences, concrete bit layouts, dependency pins,
axiom inventory, proof-check commands and publication claims. The detailed annexes supply exact
source/text references and distinguish direct formal statements from consequences requiring a
separate mathematical assembly.

Specialists performed their initial Lean source reviews without relying on previous L1–L5
reviews or the old `LEAN-COMPARISON.md`. Their prospective discrepancies received independent
challenges. The coordinator inspected the final statements and critical definitions and ran all
compilation/kernel/evidence checks. This is not an independent handwritten derivation of every
auxiliary tactic step, nor a proof that the model describes concrete primitives securely.

The actual model uses total VCVio `OracleComp` programs with hard transcript budgets and explicit
independent PMF mixtures of strategies. The source includes randomized endpoints; private coins
are not absent. A general semantics-preserving lift from arbitrary partially terminating
operational algorithms is not exported. The secure claim here is about the represented programs,
not arbitrary executable adversary binaries. Entropy, state, salts, keys, seeds and check widths
are the real stated widths, not reduced toy parameters.

Excluded: concrete Argon2id/BLAKE2b/HMAC/PBKDF2 security, physical memory/time lower bounds,
real randomness, side channels, Rust/browser implementation correctness, production vectors and
full release reproducibility. Lean's own kernel/compiler implementation and every upstream
library internals were not audited. The existing comparison is assessed separately after this
audit; it was not accepted as proof evidence.

## Trust and actual checking path

Toolchain: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
VCVio: `87bc1892fff1982e97cfd8c7303c9d1f2bfdc2f9`; Mathlib:
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All 13 dependency HEADs match the full revisions
in `lake-manifest.json`; their tracked working trees were clean at inspection.

Each source was elaborated directly with its real path and root into a new ignored `freshlib/`.
That path precedes dependencies in `LEAN_PATH`; the old project's `.lake/build/lib/lean` was
removed from the import search. Every local dependency was built first. No source tree was copied.
The final checkpoint was executed with the evidence directory as cwd, so its relative JSON output
does not overwrite the author's existing inventory. `lake build` is reported separately as
ordinary package usability/incremental-build evidence; `--no-cache` does not itself force a rebuild.

The official checker's `replayFromImports` then replayed each freshly generated module, including
the package entry. Six modules used individual `leanchecker` CLI commands; the remaining 34 used
that same installed function in a sequential audited wrapper. This is a separate kernel-replay
phase, not a second independently implemented proof logic.
Imported dependency proof implementations were not independently rebuilt/replayed in their entirety;
the transitive axiom check covers assumptions used by all local mathematical roots.

`Checkpoint.lean` selects all `MhfeLean.` and `_private.MhfeLean.` declarations, including unused
local mathematical helpers. It checks kernel registration, rejects local axioms and traverses
their transitive dependencies, rejecting every axiom outside the three allowed logical axioms.
Its inventory metaprogram lives in a separate `ProofInventory` namespace and is not counted as
a mathematical root. Static source review found no active `sorry`, local `axiom`, unsafe proof
override or native proof tactic in the reviewed chapters.

Three separate synthetic controls introduce an unused local axiom, a theorem using `sorry`,
and a true theorem proved by native evaluation. The actual checkpoint rejects each at its
axiom gate. These probes are outside the reviewed source and are never accepted mathematical
proofs of the development. Their actual status/message records are listed below.

The [Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
describe native-proof axiom changes. In this toolchain native evaluation creates a dedicated
`_native...ax` declaration; the README's blanket statement that it appears as `Lean.ofReduceBool`
is outdated. The complete allowlist rejects either form, so this wording error does not weaken
the current check. The trusted core remains Lean's kernel and the permitted logical axioms;
successful native-code execution alone is not treated as proof acceptance.

The machine has about 15.3 GiB physical RAM and no swap. Available physical memory was sampled
before every admission and at least every five seconds, including other processes. A dynamic
cgroup cap leaves at least 5% plus admission headroom; worker threads derive from that budget.
The board is another model, so the workspace rule specific to `NP950QED-KA2DE` does not apply.
The implementation still contains that model-specific thermal guard. Jobs were sequential within
this phase, with logs/checkpoints retained. No fixed lifetime heavy-check lock was used, and no
protocol parameter was reduced.

Initial small cgroup limits caused avoidable file-cache pressure on a later module: the measured
scope had about 145 MiB anonymous memory but over 1.5 GiB file charges and repeated limit hits.
The physical machine still had over 2 GiB available. A separate bounded headroom controller raised
only this audit's cache-dominated scopes using current charges plus globally available memory,
minus the 5% reserve and another 256 MiB. Each adjustment is retained. This corrected resource
accounting, not proof logic; original slow-run durations and logs were preserved.

The principal command forms are:

```sh
LEAN_PATH=<freshlib>:<dependency-libraries>:<Lean-library> \
lean -j<JOBS> --root=<L> -o <freshlib>/<Module>.olean <L>/<Module>.lean
LEAN_PATH=<same-fresh-path> leanchecker MhfeLean.Chapters.<Chapter>
# Remaining exact modules: an audited #eval wrapper invokes replayFromImports in sequence.
```

The toolchain bin directory is first on PATH. Each command runs in a bounded systemd user scope.
Exact argument vectors, UTC start/end, exit statuses and log hashes are retained in ignored,
**machine-local** `AUD-012-evidence/`. They are not public downloadable evidence files.

The original per-file replay was deliberately interrupted after six successes. Inspection of
the pinned CLI showed that a target is also a module-name prefix: `MhfeLean` would select every
descendant again, and repeated commands also rescan dependency paths. The unfinished
`ChainCompletion` command's termination status 241 and the explicit stop record are retained as
orchestration history, not a mathematical rejection. It was included in the successful remaining
list. The wrapper calls the identical official `replayFromImports`: it reads all module-data
parts, takes the most-private constant map, imports dependencies and calls kernel replay. A
`REPLAY_OK` marker is printed only after each successful return; the completed CLI set plus
those markers covers all 40 source modules exactly once for acceptance.

## Finding register

| ID | Category | Severity | Status | Publication implication |
| --- | --- | --- | --- | --- |
| AUD-012-FUN001 | FUN | Medium | Open | Full deniability-game equivalence needs a broader record kernel or an explicit narrower scope. |
| AUD-012-BLD001 | BLD | Medium | Open | The documented kernel loop can mask every failure with exit 0. |
| AUD-012-DOC001 | DOC | Low | Open | Exact-coverage claims need finite-domain and missing-assembly qualifications. |
| AUD-012-DOC002 | DOC | Low | Open | Native-proof axiom description is outdated for the pinned toolchain. |

These findings do not assert a false checked final inequality or a successful attack on MHFE.
The unqualified independence wording also repeats the provenance ambiguity already recorded as
AUD-011-DOC002; that original ID is retained rather than assigning another one here.

