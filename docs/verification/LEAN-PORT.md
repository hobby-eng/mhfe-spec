# Port of the MHFE Lean development to Lean 4.35

> Published in the specification repository on 2026-11-16. Paths in this document are those of the
> machine-local working copies in which the work was done: `tmp/easycrypt-mhfe-2026-11-09/` is now
> [`proofs/easycrypt/`](../../proofs/easycrypt), `tmp/lean-review-2026-11-11/port-v4.35/` is
> [`proofs/lean/`](../../proofs/lean), `tmp/code-proof-mhfe-core-2026-11-12/` is
> [`proofs/code/`](../../proofs/code), `LEAN-COMPARISON.md` is [`COMPARISON.md`](COMPARISON.md),
> `PORT-v4.35.md` is [`LEAN-PORT.md`](LEAN-PORT.md) and `review-2026-11-12/AUD-01N-remediation.md`
> (N = 1, 2, 3) is [`remediation/AUD-01N.md`](remediation/). The original Lean 4.28 development, its
> frozen copy (`snapshot/`), the other review records, the logs and tools under `tmp/` and
> `HANDOFF.md` are not published; line numbers given for the frozen copy refer to it, and the names
> are the same in `proofs/lean/`.

Date: 2026-11-12 (UTC). Source: the frozen copy `snapshot/` of Codex's development (39 files,
32,876 lines, written for Lean 4.28.0, Mathlib 8f9d9cff, VCVio e7f4c8d0). Port: `port-v4.35/`.
Full patch: `out-v4.35/port.patch`.

Revised on 2026-11-12 after the audits AUD-012 and AUD-013 of the specification repository: the
numbers of this page were regenerated, the limits of the header comparison are stated, and the
section "After the audits" describes what changed in the port.

Revised on 2026-11-13: the chapter `TrialCount` was added for the paragraph on the number of trials
that the specification added at commit `b155665` (section "Added on 2026-11-13").

## Result

| Check | Lean 4.28 rebuild (`out-v4.28/`) | Lean 4.35 port (`out-v4.35/`) |
| --- | --- | --- |
| Toolchain | Lean 4.28.0, Mathlib 8f9d9cff, VCVio e7f4c8d0 | Lean 4.35.0, Mathlib v4.35.0 (56a0058), VCVio 87bc189 |
| Modules compiled | 38 chapters of 38 | 38 chapters of 38, and the new `LegacyPMF` (below), `DeniabilityRecords` ("After the audits") and `TrialCount` ("Added on 2026-11-13") |
| Declarations in the inventory | 5,919 | 6,185 (6,056 before `TrialCount`, 6,036 before `DeniabilityRecords`) |
| Theorems in the inventory | 3,813 | 4,003 (3,904 before `TrialCount`, 3,888 before `DeniabilityRecords`) |
| Axioms of the whole development | `propext`, `Classical.choice`, `Quot.sound` | the same |
| `#print axioms` of the 71 main statements | 70 × the three, 1 × `propext`, `Quot.sound` | identical |
| Kernel replay of every module | lean4checker v4.28.0: all 38 chapters pass | leanchecker of Lean 4.35.0: all 41 chapters pass (`port-v4.35/check.sh`) |

The port changes proof scripts, not mathematics. The only changed statements are those of K5 and W5,
brought to the corrected text on purpose, and one chapter of new statements was added after the
audits (the sections on K5 and W5 and "After the audits"). Measured against the original sources:

- Declaration headers (name, binders, statement), compared as text by `tools/decls.py` and
  `tools/decldiff.py` (`out-v4.35/decls/`): 2,582 identical, 13 changed, 3 removed, 46 added (30
  before `DeniabilityRecords`, which adds 16).
  - Changed by the port: the instance `PassphraseRecoding.answers` states finite answer types per
    query, because VCVio removed the class it used (below). Its name did not change; the tool keys
    every instance by its header, so its old form counts as removed and its new form as added.
    `G10WalletCounts.crypto` renames a pattern variable from `query` to `point`, because `query`
    became ambiguous.
  - Changed to the corrected text: `K5.delta`, `K5.ranked`, `K5.weighted`, `K5.bound`,
    `K5.coarse_bound`, `K5.refused_bound`, `K5.refused_coarse` and `W5Generation.bound`,
    `W5Source.transfer`, `W5Source.bound`, `W5.bound`, `W5Randomized.bound`; removed `K5.delta_mono`
    and `K5.ranked_allowance`; added `W5Source.error` and `W5.error`.
  - Added: the helper laws listed below and the 14 declarations of `LegacyPMF.lean`.
  - The first version of `tools/decls.py` cut a header at the first `:=`, also inside a named
    argument such as `(N := N)`, so the conclusions of such statements were not compared. Since
    2026-11-12 it cuts at the first `:=` outside brackets and names anonymous instances by their
    header; the numbers above come from the corrected tool, and apart from K5 and W5 they confirm
    the earlier result.
  - What this comparison shows and what it does not. The tools compare the normalized text of each
    header. They do not compare the value of a definition, the fields of a structure, the equation
    clauses after the first, attributes and modifiers, or the `variable` lines that a declaration
    inherits, and they read strings and comments by simple patterns. Equal headers therefore do not
    prove equal elaborated types, and the numbers are evidence for the reading of the sources
    below, not a replacement of it.
- Changes that the header comparison cannot see, read in the sources:
  - `FiniteOracleViews` (PassphraseDomains) now assumes `[∀ t, Fintype (spec.Range t)]` instead of
    `[spec.Fintype]`. VCVio's former class had this family as its only field (through
    `PFunctor.Fintype`), so the two say the same; neither makes the passphrase alphabet finite.
  - Inside `namespace MhfeLean` the names `PMF.uniformOfFintype` and `PMF.uniformOfFinset` now
    resolve to the definitions of `LegacyPMF.lean`, which repeat the former Mathlib definitions
    (`PMF.ofFinset` with the same masses). The statement text is unchanged; the constants it names
    are new ones with the same meaning.
  - `ask` in `Gamma2Model` and `TranscriptErasure` is built on `OracleSpec.query` instead of
    `OracleQuery.query`: one query with the identity continuation, as before. The executor laws
    state the same answer and the same one-entry transcript.
  - Reducibility attributes on the oracle specifications, on `FiniteBits.fintype` and on
    `Mode.Value` change how terms unfold, not what they are.
  - `RoundRelabel.tableEquiv` proves its inverse laws differently; its two maps are unchanged.
  - `Checkpoint.report` collects the axioms through the public `collectAxioms` and writes its
    inventory to the working directory.
- Every theorem of the 4.28 inventory is present in the 4.35 inventory except two, removed on
  purpose with the enlargement of K5's loss: `K5.delta_mono` and the private
  `K5.ranked_allowance` (section "K5 and W5 brought to the corrected text"). The other names found
  only in one inventory are names Lean generates itself (`._proof_n`, `._simp_n`, `.eq_1`,
  `.toCtorIdx`, `._f`, `._abel_n`, `.congr_simp`, match splitters) and the added declarations.
- Size (`out-v4.35/port.patch`, regenerated on 2026-11-12 by `diff -ruN --exclude='*.md'` of the two
  `MhfeLean` folders; every added or removed line counts, blank ones included): 1,028 lines added
  and 384 removed in 38 files. Two of the files are new and account for 495 of the added lines:
  `LegacyPMF` (129) and `DeniabilityRecords` (366). Before `DeniabilityRecords` the same count gave
  661 and 384 in 37 files. The earlier figure of this page, 618 and 380, left out blank lines and
  preceded the change of the checkpoint's output path. The patch quotes one line of the original
  `Checkpoint.lean` with a path of the machine it was written on.

Time: the port itself took about 70 minutes of session time (2026-11-12 00:20 to 01:26 UTC),
after the toolchain and libraries had been installed; most of it went into diagnosing each new
kind of failure once, after which `tools/port-loop.sh` applied the mechanical fixes.

## Why the sources did not build, and what was changed

### 1. Library changes (names, definitions, classes)

| Change upstream | Fix in the port |
| --- | --- |
| Mathlib (2026-10-04) turned the uniform distributions `PMF.uniformOfFintype` and `PMF.uniformOfFinset` into measures; VCVio dropped its module `ToMathlib.General`. | New module `LegacyPMF.lean` defines both again as PMFs, exactly as the old Mathlib did (`PMF.ofFinset`), with the 12 lemmas the chapters use, in namespace `MhfeLean.PMF`. Inside `namespace MhfeLean` the name `PMF.uniformOfFintype` resolves to it, so no statement text changed. Credited to Mathlib 8f9d9cff and VCVio e7f4c8d0 (Apache 2.0). |
| VCVio: `OracleQuery.query` became `OracleSpec.query`; computations are built on `PolyFun` `FreeM`. | `ask` in `OracleModel` and `TranscriptErasure` uses `OracleSpec.query`. |
| VCVio removed the class `OracleSpec.Fintype`. | Ordinary hypotheses `∀ t, Fintype (spec.Range t)`, as VCVio now recommends. |
| VCVio's induction principle gives `liftM (query t) >>= next` instead of `query t >>= next`. | One proof (`WalletGenerationCompiler.execution`) restates its goal with `ask` on both sides. |
| VCVio exports `HasQuery.query`, which clashes with a local name in a pattern. | Pattern variable renamed. |
| Mathlib: `List.Sublist.cons₂` became `cons_cons`; `zero_le` takes its argument implicitly; `List.countP_cons` and `List.filterMap_cons` are no longer simp lemmas; `x >>= fun a => pure (f a)` is now simp-normalised to `f <$> x`; Mathlib now has its own `Fintype (BitVec n)`. | Renamed constructor; dropped the argument; the two list lemmas added to 29 simp calls; a transcript law for `<$>` (`WalletPairPort.transcript_map`); `FiniteBits.fintype` marked `@[instance_reducible]` so that it unfolds as before. |
| Lean: `CollectAxioms.collect` (used by `Checkpoint.lean`) became private. | `Checkpoint` uses the public `collectAxioms` and joins the results; it writes `checkpoint-inventory.json` to the working directory of the build, not to Codex's evidence folder. |

### 2. Stricter checking of implicit arguments (Lean versions after 4.28)

Lean now checks implicit arguments, instance arguments and metavariable assignments at a new
`.implicit` transparency, where ordinary definitions do not unfold. A term whose type is equal
only after unfolding a definition (for example the answer type `spec (.a p s)` against `Key`, or
`Mode.Value .wallet Check Data` against `Data`) is then rejected by `rw` and `simp`, although
`exact` still accepts it. Fixes:

- The oracle specifications (`Gamma2Model.spec`, `WalletGeneration.spec`, `DeniabilityModel.spec`
  and `combinedSpec`, `WalletData.walletSpec`, `WalletCollision.combinedSpec`,
  `SeedWalletModel.spec`) are `@[reducible]`; `W7OtherTests.Mode.Value` is
  `@[implicit_reducible]`.
- A typed `do` binding such as `let salt : Half ← ask (.b i x)` now instantiates the executor at
  the reduced type. The query law is stated again at these types:
  `Gamma2Model.execute_ask_a/b/h/g`, `DeniabilityModel.execute_ask_a/b/h/g`,
  `G10WalletAttack.execute_query_b/g` (each proved by the general law or `rfl`).
- Two structures whose proof fields were elaborated in unfolded form no longer match the general
  coercion lemma: `PassphraseWindow.baseEmbedding_apply` and `SelectionRules.relabel_apply`
  state their application by `rfl`.
- A few explicit implicit arguments, `change` steps and one `erw`.

### 3. Changed `simp` behaviour

- When `simp` unfolds a definition inside `decide p` or inside the condition of an `if`, the
  `Decidable` instance keeps its old type, and `decide_eq_true_eq`, `decide_eq_decide` or
  `Finset.mem_filter` no longer apply. Fix: remove `decide` first, unfold afterwards (simp calls
  split in two, or `unfold` and `rw`).
- `simp` no longer closes a goal whose two sides differ only in such instances: `rfl` added
  (6 places), and in counting proofs either `rfl` or a case split so that `omega` sees one atom.
- `simp` reports "no progress" and "no goals" as errors: `try` added (16 `dsimp`, a few others).
- `simpa … using h` that now fails was rewritten as `simp … at h ⊢` and `exact h`
  (48 places, by `tools/port-fix.py`).

### 4. One performance trap

`G9.state_mass` rewrote with `Fintype.card_prod` without naming the factors. On 4.35 the
unifier compared `BitVec 128` with the abbreviation `Half` by evaluating the cardinality, which
enumerates 2^128 values and exhausted memory (the chapter was killed at 6 GB). The fix names the
factors: `Fintype.card_prod Half Half`.

## Kernel replay

`tools/leanchecker-v4.35.sh` replays every declaration of every compiled module through Lean's
kernel, starting from the environment of its imports, with `leanchecker` (the successor of
lean4checker, shipped with the 4.35.0 toolchain). Results: `out-v4.35/leanchecker/summary.tsv`.

- `leanchecker` accepted all 39 modules (the 38 chapters and `LegacyPMF`) in 124 s. Since 2026-11-12
  the replay is the third step of `port-v4.35/check.sh`, which stops at the first module that the
  checker rejects; it accepts all 40 chapters ("After the audits"). The audit AUD-012 replayed the
  40 modules of its snapshot on its own, from files it had compiled itself.
- The toolchain also ships two independent checkers. `lean4lean` cannot read the toolchain's own
  compiled files (it reports "incompatible header" even for `Std.olean`), so its 39 runs in the
  summary fail before checking anything. `nanoda_bin` (an external checker written in Rust) reads
  export files written by `leanexport`; the export of the smallest module with its Mathlib
  dependencies is already 2.3 GB (148 s to write), so this check was not run. It remains possible
  if a check outside Lean's own kernel is wanted.

## What the port does not do

- It keeps the old discrete uniform distributions (`LegacyPMF`). Moving the statements to
  Mathlib's new measure-based uniform distributions would change statement text in 829 places
  and is a separate, larger task.
- It does not tidy the proofs: the `try` guards and the `simp … at h ⊢; exact h` pairs written
  by the script could be shortened by hand.
- Hopscotch, required but unused by the original, is not required by the 4.35 build.

## K5 and W5 brought to the corrected text (2026-11-12)

The specification now states a smaller loss in Proposition K5, `δ_K = 2^-128 + 11·2^-256` for every
`m`, and keeps `k_S` in `δ_gen` in Corollary W5 (`mhfe_spec` commit `6161a3f`). Codex's development
already proved the first per candidate (`K5Conditional.before_bound`) and then enlarged it to the
former `δ_K = 2^-128 + 11(m + 1)·2^-256`; for W5 it weakened the adversary's `k_S` seed calls to
`k_S + 1` before Lemma W2. In the port:

- `K5.delta` is the constant `1/2^128 + 11/2^256`; `K5.ranked` is the per-candidate bound itself,
  and `K5.bound`, `K5.coarse_bound`, `K5.refused_bound`, `K5.refused_coarse` state it. The
  enlargement (`delta_mono`, `ranked_allowance`) is gone.
- `W5Generation.bound` applies the generation coupling with the adversary's own `kS`;
  `W5Source.error` is `ε_W` with `kS + 1` everywhere except `W2.delta kS qT`, and `W5.bound`,
  `W5Randomized.bound` state `top2(kA/12, kS + 1) + W5.error … kS …` (`W5.error` adds the first
  creation refusal `2^-256`).
- Checks: the four affected modules rebuild, the inventory has 6,036 declarations and 3,888 theorems
  with the three standard axioms, the 71 `#print axioms` reports are identical to the earlier ones,
  and `leanchecker` accepts all 39 modules again. The sources before this change are in
  `out-v4.35/k5-w5/`.

## After the audits (2026-11-12)

The audit of the Lean development (AUD-012) and of the comparison and this page (AUD-013) found no
wrong bound. What changed in the port afterwards (record:
`review-2026-11-12/AUD-012-remediation.md`):

- `port-v4.35/check.sh` replaces the replay loop of the README, which returned success when a
  replay failed. It builds every module from its source, requires the inventory line of the
  checkpoint, replays each chapter through the kernel and stops at the first failure with a nonzero
  status. It does not start on top of an earlier build. `check-selftest.sh` tests it on five
  synthetic cases.
- New chapter `DeniabilityRecords.lean` (366 lines, 16 declarations, no change to any other
  chapter except its import line in `Checkpoint.lean`). `Theorem2Records.bound` and `.bits` are
  Theorem 2 for a real wallet whose record is drawn after the disclosed record and may depend on the
  container, the decoy password, the recovered decoy state and that record; the bound is unchanged.
  `Theorem2Records.independent` shows that the experiment of `Theorem2.bound` is a case of the new
  one, and `RecordOrder.independent_agreement` and `copied_agreement` show that the two orders of
  drawing give different joint laws of the two records.
- The README of the port lists where the formal statements are narrower than the text, what
  follows from them without being stated, and what is read through an unchecked interpretation; it
  names the axiom that `native_decide` adds in Lean 4.35 and no longer calls the EasyCrypt
  development independent.
- Checks: `check.sh` passes on a build from scratch (41 modules built, inventory
  `MHFE_COMPLETE_AXIOM_INVENTORY|6056|3904|standard`, 40 chapters replayed); three false variants of
  the new chapter are rejected inside the changed proofs (`review-2026-11-12/neg/`).

## Added on 2026-11-13

The specification's commit `b155665` lets the wallet-check generation reveal the pass/fail outcomes
of its trials, their number and a duration that depends only on these, at the cost of `2^-136·n`
added to every bound of Theorem 5 and Corollary W5 (`2^-120` for the sequential rule). The new
chapter `TrialCount` (1,333 lines) states and proves this for the sequential rule:
`Theorem5Trials.seed_bound`, `Theorem5Trials.pair_bound`, `W5Trials.bound`, and with private coins
`Theorem5TrialsRandomized.seed_bound`, `.pair_bound`, `W5TrialsRandomized.bound`. No existing
statement or proof changed; `Checkpoint.lean` imports the chapter. The README of the port cites the
specification at `3d88078` and lists what the chapter does not state (`w` workers, the general `n`).

- After the review of the same day (`review-2026-11-13/TRIALS-REVIEW.md`): `WalletCount.survival`
  and `WalletCount.capped_close` show that the loop cut off after `c` trials has a joint law within
  `(1 - p_U)^c` of `WalletCount.real`, and the README lists the finite passphrase alphabet of these
  theorems and what is not stated.
- Checks: `check.sh` passes on a build from scratch (inventory
  `MHFE_COMPLETE_AXIOM_INVENTORY|6185|4003|standard`, 41 chapters replayed;
  `tmp/publication-checks-2026-11-13/logs3/lean_check2.log`); `#print axioms` of the six final
  statements and of `completed_loop`, `capped_close`, `survival` and `gap_bound` gives the three
  standard axioms (`logs3/trials-axioms.txt`).

## Reproducing

```bash
cd tmp/lean-review-2026-11-11/port-v4.35
rm -rf .lake/build
LAKE=../tools/lake-v4.35.sh ./check.sh
```

`tools/lake-v4.35.sh` runs the `lake` of the local toolchain with a memory cap. The
chapter-by-chapter build of the port's first version is still available:

```bash
cd tmp/lean-review-2026-11-11
KEEP_GOING=1 python3 tools/rebuild.py 4.35.0 mhfe-review-v4.35 port-v4.35 out-v4.35
bash tools/leanchecker-v4.35.sh
```

The packages are in `workingspace/lean/packages/mhfe-review-v4.35` (manifest in
`build-v4.35/lake-manifest.json`), the toolchain in `workingspace/lean/lean-4.35.0-linux`.
