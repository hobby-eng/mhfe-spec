# Machine-checked proofs of the MHFE security bounds in Lean 4

This development proves in [Lean 4](https://lean-lang.org) with Mathlib and VCVio the security
results of the MHFE supplement, `docs/DESIGN-NOTES.md` of the specification repository at commit
`da3a733` (SHA-256 `c9a2b818…4327`). Every numbered theorem, lemma, corollary and proposition of the
Deniability section and of appendix A has a formal statement here, proved with no `sorry` and no
axiom beyond Lean's three standard ones. The statements are about the ideal model of the text;
"Where the formal statements differ from the text" lists every place where a formal statement is
narrower than a sentence of the text, where a sentence follows from proved statements without being
stated itself, and where a sentence has no formal statement.

A reader who wants to know whether the proofs hold does not need to read the 34,850 lines of proof.
It is enough to check three things, in this order:

1. the trusted base: what Lean and the libraries are trusted for ("What is trusted");
2. the statements: that each formal statement says what the text says ("How to read a statement",
   the table of `MhfeLean/Chapters/README.md` and the differences listed below);
3. the run: that the development builds and uses only the standard axioms ("Checking the proofs").

The proofs themselves need no review once these hold: Lean's kernel rejects a proof that does not
establish its statement.

## What is proved

The results are bounds in the random-oracle model: Argon2id, the salt hash, HMAC-SHA-256, the seed
function and the wallet functions are independent uniformly random functions (tables drawn
uniformly), and an adversary is an oracle program within given budgets (counts of queries in its
transcript, repeated queries included). A program is total: it halts on every answer. A randomized
adversary is an independent mixture of such programs, each within the budgets, and has theorems of
its own. Probabilities are `ENNReal` values of discrete distributions (`PMF`).

| Result of the text | Lean statement | Chapter |
| --- | --- | --- |
| Lemmas 1-3, Theorem 1 | `Lemma1.consistency`, `Lemma2.uniform_and_independent`, `Lemma3.network_uniform`, `Theorem1Feistel.joint` | `Feistel` |
| Theorem 2, both suites | `Theorem2.bits`, `Theorem2.suite3_error`, `Theorem2.suite4_error` | `DeniabilityGames` |
| Theorem 2 with a real wallet whose record may depend on the disclosed decoy | `Theorem2Records.bits`, `Theorem2Records.independent` | `DeniabilityRecords` |
| Theorem 3 and G6 | `Theorem3.bound`, `G6.bound` | `ShortSources` |
| G7, G8, G10 | `G7.bound`, `G8.weighted`, `G8.coarse`, `G10.bound` | `BatchQueries`, `MatchingAttack`, `WalletData` |
| Theorem 4 | `Theorem4.bound` | `KnownPairBound` |
| Proposition K5 | `K5.bound`, `K5.coarse_bound`, `K5.budgets` | `KnownPairAttack` |
| Theorem 5 | `Theorem5.seed_bound`, `Theorem5.pair_bound`, and for any passphrase distribution `PassphraseRefusal.seed_bound`, `.pair_bound` | `WalletSource`, `PassphraseDomains` |
| Corollaries W5, W6 | `W5.bound`, `W6.seed_bound`, `W6.pair_bound`, `W6.source_bound` | `WalletRecovery`, `OrdinaryWallet` |
| Theorem 5 and Corollary W5 when the sequential generation reveals its number of trials | `Theorem5Trials.seed_bound`, `Theorem5Trials.pair_bound`, `W5Trials.bound`, and with private coins `Theorem5TrialsRandomized.seed_bound`, `.pair_bound`, `W5TrialsRandomized.bound` | `TrialCount` |
| Proposition W7 | `W7Source.seed_refused`, `W7PairSource.refused` | `WalletPairAttack` |
| Selection rules | `WalletSelection.chosen_eq`, `WalletSelection.actual_eq`, `SelectionRules.joint` | `SelectionRules` |

Every name starts with `MhfeLean.`. `MhfeLean/Chapters/README.md` lists every result of the text
with its chapter and entry points, the supporting lemmas, and a reading order. The development has
41 chapter files and about 34,850 lines; the inventory below counts 6,185 declarations, 4,003 of
them theorems.

## How to read a statement

Each bound is an inequality between the success probability of an experiment and the text's bound,
for every adversary that satisfies its hypotheses. Theorem 3 (`ShortSources.lean`) is an example:

```lean
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (entropy state input) = input.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : State → OracleComp (spec (Fin N) E) (Fin N))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (original state hash passwords adversary) true ≤ RankedMass.top passwords (kA/12+1) +
      (qG+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal)
```

- Everything before the colon is a hypothesis. `state` and `hash` fix the bit layout of a container
  and of a verifier hash; `passwords` is the password distribution, ranked (`sorted`) with largest
  probability at most `p1`.
- `adversary` is any oracle program that receives the container and outputs a password guess. The
  four budgets say that in every run, for every container and every table of answers, its
  transcript has at most `kA` Argon2id, `qB` salt, `qH` mask and `qG` verifier queries.
- `original state hash passwords adversary` is the experiment of the text (password, source and
  random functions drawn, container encrypted, adversary run); applied to `true` it is the
  probability that the guess is right. `RankedMass.top passwords n` is the mass of the `n` likeliest
  passwords. The right-hand side is the text's bound.

The other results have the same shape. To check one, compare its experiment, its hypotheses and its
inequality with the text.

## Where the formal statements differ from the text

No bound of the text is contradicted. The differences are of four kinds.

Narrower than the text:

- **Adversaries are total programs.** An adversary is an `OracleComp` program, which halts on every
  answer, or an independent mixture of such programs (`Theorem3Randomized.bound`,
  `Theorem4.randomized`, `Theorem2.averaged_bound` and the like). A mixture can run for an unbounded
  time over its support. No theorem turns an arbitrary probabilistic program that halts with
  probability one into such a mixture, and a program that may run forever has no formal statement.
  The text says "when the adversary halts".
- **Passphrases form a finite set in the corollaries.** Theorem 5 (a) and (b) hold for any
  distribution on any alphabet (`PassphraseRefusal.seed_bound`, `.pair_bound`), for a deterministic
  program. Corollaries W5 and W6, Proposition W7, the readings of Theorem 5, the theorems on the
  number of trials (`TrialCount`) and every theorem of appendix A.6 with private coins assume a
  finite passphrase alphabet.
- **The real wallet's record in Theorem 2.** In `Theorem2.bits` the record of the real wallet is
  drawn from the real password, the source and the tables, before the decoy is drawn. In
  `Theorem2Records.bits` it is drawn last, and may also depend on the container, the decoy password,
  the recovered decoy state and the disclosed record, which is the text's "used in any way";
  `Theorem2Records.independent` shows that the first experiment is a case of the second. In both,
  a record is fixed before the adversary runs: a record that changes while the adversary queries is
  not modelled.
- **Private coins are not stated for every form.** The forms with private coins are separate
  theorems. Corollary G7 and the checksum-aware G10 without refusal, Theorem 3, Corollary G6 and
  Theorem 4 with refusal, and Theorem 5 on an arbitrary passphrase alphabet have none. Each follows
  from the deterministic form by averaging over the coins.
- **One cost budget.** For uniform secrets the bound is a game statement (`FullCostBound.bound`,
  `FullCostFloor.bound`, `FullCostRandomized.bound`). For general secrets the text's
  `Exp[top2(|C'|, |Q_S|)]` is proved as the counting lemma `PairMass.adaptive` and is not assembled
  into a game statement.
- **The number of trials for the sequential rule only.** The text adds `2^-136·n` to every bound of
  Theorem 5 and Corollary W5 for a rule that meets the first three conditions of its selection rule
  and reveals the pass/fail outcomes of its trials, their number and a duration, if its selection
  and scheduling of trials, the order in which they finish and the duration depend only on the
  outcomes and on one set of coins drawn independently of the secrets, the functions and the trial
  values, where `n` is the expected number of trials at the pass rate `2^-16`. The formal statements
  cover the sequential rule (`n = 2^16`), whose selection, scheduling and finishing order depend on
  the outcomes alone, with `2^-120` added (`Theorem5Trials`, `W5Trials`); `w` workers, with
  `(w - 1)·2^-136` more, other rules, and a rule that stops at a limit and also reveals its trials
  have no formal statement. The adversary and the response after a refusal are families indexed by
  the number of failures, which gives the outcomes; a duration is the private coins of the
  randomized forms together with that number. The joint law of the number of failures and the
  selected value (`WalletCount.real`), on tables where a value passes, is unchanged by any prefix of
  actual trials (`WalletCount.completed_loop`), and the loop cut off after `c` trials, whatever it
  does after the cut-off, is within `(1 - p_U)^c` of it on every test (`WalletCount.capped_close`,
  `WalletCount.survival`): it is the law of the loop that runs until a pass. Where no value passes
  the loop does not stop, and an arbitrary fallback is defined, as for the selected value alone; the
  bound charges such tables in full, so the fallback does not matter.
- **A generation that stops at a limit and reports a failure** has no final statement. The laws of
  a search with a limit are proved (`WalletCapped`, `WalletUnbounded`); the text's sentence that
  every bound of Theorem 5 then holds, a failure counting as no win, is not a theorem here.

Follows from proved statements, and is not stated itself:

- **"The best adversary lies between"** after Propositions G8, K5 and W7. The lower bound of each
  attack, its budgets and the upper bound for every adversary are separate theorems. W7's final
  lower bounds take a list of `n + 1` distinct candidate pairs, and their `top2` forms
  (`W7Source.seed_top2`, `W7PairSource.top2`) assume that the chosen pairs have the mass
  `top2(m, n)`.
- **The fractional top `T(x)`.** Its formula, the upper bound for every admissible weighting
  (`FractionalMass.greedy`, `FractionalTop.bound`) and `T(1 + k_A/11) ≤ top(k_A/11 + 2)` are proved.
  That the bound is attained, `top(⌊x⌋) ≤ T(x)` and the form with `⌈x⌉` for every real `x` are not
  stated.
- **`top2` as a sum of the largest products.** For a finite passphrase alphabet the supremum is
  attained (`W1.top2_attained`). For a countable one `top2` is a supremum over finite sets of pairs,
  and its equality with the ranked sum is not stated.
- **The intermediate claims of Corollary G7** (Early for batches, Lemmas G2 and G3 for them). The
  final bound is proved by the text's second route: a batch program (`BatchProgram.Program`) is
  serialized with its Argon2id queries first, with the same result, answers and query counts
  (`BatchProgram.execution`).
- **Theorem 5 for a covered selection rule.** `WalletSelection.chosen_eq` and `actual_eq` prove that
  a covered rule gives the law of the sequential completion (`WalletCompletion.real`) and of the
  whole experiment with the adversary (`WalletUnbounded.real`), from which the game of Theorem 5
  draws. Theorem 5 is not stated again with a rule as a parameter. That the rule stops with
  probability one is a hypothesis. A policy may depend on the `S` and `T` tables at a fixed
  passphrase (`actual_eq`). `SelectionRules.joint` gives the joint law of a context and the selected
  entropy for a policy indexed by any context drawn from any prior, when a value passes in every
  context; no statement uses it, and none instantiates it with the game's prior, which would first
  have to be conditioned on a passing value, or connects it to the experiment of Theorem 5. So a
  rule whose coins depend on the password or on `A`, `B`, `H` or `Ω`, which the text's condition 2
  allows (coins independent of the trial values given the secrets and the functions), is covered
  only by that lemma.
- **Results on an unranked password alphabet.** The results are stated for passwords numbered in
  decreasing order of probability (`Fin N`). The relabeling of any finite alphabet is proved in
  general (`PasswordDomains.joint`, `.combined_execution`) and applied to Theorem 3
  (`PasswordDomains.theorem3`) only.

Read through an interpretation that is not itself checked:

- **Phrases.** A 24-word phrase is 24 groups of eleven bits, the entropy followed by checksum bits
  that are a parameter (`Lemma1.consistency`) or the leading bits of a `G` answer (the G10 forms).
  No word list, parser or SHA-256 is modelled, and neither is the normalization of passwords and
  passphrases. `PasswordDomains.admitted_finite` shows that the encodings of at most 1024 bytes
  form a finite set.
- **Two models.** Theorem 2 has a width-parametric model of its own (`DeniabilityModel`); the
  guessing bounds use the model of `OracleModel`. Both define the twelve-round network of the text;
  no lemma relates them.
- **Wallet records** are an abstract type with arbitrary distributions. The scenario `U` sees the
  disclosed phrase only. The real wallet's record may depend on the whole tables, which is more
  than any use of a wallet needs and costs the adversary's budgets nothing.
- **Refusal.** After a refused creation the experiment continues with an arbitrary response, which
  contains the text's redraw. The redraw loop is not built.

Not results, and without a formal statement:

- the remark that about six sequential calls suffice to filter a known pair;
- the example of TON's mnemonic check: a source that must also pass a check on the phrase alone is
  outside Theorem 5, and the formal source draws every phrase without such a condition;
- the heuristic estimates, numerical examples and open questions, among them the example of an
  ordinary source without wallet data in the readings of Theorem 5.

Two details of the lower bounds: `ENNReal` subtraction stops at zero, so where a bound of the text
is negative the formal one is zero, which is never weaker; and the matching attack on G10 that
derives the wallet data from the phrase asks `G` twice per candidate (`q_G ≤ 2m`), once for the
checksum.

## What is trusted

- **Lean 4.35.0** and its kernel, which checks every proof term.
- **The libraries**, pinned in `lake-manifest.json`: Mathlib `v4.35.0` (`56a0058`) for probability
  and real analysis, VCVio `87bc189` for oracle computations, and their dependencies. The
  development relies on their definitions, not on any unproved statement of theirs.
- **`MhfeLean/Chapters/LegacyPMF.lean`** restores two definitions that Mathlib replaced in 2026:
  the uniform distributions `PMF.uniformOfFintype` and `PMF.uniformOfFinset` as discrete
  distributions, exactly as Mathlib `8f9d9cff` defined them, with the lemmas the chapters use, all
  proved.
- **Three standard axioms**: `propext`, `Classical.choice` and `Quot.sound`. `Checkpoint.lean`
  collects the axioms that the declarations of the development depend on and fails on any other
  name. That excludes a `sorry` (the axiom `sorryAx`), an axiom declared by the development, and a
  proof by native evaluation: in Lean 4.35 each `native_decide` adds an axiom of its own, named
  after its theorem (`T._native.native_decide.ax_1_1` for a theorem `T`), where earlier versions
  used `Lean.ofReduceBool`.

Security assumptions and query budgets are hypotheses of the statements, not axioms.

## Checking the proofs

With [elan](https://github.com/leanprover/elan) installed, from this directory:

```sh
lake exe cache get     # Mathlib's compiled files; without it, Mathlib is compiled too (hours)
./check.sh
```

The script builds every module from its source, replays every compiled chapter through Lean's
kernel and stops at the first failure with a nonzero status that names the step. Its three steps:

1. `lake build`. Its last module, `MhfeLean/Chapters/Checkpoint.lean`, collects every declaration
   of the development with all its dependencies and fails if any of them is unchecked by the
   kernel, is an axiom of the development, or depends on an axiom other than the three above.
2. The build must print the inventory line

   ```
   MHFE_COMPLETE_AXIOM_INVENTORY|6185|4003|standard
   ```

   (declarations, theorems, standard axioms only). The full list is written to
   `checkpoint-inventory.json`.
3. `lake env leanchecker` on each chapter, one at a time: the kernel replays every declaration of
   the compiled file, independently of the elaborator that produced it. The entry file
   `MhfeLean.lean` only imports the chapters and declares nothing.

The script does not start when `.lake/build` already holds compiled modules of the development:
Lake keeps a compiled module whose source is unchanged, so a second run would not check the sources
again. Remove the folder and run the script again. `LAKE` names another `lake` executable.

`./check-selftest.sh` tests the script itself on a synthetic project with a stand-in for `lake`: a
failing build, a build without the inventory line, a module that the replay rejects, a leftover
build, and a run in which every step passes.

The axioms of a single result can be printed with `#print axioms MhfeLean.Theorem3.bound` in a file
that imports `MhfeLean`.

## What is not proved

- Real costs. The bounds count queries to ideal functions. They say nothing about the time or memory
  of real Argon2id or PBKDF2, or about how many queries an attacker can afford.
- The complete `mhfe` application. This development proves security bounds in the specification's
  ideal model. A [separate Lean proof of the `mhfe_core` code](../code/README.md) proves functional
  correctness of the translated cipher, packing and recovery core under its documented assumptions
  and trusted models. The CLI, browser integration, side channels and generation of randomness
  remain outside these proofs.
- Heuristic estimates, numerical examples and open questions of the text.
- What the section "Where the formal statements differ from the text" lists as narrower, as not
  stated, or as read through an interpretation.

## History and relation to EasyCrypt

The development was written by Codex (OpenAI) for Lean 4.28.0 and ported to Lean 4.35.0 with Claude
(Anthropic) on 2026-11-12. The later statements and chapters described here,
`MhfeLean/Chapters/LegacyPMF.lean` and the check scripts were also written with Claude. The port
changed proof scripts, one instance declaration (`PassphraseRecoding.answers`, because VCVio removed
the class it used) and the name of one pattern variable, and added `LegacyPMF.lean`; no statement of
a result changed. Afterwards the statements of Proposition K5 and Corollary W5 were brought to the
corrected text (a loss of `2^-128 + 11·2^-256` per wrong candidate in K5, and `k_S` in `δ_gen` in
W5), which the original proofs already contained per candidate and per step. The chapter
`DeniabilityRecords` was added on 2026-11-12, after a review had found that Theorem 2 fixed the real
wallet's record before the decoy. The chapter `TrialCount` was added on 2026-11-13 for the paragraph
on the number of trials, which the specification added at commit `b155665`; the README then moved to
commit `3d88078`, whose other change only excludes a phrase that must also pass another wallet's
check, and on 2026-11-15 to commit `da3a733`: the two commits up to it (`33dba0f`, `da3a733`) state
when the trials may be revealed and ask for the coins of a selection rule to be independent of the
trial values given the secrets and the functions, with no change to a statement.

The same results were also formalized in EasyCrypt, as a separate development in another proof
system. The two are not blind replications of each other: the author of the EasyCrypt development
had reviewed the model, the games and the statements of this one before writing it and consulted it
while writing. The two were compared result by result
([`docs/verification/COMPARISON.md`](../../docs/verification/COMPARISON.md)). They give the same
numerical bounds, each under its own hypotheses; their experiments and domains differ in the places
that the two READMEs list, so the agreement is one of bounds and not an identity of theorems. The
comparison led to nine corrections of the text, all in the specification since commit `98620cc`.
