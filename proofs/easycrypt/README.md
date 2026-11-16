# Machine-checked proofs of the MHFE security bounds in EasyCrypt

This development proves in [EasyCrypt](https://github.com/EasyCrypt/easycrypt) the security results of
the MHFE supplement, `docs/DESIGN-NOTES.md` of the specification repository at commit `da3a733`
(SHA-256 `c9a2b818…4327`). Every numbered theorem, lemma, corollary and proposition of the Deniability
section and of appendix A has a formal statement here, proved with no `admit`. The statements are
about the ideal model of the text; "Where the formal statements differ from the text" lists every
place where a formal statement is narrower or weaker than a sentence of the text, or where a sentence
of the text has no formal statement.

A reader who wants to know whether the proofs hold does not need to read the 21,000 lines of
proof. It is enough to check three things, in this order:

1. the trusted base: what EasyCrypt itself and the solvers are trusted for ("What is trusted");
2. the statements: that each formal statement says what the text says ("How to read a statement",
   `INDEX.md` and the differences listed below);
3. the run: that the development compiles without `admit` ("Checking the proofs").

The proofs themselves need no review once these hold: EasyCrypt rejects a proof that does not
establish its statement.

## What is proved

The results are bounds in the random-oracle model: Argon2id, the salt hash, HMAC-SHA-256, the seed
function and the wallet functions are independent uniformly random functions, and an adversary is
any program that queries them within given budgets (counts of queries, repeated queries included).

| Result of the text | What it bounds | EasyCrypt statement | File |
| --- | --- | --- | --- |
| Lemmas 1-3 | the Feistel network is a permutation; its output is uniform | `invpermK`, `permK`, `lemma2`, `lemma3`, `enc_uniform` | `Model.ec` |
| Theorem 1 | honest and prepared disclosures have the same distribution, for random and for any fixed functions | `theorem1`, `theorem1_fixed` | `Deniability.ec` |
| Theorem 2 | the advantage of every adversary in telling them apart | `theorem2`, instances for suite 3 at 12 to 24 words and suite 4 at 12 to 21 words | `Deniability.ec`, `Instances.ec` |
| Theorem 3, Lemmas G1-G5, Corollaries G6, G7, G10, Remark G9 | guessing the password of one container | `theorem3`, `G1` … `G10` | `Chain.ec`, `OneContainer.ec` |
| Proposition G8 | a matching attack that nearly reaches Theorem 3 | `G8`, `G8_top`, `G8_bracket` | `OneContainer.ec` |
| Theorem 4, Lemmas K1-K4 | guessing the password from a known plaintext-ciphertext pair | `theorem4`, `K1` … `K4` | `KnownPair.ec`, `Delta2.ec`, `Theorem4.ec` |
| Proposition K5 | the matching attack on a known pair | `K5`, `K5_top`, `K5_bracket`, pair lemma `pairK` | `K5.ec` |
| Theorem 5, Lemmas W1-W4, the selection rules | recovering the seed or the password and passphrase of a wallet-checked phrase | `theorem5_seed`, `theorem5_pair`, `W1` … `W4`, `selection_eq` | `Passphrase.ec` … `Theorem5.ec` |
| A generation that stops at a limit and reports a failure | the same bounds, for every limit | `theorem5_seed_capped`, `theorem5_pair_capped` | `Selection.ec`, `Theorem5.ec` |
| Readings of Theorem 5 | uniform secrets (exact value of `top2`), a known passphrase, one cost budget | `top2_uniform_eq`, `top2_known`, `theorem5_cost`, `theorem5_cost_uniform` | `Theorem5.ec` |
| Corollaries W5, W6, Proposition W7 | the phrase itself; an ordinary 24-word phrase; the matching attack | `W5`, `W6_seed`, `W6_pair`, `W6_phrase`, `W7_seed`, `W7_pair`, `W7_bracket` | `W5W6.ec`, `W7.ec` |
| The number of trials (A.6, selection rule) | the sequential generation that reveals the outcomes of its trials, their number and a duration that depends only on these and on independent coins: Theorem 5 and Corollary W5 with `2^-120` added | `theorem5_seed_trials`, `theorem5_pair_trials`, `W5_trials`, `E_pU` | `PassRate.ec`, `TrialGames.ec`, `TrialCoupling.ec`, `TrialFake.ec`, `TrialCount.ec` |

`INDEX.md` lists every result of the text with all its formal statements and their lines (generated
from the sources).

## How to read a statement

Each bound is a lemma about the probability of an event in a game, for every adversary that keeps
its budgets. Theorem 3 (`OneContainer.ec`) is an example. The game draws the password, the source
and the container and lets the adversary guess:

```
module Setup0 = {
  proc run() : pw * state = {
    var p, e, hv, y;
    R.RO.init(); RG.RO.init();          (* A, B, H and G: fresh random functions *)
    p <$ dP;                            (* the password, with its distribution *)
    e <$ dent;                          (* the source entropy *)
    hv <@ RG.RO.get(e);                 (* its verifier *)
    x <- pack e hv.`1;
    y <@ Net(Ideal).enc(p, x);          (* the container *)
    ...
```

The adversary `A` is any module that satisfies two hypotheses of its section: it terminates
(`A_ll`), and on every run, for every implementation of the oracles, it makes at most `kA` Argon2id,
`qB` salt, `qH` mask and `qG` verifier queries (`A_bounded`):

```
declare axiom A_bounded (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A(CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG].
```

The statement is then the text's inequality, with `top` the ranked password mass and `eps3` its
error term:

```
lemma theorem3 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup0, Play(A)).main() @ &m : res] <= top (kA %/ 12 + 1) + eps3 kA qB qH qG.

op eps3 (kA qB qH qG : int) : real =
  (qG%r + qB%r + 12%r * p1 * kA%r + 66%r) / 2%r ^ 128 + qH%r / 2%r ^ 256.
```

The other results have the same shape. To check one, compare its game, its section hypotheses and its
inequality with the text; `DESIGN.md` explains how each part of the text is modelled.

## Where the formal statements differ from the text

No bound of the text is contradicted. The differences are of three kinds.

Narrower than the text:

- **Passphrases form a finite set.** The text allows a countable list `v_1, v_2, …`. The finite set
  can be as large as any implementation's input limit allows, but a distribution with infinite
  support is not covered.
- **Adversaries terminate.** Every adversary, and whatever the owner does after a refused creation,
  is a program that halts when its oracles do (`A_ll`, `Rf_ll` and the like). The text says "when
  the adversary halts"; a program that may run forever has no formal statement here.
- **One cost budget.** `theorem5_cost` states the main term as a number `T` that bounds
  `top2(m, n)` on every run within the budget. The text writes this term as an expectation over the
  game, which can be smaller. The reading for uniform secrets, `theorem5_cost_uniform`, is the
  text's.
- **Selection rules whose coins depend on the secrets or the functions.** Condition 2 of the
  selection rule asks for coins independent of the trial values given the secrets and the functions,
  so a rule's coins may depend on the password, the passphrase or the functions. `selection_eq` and
  the statements for every covered rule take a rule module that cannot read the secrets, the random
  oracles of the game or the trial values (`Rl <: RULE` with `Gen`, `Trials` and the oracles
  excluded), so its coins are independent of all of them. A rule whose coins depend on the secrets
  or the functions has no formal statement here.
- **The number of trials: the sequential rule only.** The text adds `2^-136·n` for any rule that
  meets the first three conditions of the selection rule and whose selection and scheduling of
  trials, the order in which they finish and the duration depend only on the outcomes and on one set
  of coins drawn independently of the secrets, the functions and the trial values, with `n` the
  expected number of trials when each passes with probability `2^-16`, and states
  `2^-120 + (w - 1)·2^-136` for `w` workers. Only the sequential rule of the specification is stated
  (`n = 2^16`, `2^-120`), whose selection, scheduling and finishing order depend on the outcomes
  alone: `GamePRO` and `Game5O` generate the phrase with `SeqU` and give the adversary the outcomes
  of all its trials. The coupling of the text is proved for the rule cut off after `2^80` trials
  (`cc_upto`, `cc_bad`); the difference from the uncut rule and the trials of the reduction that all
  fail cost `2^-256` each and are absorbed in the slack of `E_pU_tight` (`2^-136 - 2^-154`). A
  duration that depends only on the outcomes and on coins independent of the secrets, the functions
  and the trial values is something the adversary computes itself from the outcomes it receives and
  its own coins. The response after a refusal is any that Theorem 5 and Corollary W5 allow: the
  proof replaces it by one that always wins (`RwSeed`, `RwPair`, `Rw5`), which can only raise the
  probability. A rule that stops at a limit and also reveals its trials, which the text allows, is
  not stated.

Read through an interpretation that is not itself checked:

- **Phrases.** Sources are entropy values. The map from an entropy to its checksum-valid BIP39
  phrase is an abstract injection (`ph`, `phE`, `ent_of_phr`), realized in `Instances.ec` by
  synthetic encodings. No word list, checksum or parser is modelled, and neither is the
  normalization of passwords and passphrases.
- **Budgets on every run.** The budgets hold for every implementation of the oracles, not only for
  the random functions. `ASSUMPTIONS.md` explains why no adversary of the text is lost.
- **Batches (Corollary G7).** The formal adversary submits its Argon2id queries in batches and its
  other queries one at a time. A batch of any queries, as in the text, reduces to this by answering
  its Argon2id queries first, which the text names as its second route.
- **Inequality (2).** `averaging` is stated for the monitored lazy chains, so its right-hand side
  includes the event Early, which the text charges one step later. The exact comparison of the
  programmed and unprogrammed games is in the proof, not a named lemma.
- **Wallet records** of the deniability experiments are abstract distributions; the instances use a
  one-value record type, which shows that the hypotheses are consistent, nothing more.

Not results, and without a formal statement:

- the exclusion, since commit `3d88078`, of a phrase that must also meet another condition on the
  phrase alone (for example TON's mnemonic check), with its estimates: the formal generation draws
  every phrase by the selection rule alone, so the statements need no change;

- the remark that about six sequential calls suffice to filter a known pair;
- the heuristic estimates, numerical examples and open questions.

Three details of the matching attacks: their top forms assume that enough distinct passwords exist
(`m + 1 <= |Pw|`), which the text leaves implicit; their budgets are maxima over the runs; and the
attack of Corollary G10 still asks the verifier oracle once per candidate when the source has 24
words (`q_G <= m`), where an attack without these calls exists. When no decoy password has positive
probability, the prepared experiment of the simulation corollary is the empty sub-distribution, not
an explicit failure.

## What is trusted

- **EasyCrypt** (commit `ce19cb6` of its main branch, after release r2026.10): its core logic, the
  program logics (probabilistic relational, probabilistic and expectation Hoare logic) and its
  standard library, in particular the random-oracle theories (`PROM`, the eager form `FinEager`)
  and the expectation operator `Ep`.
- **The SMT solvers** behind `smt` steps, run through Why3 1.9.0: Alt-Ergo 2.6.5, Z3 5.4.1 and
  CVC5 1.4.2. A step counts as proved when one of them proves it. Unlike a proof assistant with a
  small kernel, EasyCrypt does not replay these steps as proof objects.
- **The assumptions of the model**, listed in `ASSUMPTIONS.md`. None states a security property or a
  bound: they fix types, widths and distributions of abstract theories (all realized by concrete bit
  strings in `Suite3.ec` and `Instances.ec`), or are the hypotheses of a section (budgets,
  termination), under which its lemmas hold for every adversary. Two stay assumptions: passwords and
  passphrases form finite sets with probability distributions.

A false `smt` step or a wrong proof is rejected. This was checked by negative controls: copies of a
file with one change that makes a statement false (half of `2^-128` in a potential, one `2^-256` too
few, a smaller error term), each of which EasyCrypt rejects inside the changed proof.

## Checking the proofs

Install EasyCrypt at commit `ce19cb6` with Why3 1.9.0 and the three provers above (EasyCrypt's own
instructions), then let EasyCrypt find the provers and list them:

```sh
easycrypt why3config
easycrypt config
```

Check every source:

```sh
./check.sh
```

The script compiles each file of `src/` as the main input, in strict mode and with all configured
provers, stops at the first failure with a nonzero status and names the file. Arguments are passed
to `easycrypt compile`, and `EASYCRYPT` names another executable.

The script does not start when `src/` holds a compiled cache (`*.eco`). EasyCrypt accepts an
up-to-date cache without checking the proofs again, with `-no-eco` too, and whether a strict or a
weak check wrote it; so a cache next to a source would turn the check into no check. Remove such
files and run the script again. It also refuses a source that holds `admit` or a weak-check pragma.

One `smt` step, in `src/KnownPair.ec` at line 365, depends on the resources of the run: with the
default time limit it failed in two full runs of the check on 2026-11-16
(`cannot prove goal (strict)`) and passed when the file was checked alone, and audit AUD-016 saw it
fail and pass in the same way. A larger limit does not weaken the check, which still requires every
goal to be proved:

```sh
./check.sh -timeout 20
```

gives every `smt` step 20 seconds.

`./check-selftest.sh` tests the script itself on four synthetic cases: a failing compiler, a false
theorem with a cache from a weak check, the same theorem without the cache, and a true theorem.

The development was also compiled with release r2026.10 (Why3 1.8.2, Alt-Ergo 2.6.4, Z3 5.3.1, CVC5
1.4.2).

## What is not proved

- Real costs. The bounds count queries to ideal functions. They say nothing about the time or memory
  of real Argon2id or PBKDF2, or about how many queries an attacker can afford.
- The implementation. The proofs are about the algorithm of the specification, not about the `mhfe`
  program or any other code; side channels and the generation of randomness are outside them.
- Heuristic estimates, numerical examples and open questions of the text, which are not results.
- What the section above lists as narrower than the text.

## Relation to the Lean development

The same results were also formalized in Lean 4 (Mathlib, VCVio), as a separate development in
another proof system. The two are not blind replications of each other: the author of this
development had reviewed the model, the games and the statements of the Lean development before
writing it and consulted the Lean development while writing it (`SCOPE.md`). Its structure and
proofs are its own. The two were compared result by result and agree on every bound
([`docs/verification/COMPARISON.md`](../../docs/verification/COMPARISON.md)). The comparison led to
nine corrections of the text, all in the specification since commit `98620cc`: two state sharper
bounds (the loss of Proposition K5 and the seed-query budget of Corollary W5), and the others make
sentences say exactly what is proved, name a second proof route and allow a limit on the generation.
The two later commits up to `3d88078` let the wallet-check profile reveal the number of its trials
and exclude phrases with another condition; the statements of the number of trials were added to
this development for them (`TrialCount.ec`). The commits `33dba0f` and `da3a733` then state when the
trials may be revealed and ask for the coins of a selection rule to be independent of the trial
values given the secrets and the functions; no statement changed. That the rules here cannot read
the secrets or the functions, while the text lets their coins depend on them (the former wording did
too), is now listed above as narrower than the text.

## Files

| File | Contents |
| --- | --- |
| `src/*.ec` | the development: 23 files; `DESIGN.md` describes each |
| `check.sh`, `check-selftest.sh` | the check of all sources, and the test of that check |
| `INDEX.md` | every result of the text with its formal statements |
| `ASSUMPTIONS.md` | every axiom and section hypothesis, with its meaning |
| `SCOPE.md` | the results in scope and the modelling decisions |
| `DESIGN.md` | how the text maps to EasyCrypt |
| `tools/make_index.py` | writes `INDEX.md` from `src/` |
| `SHA256SUMS` | the SHA-256 of every source; from `src/`: `sha256sum -c ../SHA256SUMS` |
