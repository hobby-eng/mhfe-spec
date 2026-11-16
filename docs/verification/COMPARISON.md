# Two machine-checked formalizations of the MHFE security proofs: EasyCrypt and Lean 4 compared

Written 2026-11-11 (UTC). Paths are relative to the workspace root.

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

- Text: `mhfe_spec/docs/DESIGN-NOTES.md`, SHA-256
  `c5f1afdbc83479121e6cf8f6328e2f8a641682fe7372792fe821681edb64caee`.
- EasyCrypt development: `tmp/easycrypt-mhfe-2026-11-09/src/`, 18 files, 19,402 lines.
- Lean development: `tmp/mhfe-lean-setup-2026-11-08/MhfeLean/`, accepted state of
  2026-11-09T19:44Z, 39 files, 32,876 lines; frozen copy with checksums in
  `tmp/lean-review-2026-11-11/`.

Revised 2026-11-12 (UTC) after three audits of the specification repository: AUD-011 (the EasyCrypt
development), AUD-012 (the Lean development) and AUD-013 (this comparison). Sections 1 to 11 keep
the counts, times and line numbers of 2026-11-11, which describe the states above. What changed
since is in the table below and in the passages that carry a date.

| | State compared on 2026-11-11 | State on 2026-11-12 |
| --- | --- | --- |
| Text | `DESIGN-NOTES.md`, SHA-256 `c5f1afdb…caee` | commit `98620cc`, SHA-256 `50affa7d…6346`: the nine corrections of appendix B applied |
| EasyCrypt | 18 files, 19,402 lines | 18 files, 19,475 lines (`SHA256SUMS`): K5 and W5 at the corrected text, the exact `top2` for uniform secrets, Theorem 5 for a generation that stops at a limit, `check.sh` |
| Lean, the author's sources | Lean 4.28.0, 39 files, 32,876 lines | unchanged; they state the former K5 and W5 |
| Lean, the port | none | `tmp/lean-review-2026-11-11/port-v4.35/`, Lean 4.35.0, 41 files, 33,520 lines: K5 and W5 at the corrected text, the chapter `DeniabilityRecords`, `check.sh` |

Revised again 2026-11-13 (UTC) for the specification at commit `3d88078`. Its commit `b155665` adds
to the selection rule of A.6 a paragraph on the number of trials: a generation may reveal the
pass/fail outcomes of its trials, their number and a duration that depends only on these, at the
cost of `2^-136·n` added to every bound of Theorem 5 and Corollary W5, `2^-120` for the sequential
rule. Its commit `3d88078` excludes a phrase that must also pass another wallet's check, which adds
no result. Both developments now state the number of trials for the sequential rule (section 5.10).

| | State on 2026-11-13 |
| --- | --- |
| Text | commit `3d88078`, SHA-256 `dbfa0746…d65f` |
| EasyCrypt | 23 files, 21,479 lines (`SHA256SUMS`): the number of trials in `PassRate.ec`, `TrialGames.ec`, `TrialCoupling.ec`, `TrialFake.ec`, `TrialCount.ec` |
| Lean, the port | 42 files, 34,854 lines, 6,185 declarations of which 4,003 theorems: the number of trials in the chapter `TrialCount` |

Revised 2026-11-15 (UTC) for the specification at commit `da3a733` (`DESIGN-NOTES.md`, SHA-256
`c9a2b818…4327`); the developments are unchanged. Its commit `33dba0f` states the condition of the
paragraph on the number of trials: the selection and scheduling of the trials, the order in which
they finish and the duration depend only on the outcomes and on one set of coins drawn independently
of the secrets, the functions and the trial values. A rule that stops at the first or the second
pass according to a bit of the password meets the first three conditions, but the number of passes
shows the bit. In both developments the sequential rule selects, schedules and finishes its trials
by the outcomes alone; the coins of a duration are the adversary's own in EasyCrypt and the private
coins of the randomized forms in Lean. Its commit `da3a733` asks for the coins of a selection rule
to be independent of the trial values given the secrets and the functions; the former wording,
independent of the trial values, allowed a coin equal to a bit of the password XOR a bit of a trial
value, which is independent of the trial values when that password bit is uniform. Both developments
modelled a stronger condition, so neither could expose the gap, and neither README listed this
narrowing at `3d88078`. `da3a733` also drops a sentence of the supplement's security summary, which
changes no result. Section 4.7 compares the coins that the rules of the two developments may use.

## Abstract

The MHFE supplement proves, in an ideal model, two kinds of statements about a memory-hard Feistel
encryption of BIP39 mnemonics: that a disclosed decoy is distributed as an honest wallet, and that
recovering the password or the source costs a number of Argon2id evaluations close to the best
dictionary attack. The proofs were formalized twice, by two different AI coding agents working in
two unrelated proof systems: in Lean 4 with Mathlib and VCVio, checked by Lean's kernel, and in
EasyCrypt, with probabilistic relational and expectation logics and SMT solvers. This report
compares the two developments: how each models the ideal functions, the adversary and the games;
what each statement says, result by result; how each proof goes; what each covers beyond or short of
the text; how large each is; and what has to be trusted. Both developments have a formal statement
for every numbered result of the text, with the text's constants, and neither found a result of the
text to be false. The statements agree on the bounds, each under its own hypotheses. They are not
the same theorems: the developments differ in the domains of the secrets, in what an adversary is,
in the form of its budgets, in the record of the real wallet in Theorem 2, in the treatment of the
source generation, in the arithmetic of lower bounds and in a number of statements that only one of
them has (section 6). Both were checked by others than their authors: the Lean development was
rebuilt from source and replayed through Lean's kernel, the statements of each were compared with
the text by five reviewers, with no blocker found, and three audits on 2026-11-12 checked each
development and this comparison (section 8). The comparison also records what the formalizations
found in the text, with the corrections that the text has since received.

## 1. Introduction

MHFE encrypts a BIP39 mnemonic under a password into another valid mnemonic with a twelve-round
Feistel network whose round function runs Argon2id. Its design notes contain a supplement of proofs
in an ideal model, in which Argon2id and HMAC are independent uniform functions and an attacker is
bounded only by the number of its queries. The supplement is long (about 1,300 lines of proofs), its
bounds have many terms, and several of its arguments are delicate: resampling a whole table after
programming a few points, a stopping-time argument for queries made out of order, an averaging over
eleven round positions, a rejection loop whose rejected trials must stay hidden. A second pair of
eyes was wanted, and a machine-checked proof is the strongest form of one.

Two formalizations were made. The first, in Lean 4, was written by Codex; the second, in EasyCrypt,
by Claude. They were made one after the other and are not independent: the author of the EasyCrypt
development had reviewed the model, the games and the statements of the Lean development before
starting and consulted it while writing, and both formalize the same text. Their structure and their
proofs were developed separately, in systems that share no code and little method.

This report answers five questions.

1. Do the two developments prove the same statements, and are these the statements of the text?
2. Where they differ, which difference is a matter of form and which changes the claim?
3. How do the proofs differ, and what does each system make easy or hard?
4. What must a reader trust in each case, and what was checked independently?
5. What did the formalizations find in the text?

Section 2 lists the results of the text. Section 3 gives the two developments at a glance. Section 4
compares the models, section 5 the statements and proofs result by result, section 6 the coverage.
Sections 7 and 8 compare size and trust. Section 9 lists what was found, section 10 the limits of
this comparison, and section 11 concludes. The appendices hold the table of correspondences, the
proposed corrections to the text and the instructions for rechecking.

## 2. The text

All results are in the ideal model of the supplement's section A.1: a password `P` drawn from a
distribution with ranked probabilities `p_1 >= p_2 >= ...`, independent uniform functions `A`
(Argon2id, from a password and a 128-bit salt to a 256-bit key), `B` (the salt of a round), `H` (the
128-bit mask of a round, from a key) and `G` (a 256-bit hash of the entropy), twelve Feistel rounds
on a 256-bit state, and an adversary limited to `k_A` queries of `A`, `q_B` of `B`, `q_H` of `H`,
`q_G` of `G`. `top(m) = p_1 + ... + p_m` is the success of the best dictionary attack with `m`
tries.

| Group | Results | Main statement |
| --- | --- | --- |
| Deniability | Lemmas 1-3, Theorem 1, Theorem 2, a corollary on simulation, suite 4 forms | Theorem 1: for a 24-word source the disclosed view has exactly the distribution of an honest one. Theorem 2: for every source length the advantage is at most `(k + 2) p_1 + l 2^-ENT + (12 q + 146) 2^-256`. |
| One container (A.2-A.4) | Theorem 3 with Lemmas G1-G5; Corollaries G6, G7, G10; Remark G9; Proposition G8 | `Pr[win] <= top(k_A/12 + 1) + (q_G + q_B + 12 p_1 k_A + 66)/2^128 + q_H/2^256`; G8: a matching attack reaches `top(m + 1)(1 - m δ)`. |
| A known pair (A.5) | Theorem 4 with Lemmas K1-K4; Proposition K5 | `Pr[win] <= T(1 + k_A/11) + (24 p_1 k_A + 2 q_B + 419)/2^128 + (2 q_H + 12)/2^256`, with `T` the fractional top. |
| A 24-word source with a passphrase and the wallet check (A.6) | Theorem 5 with Lemmas W1-W4; Corollaries W5, W6; Proposition W7; the selection-rule paragraph; three readings | seed recovery at most `top2(k_A/12, k_S) + ε_W + 2^-512`, pair recovery at most `min{top2(k_A/12 + 1, k_S + 1), top2(k_A/12, k_S) + p_1 s_1} + ε_W`, with `ε_W = (s_1 k_S + q_B + (1 + 12 p_1) k_A + 66)/2^128 + (q_H + k_A)/2^256 + (q_T + q_Ω)/2^512 + δ_gen + 2^-256` and `δ_gen = 2^18 (k_S + 1)/2^256 + 2^18 q_T/2^512`. |

The text marks heuristic estimates, numerical examples and open questions as such; neither
development formalizes them.

## 3. The two developments at a glance

| | EasyCrypt | Lean 4 |
| --- | --- | --- |
| Written by | Claude (an AI coding agent) | Codex (an AI coding agent) |
| Written | 2026-11-09 to 2026-11-11 | accepted 2026-11-08; regrouped and shortened 2026-11-09 |
| System | EasyCrypt, `main` at ce19cb6 and release r2026.10 | Lean 4.28.0 |
| Libraries | EasyCrypt's standard library (`PROM`, `Distr`, `FinType`, `Xreal`) | Mathlib (8f9d9cff), VCVio (e7f4c8d0) |
| Proofs checked by | EasyCrypt's tactic engine, Why3 and three SMT solvers (Alt-Ergo, Z3, CVC5) | Lean's kernel |
| Files | 18 | 39 (37 chapters, one inventory, one root) |
| Lines | 19,402 (16,989 of code, 928 of comments) | 32,876 |
| Proved statements | 1,039 (`lemma`, `equiv`, `hoare`, `phoare`, `ehoare`; local ones included) | 1,416 `theorem` declarations |
| Definitions | 295 operators, 270 modules (games, oracles, wrappers) | 875 `def`, 209 `abbrev`, 20 structures, 10 inductive types, 66 instances |
| Lines of proof scripts | 10,677 | about 12,000 (measured on the 34,243-line state) |
| Axioms | parameters of abstract theories, all realized by instances; finite password and passphrase types with a distribution | `propext`, `Classical.choice`, `Quot.sound` |
| Hypotheses of the statements | budgets on every run, for every implementation of the oracles; termination of the adversary and of what follows a refusal | budgets in every execution, for every table; passwords ranked on a finite alphabet; a finite passphrase alphabet outside Theorem 5; programs are total by construction |
| `admit` / `sorry` | none | none |
| Time of a full check | 373 s on `main`, 468 s on the release (six cores) | 257 s of compiler time (the author's record) |

The counts of the Lean development come from a textual inventory of its declarations
(`tmp/lean-review-2026-11-11/tools/decls.py`); the counts of the EasyCrypt development from its
sources. The two line counts are not directly comparable: the systems differ in how much one line
says. Section 7 looks at this.

## 4. Models

### 4.1 Programs and probabilities

EasyCrypt is built for games. A game is a module with procedures in a small imperative language
with random sampling; its semantics is a distribution on memories, and `Pr[G.main() @ &m : E]` is
the probability of an event of the final memory. Three logics relate programs: Hoare logic for
properties that always hold (the budgets), probabilistic relational Hoare logic for the equivalence
of two games, and an expectation logic (`ehoare`) in which a potential function is carried through a
program. The EasyCrypt development uses all three; its hardest bounds (G3, G4, K3, the Cross event,
W4 and the matching attacks) are expectation-logic proofs.

Lean has no built-in notion of a game. The Lean development builds on Mathlib's `PMF` and on VCVio's
`OracleComp`, a free monad of oracle queries. An adversary is a function from the container to an
`OracleComp` program; `execute tables program` runs it against fixed tables and returns the result
with the log of queries; a game is a `PMF` obtained by binding uniform tables and secrets and
mapping the execution; the success probability is that `PMF` applied to `true`. The tables of the
ideal functions range over finite types, so most probabilistic steps are statements about finite
sums. The mixtures over strategies, the record distributions of the deniability games and the
passphrase distributions of Theorem 5 are general `PMF`s, with infinite sums and, for the
passphrases, a limit over a vanishing tail.

The consequence for the proofs is large. EasyCrypt's relational logic turns "these two games behave
alike until a bad event" into one tactic application whose side conditions are equalities of
variables. In Lean the same step is an explicit bijection or coupling between two finite
probability spaces, stated and proved by hand. Conversely, a counting argument on a finite set is
native in Lean and laborious in EasyCrypt.

### 4.2 The ideal functions

The text's functions are independent and uniform. The Lean development samples them as whole tables
before the game starts, one table for each of `A`, `B`, `H` and `G` (and `S`, `T`, `Ω` in A.6), and
the adversary reads the tables through its queries.

The EasyCrypt development models `A`, `B` and `H` as one lazily sampled random oracle on a sum type
of query points; each answer is a triple (key, salt, mask) of which each function reads its own
component. Since the three functions have disjoint domains, this is the same as three independent
functions, and it makes "a table hit" one test instead of three. `G`, `S`, `T`, `Ω` and the record
oracle are separate lazy oracles. Where a proof needs the functions fixed in advance (Lemmas G1, K1
and W3, Theorem 1, the matching attacks), the library's theorem that a lazy oracle on a finite
domain equals a function sampled as a whole (`PROM.FinEager`) switches between the two views.

The two choices are equivalent; they shift the work. With eager tables, "this point is still
uniform given everything the adversary has seen" must be proved as a resampling lemma about tables
(the Lean development has a chapter of such lemmas); with a lazy oracle it is the definition, and
what must be proved instead is that the game can be rearranged so that the point is sampled late.

### 4.3 The adversary and its budgets

In EasyCrypt an adversary is an abstract module: any program with access to the oracles and to its
own memory, including its own random choices. A budget is a Hoare judgment about a counting wrapper:
for every implementation of the oracles, a run that starts with the counters at zero ends with them
within the budget. Termination is a second hypothesis (the adversary halts whenever its oracles do).
Module restrictions state what the adversary cannot touch (the games' private variables and the
oracle tables).

In Lean an adversary is a deterministic oracle program (`OracleComp`), which halts on every answer.
Its branching is finite wherever the answers are, that is everywhere except at the record lookups of
the deniability games, whose record type is arbitrary. A budget quantifies over containers and
tables: in the execution against any tables, the log holds at most the budget's number of queries of
each kind. Randomized adversaries are covered by separate theorems that average over independent
private coins, a distribution on programs that are each within the budgets, for most results
(section 6 lists the exceptions).

Three differences follow.

- Repeated queries count in both, which is more general than the text's "repeats no query".
- The EasyCrypt hypothesis asks for the budget against every implementation of the oracles, the Lean
  one against every table. An adversary whose count exceeds the budget only on answers that no
  function gives (two different answers to one query) meets the Lean hypothesis and not the
  EasyCrypt one. Such an adversary can cap its own count without changing its behaviour on real
  functions, so no adversary of the text is lost; the argument is a remark in `ASSUMPTIONS.md`, not a
  theorem.
- A Lean program halts on every answer. A mixture of programs can run for an unbounded time over
  its support, but no theorem turns an arbitrary probabilistic program that halts with probability
  one into such a mixture. The EasyCrypt adversary is any program that terminates with probability
  one when its oracles do. Neither covers an adversary that may run forever. The text says "when it
  halts".

### 4.4 The secrets

Both take the passwords as a finite set with an arbitrary distribution. EasyCrypt keeps an abstract
finite type and ranks it by sorting (`ranked`, `pr`, `top`); Lean takes `Fin N` with the masses in
decreasing order as a hypothesis, and a separate chapter (`PasswordDomains`) transports Theorem 3 to
any finite alphabet by relabeling; the other results are stated on `Fin N`, which is the text's own
numbering of the passwords. `p_1` is the largest mass in EasyCrypt and any upper bound on it in
Lean.

BIP39 passphrases are a finite set in EasyCrypt, which narrows the text (it allows a countable
list). The Lean development has the finite case for W5-W7 and, for Theorem 5 itself, a transport to
an arbitrary distribution on a countable alphabet through finite windows and a vanishing tail
(`PassphraseDomains`), for deterministic programs. This is the one place where the Lean statements
cover strictly more of the text's setting.

### 4.5 Numbers

EasyCrypt's bounds are real numbers. Lean's are extended non-negative reals (`ENNReal`), in which a
subtraction stops at zero. For upper bounds the two agree. For the lower bounds of the matching
attacks, `top(m + 1)(1 - m δ)` is negative for large `m` in the reals and zero in `ENNReal`; both
statements are then trivially true, so the difference never changes a claim.

### 4.6 Source lengths and the layout of the state

The text packs a source of `ENT` bits and an `r`-bit verifier from `G` into the 256-bit state. Both
developments first prove their theorems for an abstract layout: EasyCrypt for a bijection `pack`
with `ENT + r = 256` whose left half is the first 128 bits of the entropy (theory `Source`), Lean
for an equivalence between entropy-verifier pairs and states with the same projection property.
Both then instantiate the layout with bit strings: Lean with `BitVec` layouts, as typed theorems for
G10 and its forms and as definitions without a written type for Theorem 3, EasyCrypt with instances
of the whole theory at all five lengths (`Instances.ec`). The deniability results are likewise width-parametric in both (suite 3 with a
256-bit state, suite 4 with a state as wide as the source).

### 4.7 The generation of a source under the wallet check

In A.6 the source is drawn again and again until a 16-bit check on its BIP39 seed passes. The text
analyses the sequential rule and extends the result to "covered" rules, which choose among the
passing trials by the outcomes alone.

The EasyCrypt development has the loop itself in the game. A selection rule is a module that calls a
trial oracle; the text's rule is one such module (`SeqU`), and the covered rules are those that
satisfy two hypotheses, the text's conditions. `selection_eq` proves the text's claim: every covered
rule gives the same probability of every event as the sequential rule. Lemma W2, Theorem 5 and its
consequences are then stated for every covered rule. Inside the proofs the sequential rule is cut
off after `2^80` trials, which it reaches with probability below `2^-256`; the cut rule is a device
and appears in no final statement.

The Lean development represents the generation by its outcome: for fixed functions and passphrase,
the selected source is uniform on the set of passing values, which is the law of the sequential rule
(a stationarity lemma proves it), and an independent uniform choice when no value passes, which
happens with negligible probability. A separate chapter (`SelectionRules`) proves that a rule which
sees only the order and the outcomes of the trials and its own coins, and stops almost surely,
produces that law: `WalletSelection.chosen_eq` equates the law of the chosen source with
`WalletCompletion.real`, the kernel from which the game of Theorem 5 draws its source, and
`actual_eq` equates the selected source together with the adversary's run with
`WalletUnbounded.real`. The termination is a hypothesis. So the covered rules are connected to the
experiment of Theorem 5 by an equality of laws. What Lean does not have is Theorem 5 stated again
with a rule as a parameter, or a statement that the sequential rule is one of the covered rules.

Both are faithful to the results of the text. The EasyCrypt form keeps the program of the
specification in the statement and states Theorem 5 for every covered rule; the Lean form states the
distribution of the sequential rule and proves that every covered rule has it.

The coins of a rule. Since commit `da3a733` (2026-11-15) condition 2 of the text asks for coins
independent of the trial values given the secrets and the functions. The coins may depend on the
secrets and the functions, as under the former wording, which allowed more (the paragraph of
2026-11-15 at the top). An EasyCrypt rule module cannot read the secrets, the random oracles of the
game or the trial values (`Rl <: RULE` with `Gen`, `Trials` and the oracles excluded in every
section), so its coins are independent of all of them; a rule whose coins depend on the secrets or
the functions is not stated. A Lean policy maps the outcome history to a distribution. `actual_eq`
takes a policy indexed by the `S` and `T` tables at a fixed passphrase. `SelectionRules.joint` takes
one indexed by any context drawn from any prior, such as all the secrets and functions, and gives
the joint law of the context and the selected entropy when a value passes in every context; no
statement uses it: no theorem instantiates it with the game's prior, which would first have to be
conditioned on a passing value, or connects it to the experiment of Theorem 5. So Lean covers, as an
equality of laws, coins that depend on the `S` and `T` tables at a fixed passphrase, and the general
condition only in that lemma; EasyCrypt states Theorem 5 itself for rules whose coins depend on none
of them.

A generation that stops at a limit. Since 2026-11-12 the text lets an implementation stop after a
stated number of trials and report a failure (appendix B, item 9). Three experiments must be kept
apart: a rule that reports a failure and creates no container; the cut rules inside the two proofs,
which go on with some source at the cutoff (EasyCrypt with its last trial, Lean with a fallback that
its proof leaves arbitrary); and a generation conditioned on its success. EasyCrypt has the first as
a game since 2026-11-12 (`SeqF`, `GameF`): a failure creates no container and counts as no win,
`capped_up` bounds every event by the same event under the cut rule plus `2·2^-256`, for every
limit, and Theorem 5 holds as stated (`theorem5_seed_capped`, `theorem5_pair_capped`). Lean has the
laws of a search with a limit (`WalletCapped`) and no final statement for the first experiment.
Neither states a bound conditioned on a successful generation, and the text claims none.

### 4.8 Creation refusal

Creation refuses a container equal to its source and asks for other settings. Both developments let
the continuation after a refusal be arbitrary and prove each bound with the probability of a refusal
added, `2^-256` for the 256-bit state of appendix A and `2^-W` in Theorem 2 (section 5.2): EasyCrypt
through one lemma per game family for every terminating continuation, Lean through "refused"
variants of the theorems with an arbitrary response. Neither builds the loop that draws again.

## 5. The results one by one

Each subsection gives the text's claim, the formal statements, the route of each proof and the
differences. Names of the EasyCrypt development are lemmas of `src/`; names of the Lean development
are prefixed by `MhfeLean.` in its sources. Appendix A has the full table with files and lines.

### 5.1 Lemmas 1-3 and Theorem 1

The text. Lemma 1: decrypting a container under any password and encrypting the result under the
same password gives the container back. Lemma 2: a uniform state sent through a permutation chosen
independently of it is uniform and independent of the permutation. Lemma 3: two Feistel rounds with
independent uniform round functions send one fixed input to a uniform output. Theorem 1: for a
24-word source, the functions, the container, the disclosed password, the disclosed phrase and its
record have exactly the same joint distribution in the honest and in the prepared experiment, also
for fixed functions.

EasyCrypt. `invpermK` and `permK` are Lemma 1 for the network as a pure function of any table.
`lemma2` is an equality of distributions. `lemma3` is the two-round statement and `enc_uniform` its
network form (twelve fresh masks give a uniform state), which Remark G9 uses. `theorem1` states
equal acceptance probabilities for every distinguisher of the joint view with the random oracle, and
`theorem1_fixed` the same with the functions fixed. The proof makes the oracle a whole function,
then couples the two experiments by the bijection `X -> D_Q(E_P(X))` of Lemmas 1 and 2.

Lean. `Lemma1.consistency`, `Lemma2.uniform_and_independent` and `Lemma3.network_uniform`;
`Theorem1Feistel.joint` is an equality of two `PMF`s, for any law of the environment (the functions)
and any family of round masks, and `Theorem1.kernel_eq` is the same for fixed functions and a fixed
pair of passwords. The proof of Theorem 1 is the same change of variable: drawing `X` uniformly and
continuing with `D_Q(E_P(X))` equals drawing `X` uniformly and continuing with `X`.

Differences. None in the theorems. Lean states the equality of the laws; EasyCrypt states it as
equal probabilities for all distinguishers, which is the same thing. Lemma 1 also says that the
decrypted state is a valid phrase: Lean has this for 24 words, with the checksum as a parameter;
EasyCrypt states the lemma on states only. Neither models a word list, a parser or SHA-256.

### 5.2 Theorem 2 and the simulation of a prepared disclosure

The text. For a source of 12 to 24 words the advantage of a distinguisher that queries Argon2id on
`k` distinct passwords, HMAC `q` times and the record oracle `l` times is at most
`(k + 2) p_1 + l 2^-ENT + (12 q + 146) 2^-256`; suite 4 has the same analysis with a state as wide
as the source. A simulator that draws a password, recovers the container and programs a fresh
record reproduces the prepared disclosure up to `p_1`.

Both developments prove one width-parametric bound,
`(k + 2) p_1 + l 2^-ENT + 2·2^-W + 12 (q + 12) 2^-256`, where `W` is the width of the state: 256 in
suite 3, where it gives the text's `(12 q + 146) 2^-256`, and `ENT` in suite 4.

EasyCrypt. `theorem2`, in an abstract theory over the half width, with instances for suite 3 at 12
to 24 words and suite 4 at 12 to 21 words. The proof follows the games of the text: remove refusal
and redraw (`2^-W + p_1` and `2^-W`); answer the encryption's own Argon2id and HMAC points from a
private table, which changes nothing until the adversary queries a private point or looks up the
real phrase; draw the real source after the run, so that a lookup hits it with probability
`l 2^-ENT`; draw the keys and the password after the run for the private points, which gives
`(k + 1) p_1 + 12 (q + 12) 2^-256`; what remains is Theorem 1's bijection. The real wallet's record
may depend on every value of the experiment. `simulation` bounds the difference between the prepared
disclosure and the simulator by the probability of the real password, for every container.

Lean. `Theorem2.bits`, generic in the width, the source length and the packing, with the
arithmetic identities `Theorem2.suite3_error` and `Theorem2.suite4_error`, in a width-parametric
operational model of its own (`DeniabilityModel`), and `PreparedDisclosure.simulation` with its
conditional and failure forms. The proof has the same steps: a bad event of probability at most
`(k + 1) p_1 + l 2^-ENT + 12 (q + 12) 2^-256`; a coupling that replaces the real password's row of
`A` and the twelve values of `H` on the real path by spare ones, after which the run is unchanged
unless it is bad; a bijection of the sample space that makes the replaced tables fresh; Theorem 1's
change of variable; and the two refusal events, `p_1 + 2^-W` and `2^-W`.

Differences.

- In Lean only `A` and `H` are sampled; `B` and `G` are arbitrary fixed functions, which is
  stronger. In EasyCrypt all are random oracles.
- The real wallet's record. In Lean's `Theorem2.bits` it is drawn before the decoy, from the setup,
  the real password, the source and all four functions, so it cannot depend on the decoy. In
  EasyCrypt it is drawn last, from the source, the password, the states, the decoy's password and
  the disclosed record (`dReal`), and not from the functions. Neither experiment contains the other,
  and the text says "used in any way". The difference is one of experiments, not of names: let the
  scenario `U` return a fresh fair bit; a real record that copies the disclosed one agrees with it
  with probability 1, and a record drawn before it with probability 1/2, whatever its law (in Lean
  `usage` is fixed outside the averaged setup, so the setup cannot carry the bit). It changes no
  bound, because the real record is read only by a lookup of the real phrase, which the bad event
  charges. Since 2026-11-12 the Lean port has both experiments: `Theorem2Records.bits` draws the
  record last, from the real password, the source, the tables, the container, the decoy password,
  the recovered decoy state and the disclosed record, with the same bound; its record kernel has
  every argument of EasyCrypt's `dReal`. `Theorem2Records.independent` shows that the experiment of
  `Theorem2.bits` is a case of the new one, and `RecordOrder.independent_agreement` and
  `copied_agreement` are the two probabilities above. In both developments a record is fixed before
  the adversary runs.
- The simulation corollary when no other password has positive probability. Lean returns the
  failure result of the text explicitly (`PreparedDisclosure.failure`). In EasyCrypt the prepared
  disclosure draws the decoy from `dP \ pred1 p`, which is then the empty sub-distribution, and the
  bound holds trivially; `simulation` does not build the failure branch.
- Both leave the behaviour after a refused or redrawn first draw arbitrary, which contains the
  text's redraw. Neither constructs the redraw loop as an experiment of its own.
- Lean proves Theorem 2 in a second oracle model, with no lemma that links it to the model of its
  guessing bounds, and does not instantiate it per suite; EasyCrypt uses one model throughout and
  instantiates it at the nine pairs of suite and length.

### 5.3 Theorem 3 and Lemmas G1-G5

The text. Γ0 is the real game. Γ1 draws the container uniformly and defines the source by decryption
(Lemma G1: same joint distribution). Γ2 makes `G` at the source fresh, which is unseen until `G` is
queried there (Bad). The chain `c_1 ... c_36` is the sequence of the 36 points of the decryption of
the container under the real password. G2: without premature queries the chain is queried in order.
G3: a premature query (Early) has probability at most `(12 p_1 k_A + 66 + q_B)/2^128 + q_H/2^256`.
G4: Bad without a complete chain and without a premature query (`Bad ∧ ¬Comp ∧ ¬Early`) has
probability at most `q_G/2^128`. G5: without a premature query the points of the chain are distinct.
Assembly: a complete chain costs twelve Argon2id queries with the real password, so at most `k_A/12`
passwords have one, and the guess adds one.

EasyCrypt. `G1` is a program equivalence proved with the functions fixed in advance and Lemma 2. The
step from Γ1 to Γ2 is one lemma for every play (`upto_bad`, `ineq1`). Γ2 is then run lazily: the
game never decrypts under the real password, and a monitor that the adversary cannot see records
the chain of every password as its points become defined (`lazy_gamma2`). `G2` and `G5` are
invariants of the monitor. `G3` and `G4` are expectation-logic proofs: the password is drawn after
the run, and the potential is the expected remaining risk of the chain of a password drawn from the
distribution plus the unused budgets; a query raises it by at most its share of the budget, a fresh
answer keeps it in expectation, and its value at the start is the bound. The assembly (`gamma2`,
`theorem3`) counts the passwords with complete chains in the log (`mass_cands`).

Lean. `G1.joint_resampling` is a bijection of the sample space that exchanges the verifier part of
`G` at the source with a spare value. The step to Γ2 is pointwise: for every sample, a win against
the programmed table implies a win or Bad against the plain one (`Theorem3.transfer`). Lemmas G2 and
G5 are statements about the times at which the points of the chain are first queried in a log. For
G3, a premature query implies one of 35 events (twelve for `B`, twelve for `A`, eleven for `H`):
the table's value at a point that a monitoring program selects just before its first query falls
into the set of values that would make the next chain point an already logged one. Each such event
has probability at most the expected size of the set over `2^128` or `2^256`, by one lemma on a
table value outside the program's own log, and the sizes add up to the text's count
(`G3.lemma_g3`). G4 stops the decryption before its last `H` query in the same way.
`Theorem3.bound` assembles them; `Theorem3Randomized.bound` averages over private coins.

Differences. The bounds are identical, constant by constant. The proofs of G3 differ in kind. The
Lean proof is the text's union bound, with "fresh at the time of the query" made exact by stopping a
program before the query. The EasyCrypt proof has no union bound: it carries a potential through the
lazy game, and the bound is the potential's value at the start. Lean never defines a lazy game and
proves only the inequality between Γ1 and Γ2; EasyCrypt proves the equivalence of the lazy and the
eager Γ2 and the two equalities "until Bad" of the text. Both state the theorem for an abstract
layout of the state; EasyCrypt instantiates it at the five source lengths, Lean has the bit layouts
for Theorem 3 as definitions without a stated type.

### 5.4 Corollaries G6, G7 and G10, and Remark G9

G6 (recovering the source). Both obtain it from Theorem 3's Bad bound with one more `G` query:
EasyCrypt wraps the adversary so that its output becomes a query (`G6`), Lean has `G6.bound` and a
randomized form.

G7 (depth). The text: if the Argon2id queries occupy at most eleven batches, the adversary wins
with probability at most `p_1` plus the error. EasyCrypt has batches of Argon2id queries in the
oracle interface from the start; Lemma G2 is stated with batch numbers, so a complete chain without
a premature query needs twelve calls that contain Argon2id queries (`comp_depth`, `G7`). Lean proves
the same final bound by another route (`G7.bound`). It defines programs that commit a whole batch
before they see an answer (`BatchProgram.Program`, run against fixed tables by `BatchProgram.run`)
and proves that serializing each batch with its Argon2id queries first gives the same result, the
same answers and the same count of every kind of query (`BatchProgram.execution`,
`BatchCrypto.execution`, `BatchCrypto.counts`). `G7.bound` takes a batch adversary with at most
eleven batches that hold Argon2id queries, applies this compiler, and uses that a complete chain
needs twelve groups of consecutive Argon2id queries; its probability is written for the compiled
program. The text's intermediate claims (Early extended to batches, G2 and G3 for it) are not Lean
statements. The text names this second route since 2026-11-12 (appendix B, item 8).

G9 (refusal). Both prove that a fixed state is its own image with probability exactly `2^-256` and
that every theorem holds with refusal after adding `2^-256` (EasyCrypt: `G9`, `refusal`, `refusalK`;
Lean: `G9Game.probability` and refused variants).

G10 (wallet data). Both prove the bound with `q_Ω` added beside `q_G`, for an idealized wallet
function of the entropy, and the form in which the wallet data is derived from the phrase with its
checksum. EasyCrypt reduces G10 to Theorem 3 by an adversary that asks `G` whatever it asks `Ω`
(`G10`), and gives the checksum-aware form its own first steps (`G10_derived`). Lean, after its
shortening, proves the checksum-aware bound once and specializes it to independent wallet data
(`G10Direct.bound`, `G10.bound`).

The end of A.4 notes that a 24-word source without wallet data gives the adversary nothing to test,
so it wins with probability at most `p_1`. Both have it for every adversary, with no budget:
EasyCrypt as `G0_p1`, Lean as `G10NoWallet.bound`.

Randomized adversaries. In EasyCrypt every statement covers them. In Lean the forms with private
coins are separate theorems, and four are not stated: G7 and the checksum-aware G10 without refusal,
and Theorem 3 and G6 with refusal. Each follows from the deterministic form by averaging, which is
an argument on paper and not a checked statement.

### 5.5 The matching attacks G8 and G10

The text. The attack inverts the container under the `m` likeliest passwords, tests each inversion
against the verifier, outputs the first that passes and otherwise the next candidate. It succeeds
with probability at least `Σ_j p_j (1 - (j - 1) δ) >= top(m + 1)(1 - m δ)`,
`δ = 2^-r + 2^-128 + 12·2^-256`, with `12m` Argon2id queries.

EasyCrypt. `G8` is the sum for any list of distinct candidates, `G8_top` the form with `top`,
`G8_budget` the query counts, and `G10_match`, `G10_top`, `G10_budget` the same with the test
against `Ω`. The proof replaces Γ0 by Γ1, fixes `A`, `B`, `H` in advance, and carries a potential
through the attack: the sum, over the untested candidates before the real password, of the chance
that the candidate passes. The term `2^-128 + 12·2^-256` is a lemma of its own (`pair_coll`): two
inversions of one container under different passwords agree in their first half with at most that
probability. `G8_bracket` adds the upper bound of Theorem 3 at the attack's own budget, which is the
text's remark that the best adversary lies between the two.

Lean. `G8Weighted.bound` and `G8.bound` in the text's form, `G8.weighted` and `G8.coarse` for any
injective order of candidates, `G8.budgets`, `G10Matching.bound` and `G10DerivedMatching.bound`, all
in the original games. The attack's output is a first-pass search; the real password passes; a wrong
candidate passes with probability at most `2^-r + 2^-128 + 12·2^-256`, where the last two terms
bound the event that the two inversions recover the same entropy (a collision of the last keys, or
a fresh last mask); a union bound over the earlier candidates gives the sum.

Differences. The lower bounds are the same; they are real numbers in EasyCrypt and truncated at
zero in Lean (section 4.5), which never makes the Lean bound weaker. Both isolate the same collision
lemma for two inversions. Lean's proof is a union bound over the earlier candidates on eager tables;
EasyCrypt's carries the sum through the attack's loop as a potential. The combination of an attack
with the upper bound is an EasyCrypt statement only; in Lean it follows by instantiation and is not
stated. The budgets differ in one place: Lean's attack on the form of G10 that derives the wallet
data from the phrase reads `G` once more per candidate, for the checksum (`q_G ≤ 2m`,
`G10DerivedMatching.budgets`), where the attack on independent wallet data has `q_G ≤ m` in both
developments. For a 24-word source the named attacks still ask the verifier oracle once per
candidate, although an attack without these calls exists.

### 5.6 Theorem 4 and Lemmas K1-K4

The text. Δ0 gives the adversary the pair `(X, Y)`. For each of eleven positions `j`, Δ1_j draws
`Y` uniformly and programs the two masks at the meeting point of a forward chain from `X` and a
backward chain from `Y` (K1: same distribution). K2 and K4 are structural: without premature
queries or a crossing of the two chains, each password with a complete evaluation pays eleven
Argon2id queries except for at most eleven "bad" positions. K3 bounds the premature queries by
`(24 p_1 k_A + 2 q_B + 287)/2^128 + (2 q_H + 12)/2^256`. Averaging over `j` (inequality (2)) gives
the fractional top `T(1 + k_A/11)`.

EasyCrypt. `K1` computes both joint laws exactly on fixed functions. `averaging` is inequality (2).
`K2_order`, `K2_distinct`, `K2_cross` and `K4` hold for every adversary, without budgets. `K3` is an
expectation-logic proof over both chains of every password; the constant 287 is the value of the
potential at the start. `theorem4` draws the position first, couples it with a permutation of the
rounds that puts the bad ones first, draws the password after the run and bounds the result by
`ftop` through a knapsack lemma (`ftop_max`); `ftop_attained` shows that `T` is the maximum, as the
text defines it. `theorem4_coarse` is the form with `top(k_A/11 + 2)`.

Lean. `Theorem4.bound` with the same error term, `Theorem4.randomized`, `Theorem4.coarse` and a
form with refusal. K1 (`K1.joint_law`) is a bijection of the sample space for an abstract system of
two programmed inputs, instantiated at the rounds `j` and `j + 1`. The step to Δ2 is pointwise for
each position, and the average over the eleven positions exchanges two expectations. K2
(`K2.cross_bound`) replays the run up to the two `B` queries of a pair of rounds and bounds each of
the 132 ordered pairs by `2^-128`. K3 (`K3.early_bound`) is not proved anew: the premature queries
of the forward chain are those of the one-chain game of Theorem 3 mirrored (rounds reversed, halves
swapped), and those of the backward chain are those of the one-chain game for the adversary extended
by the forward evaluation, so the bound of G3 applies twice and the counts add up to 287. K4
(`K4.lemma_k4`) is combinatorial. `T(x)` is bounded from above by a greedy argument.

Differences. None in the bounds: 419, 287 and 132 appear in both. Both state the lemmas separately.
The proofs of K3 differ most: Lean reduces it to G3 by a symmetry of the model, EasyCrypt carries a
potential over both chains of every password. The Cross event has the same 132 pairs in both, as a
union bound in Lean and as a potential in EasyCrypt. Lean proves `T(x)` only as an upper bound and
`T(x) <= top(floor x + 1)`; EasyCrypt also proves that it is attained and
`top(floor x) <= T(x) <= top(ceil x)`. Lean's form with refusal is for deterministic adversaries.

### 5.7 Proposition K5

The attack on a known pair needs eleven Argon2id queries per candidate: it runs the rounds 11 to 1
backward from `Y` and compares one half with the known `X`. Both developments prove the sum form,
the form `top(m + 1)(1 - m δ_K)` and the budget `11m`, `10m + 1`, `11m`. Lean has `K5.bound`,
`K5.coarse_bound`, `K5.budgets` and a form with refusal (`K5.refused_bound`). Its proof bounds a
false pass of one wrong candidate by `2^-128 + 11·2^-256` (a collision of its round-1 key with the
real one, or a fresh mask), sums over the earlier candidates, and then enlarges the loss to the
former text's `δ_K = 2^-128 + 11 (m + 1) 2^-256`. EasyCrypt first proved the former `δ_K` with a
lazy oracle that charged each key of a candidate's chain against the keys already in the table.
On 2026-11-12 its K5 was rewritten in the style of G8 for the new text, `δ_K = 2^-128 + 11·2^-256`:
the pair lemma for one wrong candidate (`two_k_e` in the lazy oracle, `pairK` over the whole
function), then the attack with the function fixed (`coreK_e`, a union over the candidates before
P), `K5`, `K5_top`, `K5_budget` and the bracket with Theorem 4 (`K5_bracket`). EasyCrypt now states
the text's `δ_K`. Codex's Lean sources state the former one, which is weaker; the Lean 4.35 port
(`tmp/lean-review-2026-11-11/PORT-v4.35.md`) states the new `δ_K` since 2026-11-12, by removing the
enlargement.

### 5.8 Lemma W1, the generation (Lemma W2) and the selection rules

W1 is a counting lemma: `n` pairs with at most `m` distinct passwords weigh at most `top2(m, n)`.
Both prove it by sorting (EasyCrypt: `W1` through `top_sum`; Lean: `W1.lemma_w1`).

W2 says that the real generation (draw sources until the 16-bit check passes) and a "planted" one
(a uniform source whose seed and check value are programmed) give the adversary views at distance
at most `δ_gen`. The proof must show that the rejected trials stay invisible: each is hit by an
adversary query with probability about `2^-256` or `2^-512`, and there are about `2^16` of them.

EasyCrypt. `W2_cut` goes through four games: the real generation with ghost copies of the trial
samples; a game that checks each trial with its fresh 16 bits only and programs `S` and `T` at the
passing trial alone; one in which the trial values come from three oracles indexed by the trial
number, which become lazy so that the rejected values are drawn after the adversary; and the
planted game. The expected number of rejected trials is bounded by a potential over the loop, and
the cutoff by Bernoulli's inequality. `W2` is the statement for every covered rule, obtained from
`selection_eq`-style transfer lemmas (`selection`, `selection_bound`, `rule_up`, `rule_lo`). W2 is
stated for a judge that sees the secrets after the run, so one statement covers every event.

Lean. `W2Source.generation_bound` states that the actual and the planted experiment are
statistically close with distance `W2.delta k_S q_T`, for an adversary whose distinct `S` queries at
the real passphrase and distinct `T` queries are at most `k_S` and `q_T`;
`W2Source.joint_generation_bound` adds an outer context. The chapters on generation sampling,
coupling, survival and the bound carry the proof, through raw trial lists and a capped generation.
`WalletSelection.chosen_eq` and `actual_eq` are the selection-rule statements: equalities of laws
with the sequential completion and with the whole experiment (section 4.7). `SelectionRules.joint`
gives the joint law of a context and the selected entropy for a policy indexed by that context, and
no statement uses it.

Differences. Lean counts distinct queries in the budgets of W2, EasyCrypt all queries; the Lean
hypothesis is weaker, so its statement is stronger there. EasyCrypt's W2 keeps the generation loop
as a program and quantifies over rules; Lean's works with the law of the selected source. Both use a
cap on the number of trials inside the proof and remove it at the end.

### 5.9 Lemmas W3 and W4 and Theorem 5

The text. Θ0' and Θ1 have the same joint distribution (W3, the analogue of G1 with the seed and the
check value programmed). In Θ2 the secrets are independent of the view until a bad query; W4 bounds
a collision of an inversion with the real source by `k_A/2^128 + k_A/2^256`. A password and
passphrase pair can be tested only by a seed computation at a completed chain, which gives the set
of tested pairs and `top2`.

EasyCrypt. `W3` is an equivalence for every continuation that sees all functions. `W4` and the
other bad events are expectation-logic bounds on the lazy Θ2 (`Theta2.ec`). `theorem5_seed` and
`theorem5_pair` are the two parts for every covered selection rule with refusal; `theorem5_seed_cut`
and `theorem5_pair_cut` are the same for the cut rule, from which they follow. The step from Θ0 to
Θ1 (W2 and W3 together) is one lemma, `theta01`, used by Theorem 5, W5 and W7.

Lean. `Theorem5.seed_bound` and `Theorem5.pair_bound`, with `ε_W` term by term, and
`PassphraseRefusal.seed_bound` and `pair_bound` for an arbitrary passphrase alphabet.

Differences. The bounds agree term by term, `δ_gen` and the refusal term included. Lean has the
arbitrary passphrase alphabet; EasyCrypt has the statement for every covered rule in the game
itself and, since 2026-11-12, both parts for a generation that stops at a limit and reports a
failure (`theorem5_seed_capped`, `theorem5_pair_capped`, section 4.7), which Lean does not state.

### 5.10 Corollaries W5 and W6

W5: an adversary that outputs the source and the passphrase is bounded as in Theorem 5 with one more
seed computation and no `2^-512`. W6: for an ordinary 24-word source (no check) the bounds hold
without `δ_gen` and `q_T/2^512`. EasyCrypt: `W5`, `W6_seed`, `W6_pair`, `W6_phrase`; the wrapper
that turns the guess into a seed query makes a correct guess a bad event of Θ2, which removes the
`2^-512`. Lean: `W5.bound`, `W5Randomized.bound`, `W6.seed_bound`, `W6.pair_bound`,
`W6.source_bound`. Since 2026-11-12 the text keeps `k_S` in `δ_gen` (Lemma W2 concerns the
adversary's view, and the seed query for the output comes after it). EasyCrypt states this
(`W5`, `W5_cut`: the step from Θ0 to Θ1 runs the adversary without the extra query). Codex's Lean
`W5.bound` states `k_S + 1` in all of `ε_W`, the former text, which is weaker; the Lean 4.35 port
states the new form (`W5Source.error`, `W5.error`).

**The number of trials (2026-11-13).** The text: given `S`, `T` and `Q` the outcomes are independent
passes with probability `p_U` and independent of the selected source; one uniform number per trial
couples them with outcomes of probability `2^-16`, which differ with probability at most
`|p_U - 2^-16|·n`; the variance of `|U|` is below `2^240`, so `E|p_U - 2^-16| < 2^-136`; and outcomes
of probability `2^-16` are coins the adversary can draw itself. Since commit `33dba0f` (2026-11-15)
the paragraph also requires that the selection and scheduling of the trials, the order in which they
finish and the duration depend only on the outcomes and on one set of coins drawn independently of
the secrets, the functions and the trial values; the sequential rule selects, schedules and finishes
its trials by the outcomes alone, and the coins of a duration are those of the next two paragraphs.

EasyCrypt. `theorem5_seed_trials`, `theorem5_pair_trials` and `W5_trials` (`TrialCount.ec`) generate
the phrase with the sequential rule `SeqU` and give the adversary the list of all its trial
outcomes. The coupling is the text's: the outcome of a trial is `r < k_U` against `r < 2^240` for
one uniform `r` of 256 bits (`cc_upto`, `cc_bad`), on the rule cut off after `2^80` trials; the cut
and the trials of the reduction that all fail cost `2^-256` each and are absorbed in the slack of
`E_pU_tight` (`E|p_U - 2^-16| ≤ 2^-136 - 2^-154`). EasyCrypt adversaries may sample, so a duration
computed from the outcomes and the adversary's own coins is covered by the statement itself. The
response after a refusal is any that the base theorems allow (`Rf <: AFTERP {-Gen}`): the reduction
replaces it by one that always wins (`RwSeed`, `RwPair`, `Rw5`), which can only raise the
probability.

Lean, the port. `Theorem5Trials.seed_bound`, `Theorem5Trials.pair_bound` and `W5Trials.bound`
(chapter `TrialCount`) take an adversary and a refusal response that are families indexed by the
number of failures, which gives the outcomes of the sequential rule; `Theorem5TrialsRandomized` and
`W5TrialsRandomized` add private coins, which give a duration. The joint law of the number of
failures and the selected value is a product of a geometric law of rate `p_U` and the uniform law on
the passing set (`WalletCount.real`). On tables where a value passes it is unchanged by any prefix
of actual trials (`WalletCount.completed_loop`), and the actual loop cut off after `c` trials is
within `(1 - p_U)^c` of it on every test (`WalletCount.capped_close`, `WalletCount.survival`).
The coupling is replaced by a renewal argument: two geometric laws of rates `p` and `q` differ on
every test by at most `|p - q|/q` (`TrialLaws.close`, a fixed point of the one-step recursion), and
the same continuation keeps this distance (`TrialLaws.kernel`). The variance step is the text's
(`TrialDeviation.gap_bound`: the mean of `2^16·|p_U - 2^-16|` over uniform tables is at most
`2^-120`). With rate `2^-16` the game is that of `Theorem5Randomized` and `W5Randomized` with the
number of failures as coins (`TrialEnvironment.ideal_eq`).

Differences. The bounds agree: `2^-120` added for the sequential rule. EasyCrypt reveals the
outcome list of the loop program; Lean reveals the number of failures as the index of the adversary
family, of which that list is a function. A table on which no value passes is handled in EasyCrypt
by the cut rule and in Lean by an arbitrary fallback that the bound charges in full. Neither
development states `w` workers (`2^-120 + (w - 1)·2^-136`), the general `2^-136·n`, or a rule that
stops at a limit and also reveals its trials, which the text allows.

### 5.11 Proposition W7

The attack inverts the container under `m` passwords and goes through at most `n` pairs in order of
probability, computing a seed for each and testing it against the wallet data, against the 16-bit
check, or against the check and then the wallet data. The text gives lower bounds for the seed game
and the pair game, with a loss per wrong pair of `2^-λ`, `2^-16` or `2^-(λ + 16)`, and for the pair
game also `2^-512` and `(m - 1) δ_X`.

EasyCrypt. `W7_seed` and `W7_pair` in the real game for every covered rule, with the generation and
refusal terms; `W7_top2` gives both in the text's form for the three tests; `W7_budget` the six
query counts; `W7_passes` that in the third test the wallet data is queried exactly once per pass of
the check; `W7_bracket` the upper bound of Theorem 5 for the attack. The seed and the pair game have
separate potentials, since a wrong pair that yields the real seed wins one game and loses the other.

Lean. `W7Source.seed_refused` and `W7PairSource.refused` with weighted and `top2` consequences, for
the three tests, with the six budgets and the exact count of wallet-data queries. The `top2` forms
are conditional on the selected pairs having mass `top2(m, n)` and do not tie `m` to the inverted
passwords; the budgets are a separate theorem. The final lower bounds take a list of `n + 1`
distinct pairs, where the text says at most `n`.

Both state W7 for a finite passphrase set and both bound the seed game and the pair game separately.
The bracket with Theorem 5 is an EasyCrypt statement only.

### 5.12 The readings of Theorem 5

| Reading of the text | EasyCrypt | Lean |
| --- | --- | --- |
| Uniform secrets: `top2(m, n) = min(n, min(m, N1) N2)/(N1 N2)` | `top2_uniform_eq`, the equality (since 2026-11-12); `top2_uniform`, the upper bound that the consequences use | `UniformTop2.exact_top`, the equality; the game statement `UniformPairModel.seed_bound` |
| A known passphrase: `top2(m, n) = top(min(m, n))` | `top2_known`, and part (b) in this form, `theorem5_pair_known` | `KnownPassphrase.top2`, and the game statements of `KnownProfile`, for deterministic programs |
| One cost budget `c` for Argon2id calls and seed computations | for any secrets, `theorem5_cost`: `T + ε_W + 2^-512` for every bound `T` on `top2` over the pairs the budget allows, valid on every run; uniform secrets, `theorem5_cost_uniform` | for uniform secrets, `FullCostBound.bound`, `FullCostFloor.bound` and, with coins, `FullCostRandomized.bound`; for general secrets the counting lemma `PairMass.adaptive` (`Pr[(P, Q) ∈ Z] <= Exp[top2(...)]`), not assembled into a game statement |

Neither development states the text's form with an expectation over Θ2 for general secrets as a game
statement; EasyCrypt bounds the expectation by its worst case, Lean has the expectation as a lemma.

## 6. Coverage

Both developments have a statement for every numbered result of the text, with its constants. The
statements are not the same theorems: the table lists where the experiments, the domains and the
adversaries differ, and what only one development states. "Not stated" means that the sentence
follows from stated results by an argument that no checker has seen. The Lean column follows the
statement review of 2026-11-11 (`tmp/lean-review-2026-11-11/REVIEW.md`, findings `L1-n` to `L5-n`)
and the audit AUD-012; rows marked "port" concern the Lean 4.35 port only.

| Item | EasyCrypt | Lean |
| --- | --- | --- |
| Passwords | an abstract finite set with any distribution, ranked by sorting | `Fin N` with decreasing masses; the transport to any finite alphabet exists for Theorem 3 only |
| Passphrases | a finite set with any distribution | finite in W5-W7, the readings and every form with coins; any distribution on a countable alphabet for Theorem 5 (a) and (b), deterministic programs |
| Randomized adversaries | every adversary may sample | separate theorems that average over private coins; several combinations with refusal or with the arbitrary passphrase alphabet are not stated |
| Adversaries that loop without a bound but halt with probability one | covered | total programs and their mixtures, whose running time can be unbounded over the support; no theorem turns such an adversary into a mixture |
| Adversaries that may run forever | not covered | not covered |
| The real wallet's record in Theorem 2 | drawn last: may depend on the source, the password, the states, the decoy password and the disclosed record, not on other values of the functions | `Theorem2.bits`: drawn first, from the real password, the source and the functions; port, since 2026-11-12: also `Theorem2Records.bits`, drawn last, from all of these and the realized disclosure |
| Budgets | every query counts, against every implementation of the oracles | every query counts, against every table and container; distinct queries in W2 |
| The generation of the source | the loop itself; W2, Theorem 5, W5 and W7 for every covered rule, the text's rule included (`SeqU`, `selection_eq`); the rule reads neither the secrets nor the functions | the law of the selected source (uniform on the passing set, `stationary`); for rules that see only the order and the outcomes of the trials and coins that may depend on the `S` and `T` tables at a fixed passphrase, equalities of laws with the sequential completion and with the whole experiment (`chosen_eq`, `actual_eq`), from which the game of Theorem 5 draws; Theorem 5 is not stated with a rule as a parameter; a policy indexed by any context only in `SelectionRules.joint`, which no statement uses |
| A generation that stops at a limit and reports a failure | `theorem5_seed_capped`, `theorem5_pair_capped`, for every limit (since 2026-11-12) | the laws of a search with a limit; no final statement |
| A generation that reveals the outcomes of its trials, their number and a duration (A.6, the paragraph on the number of trials) | the sequential rule, the adversary given the outcome list, any response after a refusal: `theorem5_seed_trials`, `theorem5_pair_trials`, `W5_trials` (since 2026-11-13); `w` workers, the general `2^-136·n` and a limit with revealed trials not stated | port: the sequential rule, the adversary and the response after a refusal families indexed by the number of failures: `Theorem5Trials`, `W5Trials`, with coins `Theorem5TrialsRandomized`, `W5TrialsRandomized` (since 2026-11-13); `w` workers, the general `2^-136·n` and a limit with revealed trials not stated |
| "The best adversary lies between" after G8, K5 and W7 | `G8_bracket`, `K5_bracket`, `W7_bracket` | not stated |
| `T(x)` is the largest weighted sum, and `top(floor x) <= T(x) <= top(ceil x)` | `ftop_max`, `ftop_attained`, `ftop_top` | the upper bound and `T(x) <= top(floor x + 1)` |
| One cost budget | for any secrets, a bound valid on every run (`theorem5_cost`); uniform secrets as a corollary | for uniform secrets, with an adaptively allocated total cost (`FullCostRandomized`); for general secrets a counting lemma only |
| Uniform secrets, the exact `top2` | `top2_uniform_eq` (since 2026-11-12) | `UniformTop2.exact_top` |
| `top2` as the sum of the largest products | by definition, for finite sets | a supremum over finite sets of pairs; attained for a finite passphrase alphabet (`W1.top2_attained`), not stated for a countable one |
| A known passphrase | `top2_known`, `theorem5_pair_known` | `KnownProfile`, finite passphrases, deterministic programs |
| A 24-word source without wallet data: at most `p_1` | `G0_p1` | `G10NoWallet.bound` |
| The intermediate claims of G7 | batches in the oracle interface; Lemma G2 by batches | not stated; batch programs with an exact serialization (same result, answers and counts), by which the final bound is proved |
| The lazy Γ2 and the two equalities "until Bad" | `lazy_gamma2`, `upto_bad` | not formalized; only the inequality is needed and proved |
| Theorem 2's redraw experiment | arbitrary continuation after a refusal or a redraw | the same; the redraw loop is not built |
| The simulation corollary when no other password is possible | the empty sub-distribution; the bound is trivial | the explicit failure result (`PreparedDisclosure.failure`) |
| Lemma 1, the recovered phrase is valid | on states | for 24 words |
| Source lengths | the abstract layout, and instances at every length in both suites | the abstract layout; bit-level statements with a written type for G10 and its forms; for Theorem 3 definitions whose type Lean infers (`Suite3ShortBound`) |
| Lower bounds of the attacks | real numbers | truncated at zero, never weaker |
| Remarks of the text: a six-call parallel filter, numerical examples (among them the pair game of an ordinary source without wallet data), heuristic estimates | not formalized | not formalized |
| The check of the whole development | `./check.sh`: every source in strict mode, in a folder without compiled caches | port: `./check.sh`: a build from the sources, the axiom inventory, a kernel replay of every chapter |

## 7. Size and effort

The Lean development is 1.7 times as long as the EasyCrypt one (32,876 lines against 19,402). The
difference is not in the proof scripts, which are of similar length (about 12,000 lines against
10,677), but in everything around them.

- Statements. A Lean theorem repeats its setting: the layout, the password distribution, the
  adversary and one hypothesis per budget appear in the binders of every headline theorem, and the
  statements of the Lean development took about 7,500 lines when they were last measured (at 34,243
  lines). EasyCrypt declares an adversary and its
  hypotheses once per section; the 1,039 statements of the EasyCrypt development are short.
- Definitions. A game in EasyCrypt is a few lines of imperative code and its probability is a
  primitive notion. In Lean a game is a composition of `PMF` binds over explicit table types, and
  the operational notions (execution with a log, counting, stopping) are definitions of the
  development itself: 875 definitions against 295 operators and 270 small modules.
- Variants. Lean states the randomized, refused and bit-width variants of a theorem separately.
  EasyCrypt adversaries are randomized already, refusal is one lemma per game family, and widths
  are instances of an abstract theory.
- What EasyCrypt pays instead. Arithmetic on finite sets and sums, which Lean's library handles in a
  line, takes explicit lemmas (`top_sum`, `sum_distinct_le`, the sorting lemmas behind Lemma W1).
  The expectation-logic proofs carry long invariants: the four matching-attack proofs are 150 to 320
  lines each, and two pairs of them (G8 with G10, the two games of W7) are parallel and could not be
  merged without a case split at every step.

The Lean development was shortened from 36,885 lines by its author after a review had found whole
arguments kept twice; a study of that pass estimated that its statements and models cannot go far
below 25,000 lines unchanged. The EasyCrypt development grew from a planned 4,000 to 6,000 lines to
19,402; the lower bounds of the attacks and the selection rules, which the first plan left out,
account for about a third of that.

A full check takes a few minutes in both systems: 373 seconds for the 18 EasyCrypt files on six
cores, 257 seconds of compiler time for the 38 Lean chapters by the author's record.

## 8. What has to be trusted

Lean. A theorem is accepted when the kernel, a small program, has checked a proof term. The
elaborator, the tactics and the automation produce terms and need not be trusted. The development
uses no `sorry`, no axiom of its own and no `native_decide`; its inventory reports that every
declaration depends on at most `propext`, `Classical.choice` and `Quot.sound`. What remains to be
trusted is the kernel, the reading of the statements, and the definitions of Mathlib and VCVio that
the statements use.

EasyCrypt. A lemma is accepted when the tactics of its script succeed. The rules of the logics are
implemented in a large program, with no separate checker of the result, and many steps are sent
through Why3 to SMT solvers: 2,398 such calls in this development. A step counts as proved when one
of Alt-Ergo, Z3 and CVC5 proves it; no single solver proves every step. The trusted base is
therefore much larger than Lean's. Errors in EasyCrypt's rules have been found and fixed over the
years, three of them in the probabilistic `while` rules between the release r2026.10 and the
development branch used here; the development is checked on both. Thirteen negative controls, each
a false variant of a statement, are rejected at the expected place, which shows that the checks are
not vacuous at those places, not that the system is sound.

Common to both. A proof is about its statement. Whether the formal statements are the text's is a
judgment that no checker makes. It was made by reviewers reading each statement against the text,
five for each development; the reviewers were AI agents, and no human expert has read the two sets
of statements. The assumptions of the EasyCrypt development (the parameters of its theories) are
realized by instances, so they are consistent.

What was checked independently of the authors. The table gives the checks of 2026-11-11, with
their times and counts; the audits of 2026-11-12 follow it.

| Check | EasyCrypt | Lean |
| --- | --- | --- |
| Full check from source | by the development's own scripts, on EasyCrypt `main` (373 s) and on the release r2026.10 (468 s) | rebuilt independently on 2026-11-11 with Lean 4.28.0 and the pinned libraries: 38 chapters in 217 s, no warning; 37 of 38 compiled files byte-identical to the author's (the 38th differs by a path changed for the rebuild) |
| Kernel replay | not applicable | lean4checker v4.28.0 accepted every declaration of the 38 chapters |
| No `admit`/`sorry`, no own axioms | by search and by the build | by search, by the author's inventory run in the rebuild (5,919 constants, standard axioms only), and by Lean's `#print axioms` for 71 main statements |
| False statements are rejected | 13 negative controls | the author's six checker controls |
| Newest versions of the tools | EasyCrypt `main` and Why3 1.9.0 with Alt-Ergo 2.6.5, Z3 5.4.1, CVC5 1.4.2 | the sources do not compile unchanged with Lean 4.35.0 and the current Mathlib and VCVio (library changes since February 2026); a port of a copy (2026-11-12; `PORT-v4.35.md` gives its size and every change: no statement changed by the port itself, K5 and W5 then brought to the corrected text, one chapter added) compiles with them, has the same axioms, and passes Lean 4.35's kernel replay (`leanchecker`) |
| Statements against the text | five reviewers, 2026-11-11: no blocker, one major finding (the one-cost budget), closed; the minor ones closed or documented | two reviewers on 2026-11-09 for the results added then; five on 2026-11-11 for the whole current state: no blocker and no major finding, 15 minor findings and 36 notes |

The audits of 2026-11-12 (`mhfe_spec/docs/audits/`, reports AUD-011, AUD-012 and AUD-013).

- AUD-011 checked the EasyCrypt development: no wrong bound, and four findings about the check
  command and the wording of the README. Two matter to every reader of EasyCrypt proofs. The
  documented loop returned success after a failed compilation. And EasyCrypt accepts an up-to-date
  compiled cache (`.eco`) without checking the proofs again, with `-no-eco` too, even when a weak
  check wrote the cache; so the strict runs of the table count only because they ran from the
  sources, and `check.sh` now refuses to start next to a cache.
- AUD-012 compiled the 40 modules of the Lean port from their sources into a new folder, replayed
  them through the kernel, and ran the checkpoint (6,036 declarations at that time, standard axioms
  only) and three controls (an axiom, a `sorry` and a `native_decide`, each rejected). It found no
  wrong bound, and four findings: the narrower record of the real wallet in Theorem 2 (section
  5.2), a replay loop that hid failures, and two on wording.
- AUD-013 reviewed this comparison and the account of the port. It confirmed the detailed
  comparison and the counts of the header comparison, with the limits of that tool, and asked for
  the corrections that this revision makes: the conclusions claimed more than the sections support,
  and four descriptions of the Lean development were wrong or incomplete (batch programs, the
  selection rules, the conditions of G4 and G5, one empty cell of appendix A). It also checked the
  EasyCrypt additions of 2026-11-12 on both EasyCrypt versions.

The findings are addressed in the two developments (the folder `review-2026-11-12/` of each) and in
this revision. The auditor has verified the fixes of the AUD-011 findings; the later fixes are not
yet verified by the auditor.

## 9. What the formalizations found

In the text. No result was found false, and every constant of every bound was reproduced by both
developments. The remarks are about wording. The text has received the corresponding corrections
since (appendix B).

- Theorem 2 says that the adversary must not know the source length. The bound holds for every
  adversary; the condition matters only for what is compared.
- The bracket after Proposition K5 holds at the attack's budgets `q_B >= 10m + 1` and
  `q_H >= 11m`, which the sentence does not name.
- In W7's third test the text calls `q_Ω` "the number of passes"; as a budget it is at most `q_T`.
- The specification's list of conditions for the generation omits termination, which the
  supplement's covered rules require.
- The constant `δ_gen` has room: the EasyCrypt proof of W2 gives half of it and uses the rest to
  pay for moving from the cut rule to every covered rule. In Corollary W5 the `k_S + 1` inside
  `δ_gen` could be `k_S` (found by the review of the Lean statements, whose proof applies W2 before
  the extra seed query); the text and EasyCrypt say so since 2026-11-12.
- A.1 does not say that the password set is finite; both developments need it, and the
  specification's encodings of 1 to 1024 bytes are finite.
- The intermediate claims of G7 (Early extended to batches, G2 and G3 for it) are proved only in
  EasyCrypt; Lean reaches the final bound by serializing each batch with its Argon2id queries first,
  which the text could mention as a second route.
- K5's loss is smaller than the text states: a wrong candidate passes with probability at most
  `2^-128 + 11·2^-256`, independent of `m`; the text's `δ_K = 2^-128 + 11(m + 1)·2^-256` charges
  each key against all earlier ones. Lean proves the smaller loss and enlarges it. Since
  2026-11-12 the text states the smaller loss and EasyCrypt proves it as stated.

In the first drafts of the formal statements. Both developments had statements that were wrong or
weaker than the text, and their reviews found them before the proofs were final.

- EasyCrypt: the averaging inequality was false as first written, because the chains stop growing
  at a premature query; the selection lemma was false for a rule with a cutoff and became an exact
  equality for the text's rule; the one-cost-budget bound was missing. A switch to strict checking
  found five proofs that the fast mode had accepted wrongly.
- Lean: Corollary G7 is proved by another argument than the text's; the first snapshot lacked
  Theorem 2, K5, W7 and the selection rules, which the consolidated version added. The review of the
  current state found the gaps listed in section 6 (fifteen minor findings), none of which changes a
  bound.

## 10. Limits of this comparison

- One text, one model. Both developments formalize the supplement's ideal model. An error in the
  model itself, as a description of MHFE, would pass both. Neither says anything about Argon2id,
  HMAC, PBKDF2 or the programs.
- Not independent statements. The author of the EasyCrypt development had reviewed the model, the
  games and the statements of the Lean development before writing and consulted it while writing.
  The proofs share nothing, but agreement of the statements is weaker evidence than agreement of two
  blind formalizations would be.
- No formal link. The agreement was established by reading. No theorem relates a statement of one
  development to a statement of the other, and equal bounds do not make two experiments the same.
- Agents wrote and reviewed both. The comparison rests on machine checks for the proofs and on
  agent reviews for the statements.
- The Lean development is checked with the toolchain of February 2026 it was written for. Its port
  to the newest toolchain is a copy made for this review; the author's sources still target
  Lean 4.28. K5 and W5 at the corrected text, the chapter `DeniabilityRecords` and the audit AUD-012
  concern the port.
- Line counts and proof routes of the Lean development come from its sources and its author's
  guide; its proofs were not read line by line, since the kernel checks them.

## 11. Conclusions

1. The two developments prove the bounds of the text with the same constants, each under its own
   hypotheses. They do not prove the same theorems: the experiments, the domains and the adversaries
   differ, and section 6 says exactly what is common. Some differences are of form (distributions
   against distinguishers, real numbers against truncated ones, a program against its law). Others
   change what is covered. Lean covers more in four places: any passphrase distribution for Theorem
   5 itself, `B` and `G` arbitrary in Theorem 2, a real-wallet record that may depend on the
   functions, and, as an equality of laws, a selection rule whose coins depend on the `S` and `T`
   tables at a fixed passphrase. EasyCrypt covers more in five: every covered selection rule in the
   game itself, a generation that stops at a limit, randomized adversaries in every statement, with
   an unbounded running time provided they halt with probability one, the one-cost budget for any
   secrets as a bound valid on every run, and the brackets with the attainment of `T(x)`. Neither
   covers a countable passphrase alphabet in W5 to W7, an adversary that may run forever, or the
   one-cost bound in the text's form with an expectation.
2. The proofs differ in kind. EasyCrypt's are short where a game changes little (the logic does the
   coupling) and long where a quantity must be carried through a loop; Lean's are uniform in style,
   explicit about every probability space, and pay for it in statements and definitions.
3. Lean gives the stronger guarantee that a stated theorem holds: a small kernel and no solver, and
   its current state was rebuilt and replayed through the kernel by others than its author. That
   guarantee concerns the statement, not its distance from the text. EasyCrypt's principal games
   are closer to the text in form: one program for each experiment, with the generation loop and the
   batches in the game. They are not the text line by line: passphrases are finite, adversaries and
   continuations terminate, phrases and wallet records are abstract, and a refusal is followed by
   an arbitrary continuation.
4. Having both is a useful cross-check, not a measured assurance. A mistake in a statement is the
   main risk of a formal proof, and two statements of each result in unrelated languages, each read
   against the text, make some mistakes visible: the comparison found the differences of section 6
   and led to the corrections of appendix B. The independence is limited: one text, the model, the
   games and the statements of the first development reviewed before the second was written and
   consulted while it was written, and AI agents as authors and reviewers. The limit showed once:
   the former condition 2 of the text's selection rule allowed coins that make the selected phrase
   depend on the password, and both developments assumed stronger coins without listing this as a
   narrowing, so the comparison did not find it; a review of the wording did, on 2026-11-14 (the
   paragraph of 2026-11-15 at the top). No probability of a common undetected mistake can be given.

## Appendix A. Correspondence of the statements

The EasyCrypt names are located by `tmp/easycrypt-mhfe-2026-11-09/INDEX.md`, which gives the file and
line of each. The Lean names are those of the reading guide of the Lean development
(`MhfeLean/Chapters/README.md`) and, for the lemmas, of its sources, with the chapter and line in the
frozen copy; an empty cell means that the development has no statement of its own for the row.
Statements added on 2026-11-12 or 2026-11-13 are marked with their date; the Lean ones exist in the
port only, and their lines are those of the port.

| Text | EasyCrypt | Lean |
| --- | --- | --- |
| Lemmas 1-3 | `invpermK`, `permK`, `lemma2`, `lemma3`, `enc_uniform` | `Lemma1.consistency` (Feistel:359), `Lemma2.uniform_and_independent` (Feistel:113), `Lemma3.network_uniform` (Feistel:474) |
| Theorem 1 | `theorem1`, `theorem1_fixed` | `Theorem1Feistel.joint` (Feistel:571) |
| Theorem 2, suites 3 and 4 | `theorem2` | `Theorem2.bits` (DeniabilityGames:1467), `Theorem2.suite3_error` (DeniabilityGames:1488), `Theorem2.suite4_error` (DeniabilityGames:1499) |
| Theorem 2, a real-wallet record drawn after the disclosed one | `theorem2` | 2026-11-12, port: `Theorem2Records.bits` (DeniabilityRecords:284), `Theorem2Records.independent` (DeniabilityRecords:306) |
| Simulation of a prepared disclosure | `simulation` | `PreparedDisclosure.simulation` (Deniability:144), `PreparedDisclosure.conditional` (Deniability:79), `PreparedDisclosure.failure` (Deniability:96) |
| Lemma G1 | `G1` | `G1.joint_resampling` (ShortSources:419) |
| Lemmas G2-G5 | `G2`, `G3`, `G4`, `G5` | `G2.ordered` (OracleModel:56), `G2.missing_later` (OracleModel:93), `G3.lemma_g3` (ChainEarly:822), `G4.lemma_g4` (ChainCompletion:395), `G5.distinct` (ChainCompletion:501), `G5.twelve_queries` (ChainCompletion:532) |
| Theorem 3 | `theorem3`, `gamma2` | `Theorem3.bound` (ShortSources:897), `Theorem3Randomized.bound` (ShortSources:983) |
| Corollary G6 | `G6` | `G6.bound` (ShortSources:1240), `G6.randomized` (ShortSources:1260) |
| Corollary G7 | `G7` | `G7.bound` (BatchQueries:497) |
| Proposition G8 | `G8`, `G8_top`, `G8_budget`, `G8_bracket` | `G8.weighted` (MatchingAttack:1567), `G8.coarse` (MatchingAttack:1585), `G8.budgets` (MatchingAttack:1626) |
| Remark G9 | `G9`, `refusal`, `refusalK` | `G9Game.probability` (WalletSource:1322) |
| Corollary G10 | `G10`, `G10_derived` | `G10.bound` (WalletData:841), `G10Direct.bound` (WalletData:759) |
| G10, matching attack | `G10_match`, `G10_top`, `G10_budget` | `G10Matching.bound` (WalletMatching:597), `G10DerivedMatching.bound` (DerivedWalletMatching:246) |
| 24-word source without wallet data | `G0_p1` | `G10NoWallet.bound` (WalletData:955) |
| Lemmas K1-K4, inequality (2) | `K1`, `K2_order`, `K2_distinct`, `K2_cross`, `K3`, `K4`, `averaging` | `K1.joint_law` (KnownPairResampling:168), `K2.cross_distinct` (KnownPairCross:634), `K2.cross_bound` (KnownPairCross:674), `K3.early_bound` (KnownPairEarly:532), `K4.lemma_k4` (KnownPairBound:341) |
| Theorem 4 | `theorem4`, `theorem4_coarse`, `ftop_max`, `ftop_attained` | `Theorem4.bound` (KnownPairBound:960), `Theorem4.randomized` (KnownPairBound:973) |
| Proposition K5 | `K5`, `K5_top`, `K5_budget`, `K5_bracket`; the pair lemma `pairK` | `K5.bound` (KnownPairAttack:901), `K5.coarse_bound` (KnownPairAttack:926), `K5.budgets` (KnownPairAttack:951), `K5.refused_bound` (KnownPairAttack:980) |
| Lemma W1 | `W1` | `W1.lemma_w1` (ShortSources:60) |
| Lemma W2 | `W2`, `W2_cut` | `W2Source.generation_bound` (GenerationBound:996), `W2Source.joint_generation_bound` (GenerationBound:1015) |
| Selection rules | `SeqU_pass`, `SeqU_ll`, `selection_eq`, `selection_bound` | `WalletSelection.chosen_eq` (SelectionRules:220), `WalletSelection.actual_eq` (SelectionRules:247), `SelectionRules.joint` (SelectionRules:177) |
| Lemmas W3, W4 | `W3`, `W4`, `theta01` | `W3.resampling` (WalletResampling:144), `W3.joint` (WalletResampling:158); the `W4` namespaces of WalletCollision |
| Theorem 5 | `theorem5_seed`, `theorem5_pair` | `Theorem5.seed_bound` (WalletSource:1559), `Theorem5.pair_bound` (WalletSource:1579), `PassphraseRefusal.seed_bound` (PassphraseDomains:1046), `PassphraseRefusal.pair_bound` (PassphraseDomains:1066) |
| Theorem 5 for a generation that stops at a limit and reports a failure | 2026-11-12: `theorem5_seed_capped`, `theorem5_pair_capped`, `capped_up` |  |
| Corollary W5 | `W5` | `W5.bound` (WalletRecovery:593), `W5Randomized.bound` (WalletRecovery:622) |
| Theorem 5 and Corollary W5 when the sequential generation reveals its trials | 2026-11-13: `theorem5_seed_trials`, `theorem5_pair_trials`, `W5_trials`; `E_pU`, `cc_upto`, `cc_bad`, `uncut`, `disc_game`, `disc_game5` | 2026-11-13, port: `Theorem5Trials.seed_bound` (TrialCount:1182), `Theorem5Trials.pair_bound` (TrialCount:1200), `W5Trials.bound` (TrialCount:1231), `Theorem5TrialsRandomized.seed_bound` (TrialCount:1260), `.pair_bound` (TrialCount:1280), `W5TrialsRandomized.bound` (TrialCount:1311); `TrialDeviation.gap_bound` (TrialCount:991), `WalletCount.close` (TrialCount:599), `WalletCount.completed_loop` (TrialCount:483), `WalletCount.capped_close` (TrialCount:551), `TrialLaws.close` (TrialCount:88) |
| Corollary W6 | `W6_seed`, `W6_pair`, `W6_phrase` | `W6.seed_bound` (OrdinaryWallet:999), `W6.pair_bound` (OrdinaryWallet:1015), `W6.source_bound` (OrdinaryWallet:1032) |
| Proposition W7 | `W7_seed`, `W7_pair`, `W7_top2`, `W7_budget`, `W7_passes`, `W7_bracket` | `W7Source.seed_refused` (WalletPairAttack:1481), `W7PairSource.refused` (WalletPairAttack:1650) |
| Readings of Theorem 5 | `top2_uniform`, `top2_uniform_eq` (2026-11-12), `top2_known`, `theorem5_pair_known`, `theorem5_cost`, `theorem5_cost_uniform` | `UniformTop2.exact_top` (PasswordPairs:97), `KnownPassphrase.top2` (JointCost:30), `KnownPassphrase.pair_main` (JointCost:79), `FullCostRandomized.bound` (JointCost:535) |
| Password encodings and ranking |  | `PasswordDomains.joint` (PasswordDomains:95), `PasswordDomains.combined_execution` (PasswordDomains:300), `PasswordDomains.theorem3` (PasswordDomains:222), `PasswordDomains.admitted_finite` (PasswordDomains:324) |

## Appendix B. Proposed corrections to the text

Line numbers refer to `mhfe_spec/docs/DESIGN-NOTES.md` at SHA-256 `c5f1afdb...caee` and to
`mhfe_spec/README.md` at `50f19a6c...9a6e`. None of these is an error in a result: every bound of the
text has been proved, under the hypotheses of the formal statements (sections 4 and 6). Items 1 to 5
make a sentence say exactly what is proved; items 6 to 9 are optional tightenings or additions.

Status on 2026-11-12: items 1 to 7 are in `mhfe_spec`, commits `ad451b1` (items 1 to 5) and
`6161a3f` (items 6 and 7, after the EasyCrypt statements of K5 and W5 were strengthened to the new
text, section 5.7 and 5.10), item 9 is in `8e8cb66` and item 8 in `98620cc`. The line numbers below are those before the
commits.

1. Theorem 2, the source-length condition (DESIGN-NOTES 184-185, 657-658, 752-753). The bound holds
   for every adversary, in both formalizations; the condition is what makes the comparison with an
   honest 24-word owner meaningful, not a premise of the bound.
   - 657-658, now: "For a source shorter than 24 words, let the adversary have no information about
     the source length beyond what the experiment gives it." Proposed: "The bound holds for every
     adversary. For a source shorter than 24 words, the comparison with an honest 24-word source is
     meaningful when the adversary has no information about the source length beyond what the
     experiment gives it."
   - 752-753, now: "which is why Theorem 2 needs an adversary who does not know the source length."
     Proposed: "which is why Theorem 2 compares with an honest 24-word source only for an adversary
     who does not know the source length."
   - 184-185: the same change ("the comparison assumes" in place of "it assumes").
2. The brackets "the best adversary lies between" (4305-4306 after G8, 4590-4591 after K5,
   5091-5093 after W7). The upper bound applies to the attack only at the attack's own budgets, which
   the sentences name only in part.
   - 4305: "Together with Theorem 3 for `k_A = 12m`, `q_B = 11m + 1`, `q_H = 12m` and `q_G = m`, the
     budgets of the attack, the success of the best adversary with these budgets lies between ...".
   - 4590: "With `m = ⌊k_A/11⌋`, `q_B ≥ 10m + 1` and `q_H ≥ 11m`, the best success therefore lies
     between ...".
   - 5091: "With `k_A = 12m`, `k_S = n` and the attack's other budgets (`q_B = 11m + 1`,
     `q_H = 12m`, and `q_T`, `q_Ω` as above), Theorem 5 gives ...".
3. W7, the check and then Ω (5087). Now: "(`q_T ≤ n`, `q_Ω` the number of passes)". A budget is a
   number fixed in advance; proposed: "(`q_T ≤ n`; `Ω` is asked once per pass of the check, so
   `q_Ω ≤ q_T`)". Both statements are proved in EasyCrypt (`W7_budget`, `W7_passes`).
4. A.1, the password set (3936-3937). Now: "`Pw` is the set of normalized password encodings".
   Proposed: "`Pw` is the finite set of normalized password encodings (at most 1024 bytes each)".
   Both formalizations use the finiteness, and the ranking `p_1 >= p_2 >= ...` needs it or a
   countable set.
5. The specification's conditions for the generation (README 852-855). The list of Theorem 5's
   conditions leaves out that the rule stops with probability 1 whenever a passing phrase exists,
   which the supplement's third condition (DESIGN-NOTES 4694) and both formalizations require.
   Proposed, after "takes a passing one by the order and pass/fail outcomes of its trials alone":
   "stops with probability 1,".
6. Optional: a smaller loss in Proposition K5 (4570-4571 and the proof at 4576-4589). A wrong
   candidate passes only if one of its eleven Argon2id queries returns the key of the real path's
   round-1 point, or its round-1 mask, at a point off the real path, takes one value; so its loss is
   at most `2^-128 + 11·2^-256`, independent of `m`. The text's `δ_K = 2^-128 + 11·(m + 1)·2^-256`
   also charges coincidences with the points of earlier candidates, which the lazy view of its proof
   needs and a view with the functions fixed in advance does not. The Lean development proves the
   smaller loss (`K5FalsePass.probability`) and then enlarges it to the text's `δ_K`.
7. Optional: Corollary W5 (4817-4818). Now: "with `k_S + 1` in place of `k_S` in `ε_W`". The extra
   seed query for the output is not part of the adversary's view, so Lemma W2 applies with `k_S`;
   proposed: "with `k_S + 1` in place of `k_S` in the first term of `ε_W`" (`δ_gen` keeps `k_S`).
8. Optional: Corollary G7 (4258-4264). The final bound also follows by answering each batch with its
   Argon2id queries first and applying the sequential lemmas to the serialized adversary, which is
   how the Lean development proves it. One sentence would give the reader both routes.
9. The specification and the program (README "Generation and recovery", 800-802). The specification
   draws "until the check passes"; the program that draws stops after 64 times the expected number
   of draws and reports a failure, which happens with probability about `e^-64`. (Checked again on
   2026-11-12 against the `main` branches: from version 0.8.0 `mhfe` draws no phrases, and the
   Deriver of `multi-chain-wallet-tools` draws them with this limit; the released `mhfe` 0.7.0
   still draws.) A sentence such as "An
   implementation may stop after a number of trials far above `2^16` and report a failure; the
   phrases it does produce have the distribution of the sequential rule" would make the two agree.
   The optional chosen words, now in the Deriver's draw, give a phrase that
   is not uniform, which the theorems do not cover. The sentence about the distribution is meant for
   fixed functions and a fixed passphrase: a phrase that such a generation produces is uniform on
   the passing set, as with the sequential rule, and a failure produces nothing. The bounds of
   Theorem 5 then hold with a failure counted as no win, which EasyCrypt proves since 2026-11-12
   (`theorem5_seed_capped`, `theorem5_pair_capped`). They are not bounds conditioned on a successful
   generation.

## Appendix C. Rechecking

This appendix records how the machine-local copies were checked. The published files are checked as
the READMEs of `proofs/easycrypt/`, `proofs/lean/` and `proofs/code/` say.

EasyCrypt. `tmp/easycrypt-mhfe-2026-11-09/HANDOFF.md` describes the toolchain. `./check.sh` in that
folder checks the 18 files in strict mode, stops at the first failure with a nonzero status, and
does not start next to a compiled cache (`.eco`), because EasyCrypt accepts an up-to-date cache
without checking the proofs again. `EASYCRYPT` names the executable; `tools/work/ec.sh` and
`tools/work/ec-r2026.10.sh` are the local wrappers for the two versions. `./check-selftest.sh` tests
the script. The scripts of 2026-11-11 remain: `bash tools/work/run-all-main.sh` (summary in
`tools/work/full-main/summary.log`) and the negative controls `bash tools/work/neg/after-full.sh`
(summary in `tools/work/neg/summary.txt`); a run of theirs counts only in a folder without caches.
The sources are identified by `SHA256SUMS` in the same folder.

Lean. The independent rebuild of this report is `bash tools/rebuild-v4.28.sh` and then
`bash tools/lean4checker-v4.28.sh` in `tmp/lean-review-2026-11-11/` (Lean 4.28.0 and the packages
in `workingspace/lean`; results in `out-v4.28/`, `review-axioms/Axioms.log`). The author's own
command is `python3 rebuild-chapters.py --resume` in `tmp/mhfe-lean-setup-2026-11-08/`. The accepted
sources, artifacts and logs are identified by `CONSOLIDATED-SOURCE-MANIFEST.json` there, and the
frozen copy used for this report by `tmp/lean-review-2026-11-11/SHA256SUMS`. The port to Lean 4.35
is `port-v4.35/` there, described in `PORT-v4.35.md`. Its check is `./check.sh` in `port-v4.35/`
(a build of every module from its source, the axiom inventory of `Checkpoint.lean`, a kernel replay
of every chapter; it does not start on top of an earlier build), tested by `./check-selftest.sh`.
The chapter-by-chapter build of the first version of the port is `tools/rebuild.py 4.35.0
mhfe-review-v4.35 port-v4.35 out-v4.35` with `tools/leanchecker-v4.35.sh`.
