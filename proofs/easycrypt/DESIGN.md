# Design of the EasyCrypt development

Working notes on how the text maps to EasyCrypt, kept so that the structure stays fixed while proofs
are written.

## Files (in `src/`)

The files follow the results of the text: each holds one group of lemmas, and each requires the ones
before it. `INDEX.md` maps every result of the text to its statements.

| File | Contents | Text |
| --- | --- | --- |
| `Model.ec` | abstract theory `Feistel`: finite halves, salts, keys and passwords, round indices 0..11, query points, one random oracle `R` for `A, B, H` and its eager form `RE`, the network as a pure function (`perm`, `invperm`) and through oracles (`Net`), Lemmas 1-3, the ranked masses `top`, `p1`, `ftop` and their general lemmas | A.1, Deniability |
| `Suite3.ec` | `Feistel` with 128-bit halves and salts and 256-bit keys | A.1 |
| `Chain.ec` | the backward chain of a password from `Y`, the monitored oracle with batches of `A` queries, the lazy game; Lemmas G2, G3, G5 | A.3 |
| `Collision.ec` | the pair lemma (two inversions of one output under different passwords give the same L_0 with chance at most 2^-128 + 12 2^-256) and the expectation sums shared by the matching attacks (`Ep_swap`, `Ep_sum`, `Ep_dP`, `sum_cands`, `ranked_top`) | A.4, A.6 |
| `OneContainer.ec` | abstract theory `Source` over `ENT`: Γ0, Γ1, Γ2 as challengers, every game as challenger plus play; G1, the refusal step and the up-to-bad step once for every play; the lazy Γ2 for every adversary; G9, Theorem 3, G4, G6, G7, G8, G10, and the bound `p_1` for a 24-word source without wallet data | A.2-A.4 |
| `KnownPair.ec` | Δ0, Δ1_j and Lemma K1 | A.5 |
| `Delta2.ec` | the lazy Δ2 with both chains of every password, their invariants, and the potentials of Cross and K3 | A.5 |
| `Theorem4.ec` | K2 and K4 for every adversary, K3, the averaging inequality (2), Theorem 4, and the refusal step on Δ0 | A.5 |
| `K5.ec` | Proposition K5 | A.5 |
| `Passphrase.ec` | passphrases, seeds, `S`, `T`, `Omega`, pair masses and Lemma W1, the selection interface and the games Θ0, Θ0', Θ1, Θ2 | A.6 |
| `Generation.ec` | Lemma W2 for the rule cut off after `2^80` trials, Lemma W3, the two together as one step from Θ0 to Θ1 (`theta01`, `theta01_out`), the refusal of Θ0 | A.6 |
| `Selection.ec` | the cutoff, the sequential rule of the specification (`SeqU`) and the covered rules; the transfer of every bound from the cut rule to every covered rule; Lemma W2 for every covered rule | A.6 |
| `Theta2.ec` | the lazy Θ2: the chains from `Y`, Coll_P, the potentials of the seed and collision bounds, the pair set Z | A.6 |
| `Theorem5.ec` | Lemma W4, Theorem 5, its readings and the one-cost-budget bound | A.6 |
| `W5W6.ec` | Corollaries W5 and W6 | A.6 |
| `W7.ec` | Proposition W7 | A.6 |
| `PassRate.ec` | the share `p_U` of passing values as a sum over all states; its second moment over the random `S` and `T` (`ET_dev2`, `ES_coll`); `E|p_U - 2^-16| <= 2^-136 - 2^-154` (`E_pU_tight`) | A.6, the number of trials |
| `TrialGames.ec` | the chain of `Selection.ec` (whole functions, outcome first, values drawn when read) for a continuation that receives the outcomes (`CONTO`, `GenGameO`, `chainO`) | A.6, the number of trials |
| `TrialCoupling.ec` | outcomes as thresholds `r < |U|` and `r < 2^240` of one uniform `r`; the coupled game `CC` of the cut sequential rule padded to `2^80` steps; up to bad (`cc_upto`); the chance of a disagreement by expected-value Hoare logic (`ccb_e`, `cc_bad`) | A.6, the number of trials |
| `TrialFake.ec` | the run with `2^-16`: the selected value drawn from the passing values whatever the outcomes (`cc_cf`), the trials of the run moved into the continuation (`CB`, `cf_preb`), the target game by `SeqU` (`fro_kb`, `kb_pre`), the chance that all `2^80` such trials fail (`fl_cut`); the uncut rule against the cut one (`uncut`) | A.6, the number of trials |
| `TrialCount.ec` | the games with the outcomes revealed (`GamePRO`, `Game5O`), the reductions `BO`, `BO5`; Theorem 5 (a), (b) and Corollary W5 with `2^-120` added (`theorem5_seed_trials`, `theorem5_pair_trials`, `W5_trials`) | A.6, the number of trials |
| `Deniability.ec` | abstract theory `Denial`: honest and prepared experiments; Theorems 1, 2 and the simulation | Deniability |
| `Instances.ec` | `Source` for 12-, 15-, 18-, 21- and 24-word sources, `Denial` for suite 3 at the same five lengths and for suite 4 at 12, 15, 18 and 21 words; every theory axiom realized | |

## Conventions

- One lazily sampled random oracle answers every query point of `A`, `B` and `H`; each function
  reads its own component of the answer. A table hit is then the same test for all three functions,
  and the bookkeeping of a chain is one procedure.
- Domains are finite as in A.1, so `PROM.FinEager` can replace the lazy oracle by a whole function
  sampled in advance. The exact re-sampling lemmas (G1, K1, W3, Theorem 1) are proved there, from
  Lemmas 1 and 2, and moved back to the lazy oracle.
- A game is a challenger followed by a play (`Game(S, C)`). The challenger draws the secrets and the
  container, the play runs the adversary and decides. Lemma G1, the refusal step and the up-to-bad
  step are proved once for every play; each result then needs only its own play and assembly.
- Budgets are `hoare` judgments on counting wrappers for every oracle implementation, so they can be
  transferred to wrapped adversaries. Repeated queries count.
- The chain monitor records `c_1 ... c_36` as they become defined, the adversary's queries with
  their batch numbers, and Early_P. It is invisible to the adversary and only reads the table.
- Argon2id queries may come in batches (`abatch`); every other call is a batch of its own. Lemma G2
  is stated with batch numbers, which serves Theorem 3 and Corollary G7 at once.
- Lemma W2 and the selection rules use a judge that sees the secrets after the adversary's run, so
  one statement covers every event of the text.
- Intermediate games of one proof are `local` modules of its section, which the declared adversary
  cannot access. Modules shared between files are listed in the restrictions.

## Changes after the statement review

The first reviewer compared the skeleton with the text (findings F1-F17):

- F1: `averaging` was false, because the chains stop growing at Early_P. Early_P is now part of the
  event under the sum, and it is charged once, by Lemma K3, as in the text.
- F2: the budget lemmas of G8 and K5 assume `0 <= m`.
- F3: `top` and `top2` are the ranked sums of the text, and Lemma W1 is the text's statement.
- F4: shared modules are listed in every restriction; the intermediate games of each proof will be
  local modules.
- F5, F16: Lemma W2 uses a two-phase adversary whose judge sees the secrets after the run.
- F6: W7 is stated over declared constant lists, so its proof can wrap the attack for W2.
- F7: one refusal lemma for every play on Γ0 and one for every play on Δ0.
- F8: the generation takes a selection rule. The text's claim that a covered rule gives the same joint
  distribution as the sequential rule holds only for a sequential rule without a cutoff; the formal
  sequential rule stops after `2^80` trials. `selection` therefore bounds the difference of any
  probability of a distinguisher on the two generations by the chance that the sequential rule
  reaches its cutoff without a pass, and `selection_bound` by `2^-256` (`seq_cutoff`, as the text's
  count of trials). The proof samples `S` and `T` as whole functions, draws each trial as its
  outcome first and its value given the outcome (`marginal_sampling_pred`), defers the values to a
  lazy oracle read only at the selected index (PROM, `RO_LRO`), and moves the selection after the
  run, where a covered rule passes exactly when some value passes.
- F9: Corollary W6 has the phrase form `W6_phrase`.
- F10: `Instances.ec` realizes every axiom of the abstract theories.
- F11: `mass_top`, `top_mono`, `ftop_max` and `ftop_top` in `Model.ec`.
- F12: `K5_top`, `W7_top2`, `G10_budget`.
- F13: Lemma 1 holds for any function; Theorem 1 is stated for the random oracle.
- F14: recorded in `ASSUMPTIONS.md`.
- F15: the statements that are stronger than the text (any source length in `[128, 256]`, any
  candidate order in the attacks, repeated queries counted, batches only for Argon2id queries) were
  checked to be true and kept.
- F17: the Feistel inverse is `invperm`; Passphrase's widths are concrete words, and the passphrase
  type is the one remaining assumption there.

The second reviewer checked the revised skeleton. Changes:

- The up-to-bad step needs the play to terminate (`C_ll`): otherwise Γ1 and Γ2 can differ after Bad
  in whether they halt. The refusal steps need the play and the continuation to terminate (`Rf_ll`,
  `Rh_ll`, `Rp_ll`); the continuation is no longer forbidden to run the adversary again.
- Restrictions completed for K1, the refusal on Δ0, W2, W3, W5 and W6; the selection rules accept a
  continuation that reads the other tables, so Theorem 5 and W2 transfer to every rule.
- W3 is stated for a continuation that also sees `S` and `T`.
- The two up-to-bad statements of Θ1 and Θ2 are one lemma for every event of the output and the
  secrets.
- G10's checksum-aware form reads `G` at `E` itself, so it gets its own Γ0-Γ2 steps instead of the
  shared ones.

## Changes during the proofs

- The monitor keeps the backward chains of all passwords (`Bwd.sts : pw -> cst`) and the game records
  the real password `Bwd.p` after the adversary's run, which does not use it. The chain of the text is
  `Bwd.sts Bwd.p`; G2, G5 and `chain_end` are stated on it. This lets the proof of G3 draw P after the
  run. The known-pair game keeps its forward chains the same way (`Fwd.sts`).
- `Mon.odd` is a flag for the proof of G3: after the run, a fresh query that is not the next point of
  the real chain. It is never set (`run_inv`).
- `shape` also records that a last B or H point belongs to the current round.
- G3 assumes `0 <= qB` and `0 <= qH` besides `0 <= kA`: the budgets are counts.
- G3 is proved in expectation logic (`ehoare`). The potential of the run is the expected remaining
  risk of the chain of a password drawn from `dP`, plus the unused budgets. A submitted query raises
  it by at most its share of the budget; a fresh answer keeps it in expectation. Its value at the
  start is the bound of G3.
- The game with P drawn after the run (`ChainLate`) and its equivalence with the lazy game are
  shared, because the term `top(...)` of Theorem 3 also needs P independent of the run.
- G4 is proved in expectation logic as well. After the run the potential is `|Q_G| * 2^-128` until
  the last mask of the real chain is sampled; it is 0 once the chain is complete and its last point
  was queried by the adversary, and 0 on Early_P. The decryption keeps it in expectation. G4, Theorem
  3 and its corollaries assume `0 <= q_G` (and `0 <= q_B`, `0 <= q_H`).
- The budgets of the adversary are stated on `CountG(O)`; the lazy game wraps it as `AG`, whose
  oracles count G themselves. An equivalence carries the budgets over (`AG_eqv`).
- Inequality (1) of A.3 is one lemma for every play (`ineq1`). Corollary G6 wraps the adversary so
  that its output becomes one more G query and applies the Bad bound of Theorem 3 with `q_G + 1`.
  Corollary G7 adds to the lazy game that the logged A queries lie in at most `CountB.dp` batches,
  so Comp(P) without Early_P needs twelve calls with A queries.
- Corollary G10 is reduced to Theorem 3: Γ1 and Γ2 differ in Ω only at `e*`, so an up-to-bad step
  for Ω queries at `e*` comes first; then the adversary draws `ω*` itself and submits each Ω query
  to G as well (`AWX`), which by `RO_LRO` does not change the distribution of its view. Its budget
  hypothesis now counts every call for any implementation of the oracles (`CountW`), so that it
  carries over to `AWX`; the skeleton fixed Ω to the table of `RW`.
- The checksum-aware form of G10 reads G at `E` in the game itself, so its first step goes from Γ1
  straight to Γ2 with `ω*` drawn on its own, up to a G query at `e*` or a D query at a phrase
  whose entropy is `e*`; then the same reduction as for G10 applies, with the count `CountD`.
- The known-pair monitor logs its queries with batch numbers, one per call, like the one-container
  monitor, so the invariants of `Chain.ec` serve both. Lemma K2(1) is stated with `ordered`: the
  preceding point was queried in a strictly earlier call.

## Changes in the third round

- The sequential rule `Seq` stops after `ntr = 2^80` trials and then selects its last trial. The
  proof of Lemma W2 works on this cut rule, where the text gives a run that long any outcome. Since
  the review of 2026-11-11 the statements are for every covered rule, including the text's rule
  without a cutoff (`SeqU`); the cut rule is a device of the proofs (see the last section).
- Lemma W2 is proved through four games. `R0` is the real generation with ghost copies of the trial
  samples. `G2` checks each trial with its fresh 16 bits only and programs `S` and `T` at the passing
  trial alone; the two agree until the passing trial repeats an earlier trial point, the cutoff, or
  an adversary query at a rejected trial point (`splitwhile` on the first event, then an up-to-bad
  call). `DG` draws the trial values from three random oracles indexed by the trial number, which
  `FullEager.RO_LRO_D` turns lazy: the rejected values are drawn after the adversary, where their
  probability of meeting its queries is at most `(1 + k_S) 2^-256 + (1 + q_T) 2^-512` each. The
  expected number of rejected trials and the cutoff together are bounded by a potential over the
  trial loop (`phiL`), `2^16 K + (1 - 2^-16)^(2^80)`, and `(1 - 2^-16)^(2^80) <= 2^-256` follows
  from Bernoulli's inequality. The total is at most `2^17 K + 2^-255 <= δ_gen`.
- W2 assumes `0 <= k_S` and `0 <= q_T`; Theorem 5 assumes `0 <= q_T` as well (budgets are counts).
  The judge's budget hypothesis starts from all counters at zero, as after `CountP(IP).init()`.
- EasyCrypt r2026.10 closes a section by generalizing every lemma over all declared axioms of the
  section, used or not. `Chain.ec` therefore has two sections: the chain lemmas (G2, G5, `run_inv`,
  `chain_inv`, `chain_end`, `log_count`, `batch_count`, `comp_depth`, `chain_late`) for any
  adversary, and G3 with the budget hypothesis. The unused hypothesis `B_ll` is gone.
- `psiC_ge0` and the lemmas of W4 that use it assume `0 <= k_A`, which W4 has.
- `col2_nonA` assumes that the table and the log hold the same points; inclusion of the log in the
  table is not enough when the new query repeats a point of the table that the adversary never
  queried.
- Deniability, `simulation`: when `P` carries all the mass of `dP`, the redraw of the decoy has no
  outcome and the bound `mu1 dP p >= 1` holds trivially; the proof treats that case first, so no
  assumption on `dP` is added.
- The goals of `conseq (_ : P1 ==> Q1) (_ : P2 ==> Q2)` on a hoare goal come in the order of the
  second specification first in r2026.10; the proofs of `AG_bounded` and `AP_bounded` follow it.
- The judge of W2 sees only `A`, `B`, `H` and `W` (its module type says so), so its termination
  hypothesis asks only that these four terminate; the hypothesis of the run asks it of all six. The
  up-to-bad step for the judge needs exactly that form.
- In expectation logic (`ehoare`) r2026.10 accepts a call only when its result goes to a local
  variable. `AP` therefore stores the adversary's output in a local variable first and then in
  `AP.out`.
- The continuation after a refused creation (`Rf` of Theorem 5 and Corollary W5) cannot access
  `Gen`, the game's record of the secrets; it receives `P`, `Q` and `Y` as arguments. Otherwise
  EasyCrypt cannot relate the secrets before and after a call to an arbitrary module, and the events
  of Theorem 5 are read on `Gen`.
- Corollaries W5 and W6 for the phrase use a wrapper `AW5` that records the guess `(e, q)` in its own
  variable and submits it as one more `S` query. The up-to-bad step and the lazy `Θ2` hold for every
  event of the adversary's state (`glob A`), so the event "the recorded guess is `(E, Q)`" is carried
  from `Θ0` to `Θ2`, where it is a query of `S` at `(e*, Q)`, which is Bad. The bound is the text's,
  without a term for guessing `seed*`. Lemmas W2 and W3 see the guess through a judge and a
  distinguisher that read the wrapper's variable. The refusal step is written once per setup: an
  abstract setup may write `Gen`, so EasyCrypt cannot relate the secrets across its call.
- Corollary W6 replaces `Θ0` by `Setup0O` (E uniform, `seed* = S(E, Q)`, no check value). Lemma W3
  holds for it without `T` (section `W3O`), and `Θ1` without `T` (`Setup1O`) meets `Θ2` until a query
  of `S` at `(e*, Q)` or of `Omega` at `seed*`; no Lemma W2 is needed, since there is no selection.

## Changes in the fourth round

- Strict rechecks found gaps that weak mode had hidden: the invariants of `late_top` and `late_topP`
  read a stale variable; `/#` in `g6_bad` admitted a program goal; `upto_w` had an unprovable call
  precondition and did not track `WithWB.badw`; `upto_d` claimed more than its invariant keeps. All
  are proved now. `upto_d` states only what the text uses: the bad events agree and, without them, the
  results agree.
- OneContainer: the adversaries of G10 and G10D are restricted from the counters `WithW.cw` and
  `WithD.cd` (not from the whole wrapper modules), and `RG` gets the types of a distinguisher. The
  derived-key game is reduced to `PlayDG`.
- Model: `net_ll` (the network terminates when its oracles do), `dstate_full`, `mu1_p1` (moved from
  Chain), and `masks_uniform`: twelve rounds with fresh masks give a uniform state.
- Theorem 2 follows the games of the text. G1 and G3 are the experiments without refusal and redraw,
  at a cost of `2^-W + p1` and `2^-W`. G2 answers the encryption's A points at P and H points at the
  keys from a private table `RP`; G1 and G2 agree until the adversary or the decryption queries a
  private point (`Bad.ah`) or looks up the real phrase (`Bad.lk`). G2's result and `Bad.lk` are
  those of `GL`, where the real source is drawn after the run (eager oracle, `RG` made lazy); a
  lookup then hits it with probability at most `l 2^-ENT`. `GL` is Theorem 1's bijection applied to
  G3. For `Bad.ah`, a separate oracle `RK` indexed by round gives the twelve keys; the masks are
  fresh, so through `FinEager` the keys and the password are drawn after the run, and the hits are at
  most `(k + 1) p1 + 12 (q + 12) 2^-256`. Theorem 2 assumes `0 <= k`, `0 <= q` and `0 <= l`, and its
  adversary is restricted from the proof's oracles `RP`, `RK` and `RKE.FunRO` as from the others.
- KnownPair: the forward bookkeeping `Fwd` has a ghost flag `odd`, set by `Mon2.query` when a query
  of the finalization is fresh and not the next point of the chain being evaluated (`oddq`). The
  game `KPGame` is unchanged; the flag is never set (`run_inv3`) and serves Lemma K3 as `Mon.odd`
  serves G3. K3 needs no premise beyond `0 <= k_A`: `0 <= q_B` and `0 <= q_H` follow from the
  adversary being lossless and bounded (`ge0_budgets`).

## The matching attacks (K5, G8, G10, W7)

The lower bounds are `ehoare` proofs of `!res` (the attack fails) with a potential over the attack's
loop. All four make A, B and H a whole function drawn first (Lemma G1 or W3, then `RO_FunRO`; K5
directly): the inversions of the candidates are then deterministic. In G8, G10 and W7 only the test
oracles (G, Omega, S, T) are lazy; in K5 nothing is, its test compares two values of the function,
and its potential sums the acceptance indicators of the candidates before the real one, bounded at
the start by the pair lemma of `K5.ec` (since 2026-11-12; before, K5 kept the oracle lazy and paid
for every key of round 1 in the table). The potential is the sum over the untested candidates (or
pairs) before the real one of their pass probability: the test's chance (2^-r, 2^-(r + lambda), tw +
2^-512) while its points are unqueried, its outcome once they are queried, and 1 if its inversion
meets e*. A fresh answer keeps the sum in expectation (`Ep_sum`). At the start the candidates whose
inversion meets e* are bounded through the pair lemma of `Collision.ec` after moving the expectation
over the function inside (`Ep_swap`); `sum_cands` (or `sum_pairs`) turns the expectation over P into
the text's sum over the candidates.

## Proof plan

- `Model.ec`: the general lemmas on ranked masses, and Lemma 3.
- One container: G1 through the eager oracle and Lemma 2; the refusal step from G9; the up-to-bad
  step; the lazy Γ2 through the eager oracle; the chain lemmas G2, G5, then G3 by expectation over
  the run (`ehoare` or a direct sum over the steps of the chain); G4; the assembly. Then G6, G7, G10
  as plays reduced to Theorem 3's Γ2 lemmas, and G8.
- Then Theorem 4, Theorem 5 and Deniability, reusing the same pieces.

## Changes after the statement review of 2026-11-11

Five reviewers compared the statements with the text (their reports are not published). The
changes:

- The text's generation, the sequential rule without a cutoff, is the module `SeqU`; `SeqU_pass` and
  `SeqU_ll` show that it is a covered rule. `selection_eq` proves the text's claim exactly: every
  covered rule gives the same probability as `SeqU`, for every halting distinguisher. Lemma W2,
  Theorem 5, Corollary W5 and Proposition W7 are now stated for every covered rule, and so for the
  text's Θ0, with the text's bounds. Their proofs go through the rule cut off after `2^80` trials:
  W2's own constant `deltacut` is below `δ_gen` by more than `2·2^-256` (`deltacut_le`), which pays
  for the transfer (`rule_up`, `rule_lo`: the run without the refused branch and the refusal are both
  distinguishers of the generation, so `selection_bound` applies to each).
- One cost budget (A.6): `theorem5_cost` bounds the seed recovery of an attacker whose Argon2id calls
  cost `cA` and seed computations `cS`, at most `c` in all on every run, by `T + ε_W + 2^-512` for
  every `T` that bounds `top2(m, n)` when `12 cA m + cS n <= c`, with `ε_W` at `floor(c / cA)` and
  `floor(c / cS)`; `theorem5_cost_uniform` is the text's reading for uniform secrets. The text writes
  the main term as an expectation over Θ2; the formal one is a bound valid on every run of Θ2, which
  is what the text's consequences use. The Z-set lemma takes any budget predicate of the run.
- Reading for uniform secrets: `top2_uniform` (via `top2_le`). Proposition W7 has its top2 forms for
  both games and all three tests (`W7_top2`).
- `G10_top`: the top form of G10's matching attack.
- Remark G9: the refusal lemma of Γ0 now admits plays that read `G`, so it covers the checksum-aware
  form of G10 as well; Theorems 3 and 4 and Corollaries G6, G7 and G10 with refusal are `refusal`
  (or `refusalK`) applied to their play, plus the theorem.
- `G0_p1`: for a 24-word source (`r = 0`) without wallet data, Γ0 equals Γ2 (programming `G(e*)`
  with a fresh rest is a fresh answer, `RO_LRO`), and the adversary wins with probability at most
  `p_1`, with no budget.
- `theorem1_fixed`: Theorem 1 for any fixed functions (the eager oracle without its initialization).
- The real wallet's record depends on every value of the prepared experiment (`dReal e p x y q xd
  rc`).
- Lemmas K2 and K4 are in a section without budgets and termination (`K2K4`), and the lazy Γ2 in one
  without budgets (`LazyGamma2`), so their closed statements carry no hypothesis the text does not
  have. Theorem 5's section no longer declares a continuation it does not use.

## The remaining review items and the merged transfers

Later on 2026-11-11 the items that the review had left open were closed and the near-copies were
merged.

- A known passphrase (A.6): `top2_known` proves `top2(m, n) = top(min(m, n))` when `s_1 = 1`
  (`sr_known`: every other passphrase then has probability 0). The upper bound uses `top_sum_ex`,
  the converse of `top_sum`: the `n` largest values of a list are the values of `n` of its entries.
  `theorem5_pair_known` is the text's reading of part (b), `top(min(k_A/12, k_S) + 1) + ε_W`.
- `ftop_attained`: `T(x)` is reached by weight 1 on the first `floor x` ranked passwords and
  `x - floor x` on the next one, so with `ftop_max` it is the largest weighted sum, as the text
  defines it.
- `W7_passes`: with the check first and Ω after a pass, the attack's Ω queries are exactly the
  passes of the check, counted by a wrapper (`Passes`) around the oracle `T`.
- The brackets "the best adversary lies between": `G8_bracket`, `K5_bracket` and `W7_bracket` put
  the attack's success between the attack's lower bound and the bound of Theorem 3, 4 or 5 at the
  attack's own budget (`k_A = 12m` with `q_B = 11m + 1`, `q_H = 12m`, `q_G = m`; `k_A = 11m` with
  `q_B = 10m + 1`, `q_H = 11m`, where `T(1 + k_A/11) = top(m + 1)`; `k_A = 12m`, `k_S = n`). The upper
  bounds (`G8_upper`, `K5_upper`, `W7_upper_cut`) apply the theorem to the attack with its candidate
  list fixed by a local wrapper: the theorems ask for the budget from every initial memory, and the
  attack reads its list from a module variable. The attacks halt whenever their oracles do
  (`match_ll`, `matchK_guess_ll`, `matchp_ll`). The bracket of W7 is for the seed game, as in the
  text.
- Instances: the abstract theories are realized at every source length the text names. `Short3`
  builds a suite 3 source of `128 + a` bits for `0 < a < 128` (`pack(E, v) = E || v` through a
  bijection between the remaining `a` bits with the verifier and the right half) and is cloned for
  15, 18 and 21 words; `Suite4` builds suite 4 at a half width `hw` and is cloned for 12, 15, 18 and
  21 words. A suite 3 phrase carries its length (`phrase3`: a full state or a shorter source).
- Lemmas W2 and W3 are combined once: `theta01` bounds the difference between Θ0 with the cut rule
  and Θ1 for every judge, `theta01_out` for every event of the adversary's output and the secrets.
  Theorem 5 (seed and pair), Corollary W5 and Proposition W7 (seed and pair) use it; before, each of
  the five carried its own copy of the two equivalences. In W7 the attack with its lists fixed (`M7`)
  is the adversary, and `fixed7` relates it to the attack in a memory that holds the lists.
- Not merged: the potentials of G8 and G10, and of W7's seed and pair games. Each pair shares the
  loop over the candidates and the inversion, but the potentials differ at every step (one table or
  two; a wrong pair that yields `seed*` wins the seed game and loses the pair game), G8's game has no
  Ω oracle, and the expectation logic states a step only for a concrete sampling. A common proof
  would need a flag with a case split at each step and would be longer to read than the two.

## Changes of 2026-11-12: the corrected text and the audit AUD-011

- Corollary W5 keeps `kS` in `deltagen`: the judge `J5` of the step from Θ0 to Θ1 runs the adversary
  alone, and the wrapper's seed query at the guess comes after it.
- Proposition K5 is proved on the whole function, in the style of G8, with the loss
  `deltaK = 2^-128 + 11·2^-256` for every number of candidates: the pair lemma for one wrong
  candidate (`two_k_e` in the lazy oracle, `pairK` over the function), then a potential that sums the
  indicators `accK` of the candidates still to be tested before P (`coreK_e`).
- The reading for uniform secrets is exact: `top2_uniform_eq` gives
  `top2(m, n) = min(n, min(m, N1)·N2)/(N1·N2)`. The pairs of the first `min(m, N1)` passwords weigh
  `1/(N1·N2)` each and the others nothing, so `top_sum_ex` bounds the sum from above and `top_sum`,
  applied to the first `n` of those pairs, from below.
- A generation that stops at a limit and reports a failure: `SeqF` returns the index of the first
  passing trial among at most `n`, or none, and `GameF` is Θ0 with that rule, where a failure runs no
  adversary. `capped_up` bounds every event of `GameF` by the same event with the cut rule plus
  `2·2^-256`, for every `n`: the two rules run the same trials up to `min(n, 2^80)`; a failure wins
  nothing; and the rule with the limit selects a later trial only when the cut rule ends at its
  cutoff without a passing trial (`seq_cutoff`), or the creation is refused. The room that
  `deltacut_le` leaves inside `delta_gen` pays for both, so `theorem5_seed_capped` and
  `theorem5_pair_capped` state the text's bounds.
- `check.sh` replaces the loop of the README, which returned success after a failed compilation,
  and refuses a source folder with compiled caches, which EasyCrypt accepts without checking the
  proofs again; `check-selftest.sh` tests it.

## Changes of 2026-11-13: the number of trials (specification `3d88078`)

The specification lets a generation under the wallet-check profile reveal the pass/fail outcomes of
its trials, their number and a duration that depends only on these, and states that every bound of
Theorem 5 and Corollary W5 then holds with `2^-136·n` added (`2^-120` for the sequential rule). The
proof follows the text: one uniform number per trial decides its outcome both with `p_U` and with
`2^-16`; the two runs differ only when the number falls between the two thresholds, which each trial
does with probability `|p_U - 2^-16|`, so the chance is at most `2^16 E|p_U - 2^-16|`; with `2^-16`
the outcomes are independent of everything else and the adversary draws them itself.

Two technical choices. The coupling runs the rule cut off after `2^80` trials, padded to exactly
`2^80` steps so that both runs stay in step after they differ: EasyCrypt's relational logic does not
couple a loop that may run forever with one that stops. The uncut rule is reached at the end
(`uncut`) by moving its remaining trials behind the rest of the game, where they no longer change
the result. Both detours cost `2^-256`, absorbed in the slack of `E_pU_tight`. The general rule with
`n` expected trials and the `w`-worker case are not stated (README, "Where the formal statements
differ from the text").

After the review of the same day (finding Low-1 of its record, which is not published) the
response after a refusal is no longer restricted beyond Theorem 5's `{-Gen}`. The
coupling chain runs a continuation that counts a refused attempt as a win (`CW`, `CW5`), and the
reduction answers a refusal with a response that always wins: the seed of the refused container,
which is the entropy (`RwSeed`, with `setup_seed`), the pair (`RwPair`) or the phrase (`Rw5`). Any
other response wins at most as often, so the constants are unchanged.

