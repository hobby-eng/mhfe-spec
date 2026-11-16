# Assumptions of the EasyCrypt development

Every `axiom` of `src/` is listed here. None states a security property or a bound. Each one fixes a
type, a width or a distribution of the model, or is a hypothesis of a section that the lemmas of that
section are conditional on.

## Theory parameters

The axioms of the abstract theories are realized by concrete bit strings: `Suite3.ec` for the
model, and `Instances.ec` for `OneContainer.Source` (12-, 15-, 18-, 21- and 24-word sources) and
`Deniability.Denial` (suite 3 with a source of each of these five lengths, and suite 4 with a 12-,
15-, 18- or 21-word source). So none of them is contradictory at any source length the text names.
The 15-, 18- and 21-word cases come from two theories with a width parameter (`Short3` for
`0 < a < 128` further bits of entropy, `Suite4` for any half width), each cloned at the three or four
values. The wallet data of the `Source` instances is 128 bits wide; the theory is abstract in `λ`.
The password axioms `PwT.enum_spec` and `dP_ll` stay abstract (below).

| File | Axioms | Meaning | Realized |
| --- | --- | --- | --- |
| `Model.ec` (theory `Feistel`) | `xorA`, `xorC`, `xor0`, `xorK` | halves form a group under xor | `Suite3.ec`, `Instances.ec` |
| | `HalfT`, `SaltT`, `KeyT`, `PwT.enum_spec` | halves, salts, keys and passwords are finite types | the first three in `Suite3.ec`; passwords below |
| | `dhalf_*`, `dsalt_*`, `dkey_*` | uniform halves, salts, keys | `Suite3.ec`, `Instances.ec` |
| | `dP_ll` | the password distribution is a probability distribution | passwords below |
| `OneContainer.ec` (theory `Source`) | `ENT_r`, `ENT_range` | `ENT + r = 256`, `128 <= ENT <= 256` | `Instances.ec`, `ENT` = 128, 160, 192, 224 and 256 |
| | `dent_*`, `dver_*`, `drest_*` | uniform `ENT`-bit entropy, `r`-bit verifier and the rest of a `G` output | same |
| | `unpack_pack`, `pack_unpack`, `lead_pack` | `pack(E, v) = E ‖ v` is a bijection onto states whose first half is the first 128 bits of `E` | same |
| | `ddata_ll`, `ddata1` | uniform `λ`-bit wallet data (assumption 6 of A.1) | same |
| | `ent_of_phr` | a phrase determines its entropy | same |
| `Deniability.ec` (theory `Denial`) | the `Feistel` axioms, `dstate1`, `dkey1` | state width `W`, 256-bit keys | `Instances.ec`, `W` = 256 (suite 3) and 128, 160, 192, 224 (suite 4) |
| | `dent_*`, `dver_ll`, `drest_ll` | the real source | same |
| | `ph_inj`, `phE_inj` | a phrase determines its state or its entropy | same |
| | `dU_ll`, `dReal_ll` | the usage scenario and the real wallet's use produce records | same |

## Assumptions that stay

| File | Axiom | Meaning |
| --- | --- | --- |
| `Suite3.ec` (from `Model.ec`) | `PwT.enum_spec`, `dP_ll` | passwords are a finite set with a probability distribution. The text's `Pw` is the set of normalized encodings of 1 to 1024 bytes, which is finite. |
| `Passphrase.ec` | `PpT.enum_spec`, `dQ_ll` | BIP39 passphrases are a finite set with a probability distribution. **This narrows the text**, which allows a countable list `v_1, v_2, …`; every implementation bounds the input length. It is used for the ranked `top2` and for the selection rules, where `S` is sampled as a whole function. |
| `Passphrase.ec` | `gt0_lambda` | the width `λ` of the wallet data is positive |

Assumptions 1-5 and 7 of A.1 (uniform independent functions, HMAC as a random function, nothing
leaks from the owner's computations, independent secrets, uniform seeds and check values) are not
axioms. They are built into the games: each function is an independent lazily sampled random oracle,
the secrets are drawn independently, and the adversary's view is exactly what the game gives it.

The round index of `B` and `H` ranges over 0..11, as in A.1. The functions `A`, `B` and `H` are one
random oracle on their query points; each reads its own component of the answer, so they are
independent uniform functions.

Theorem 1 is stated for the random oracle (`theorem1`) and for any fixed functions
(`theorem1_fixed`: the functions are those of the eager oracle in the initial memory).

The real wallet of the prepared experiment produces its record as `dReal e p x y q xd rc`: any
distribution given the source, the password, the state, the container, the decoy password, the
disclosed state and the decoy's record. The text lets the real wallet be "used in any way"; its
record is shown only through a lookup of the real phrase, which is a bad event of the proof.

## Section hypotheses

Each lemma about an adversary holds for every adversary module that satisfies the hypotheses of its
section:

- `A_bounded`, `B_bounded`, `D_bounded`, `J_bounded`: the query budgets hold on every run, for every
  implementation of the oracles; repeated queries count.
- `A_ll`, `D_ll`, `J_ll`, `O_ll`, `C_ll`: the adversary, or the play that runs it, terminates
  when its oracles do (the text's "when it halts"). The judge of W2 calls only `A`, `B`, `H` and `W`,
  so `J_ll` asks those four to terminate for the judge and all six for the run.
- `Rf_ll`, `Rh_ll`, `Rp_ll`: whatever the owner does after a refused creation, or after drawing a
  decoy equal to the password, terminates. The text allows every continuation; one that does not
  terminate only lowers the probabilities, but EasyCrypt's relational logic compares two games only
  when both terminate. The continuation may run the adversary again. In Theorem 5 and Corollaries W5
  and W6, and in their forms with the number of trials, it cannot access `Gen`, the game's record of
  the secrets, against which the events are read; it receives `P`, `Q` and `Y` as arguments.
- `Rw_ll`, `Rw_win` (section `DiscGame` of `TrialCount.ec`): the lemma `disc_game` holds for any
  response `Rw` after a refusal that terminates and wins the event when it is called with `Y = E`,
  the secrets `P`, `Q` as arguments and the seed stored at `(E, Q)`. No final statement carries
  them: the trials theorems instantiate `Rw` with `RwSeed` and `RwPair`, which meet both
  (`RwSeed_ll`, `RwSeed_win`, `RwPair_ll`, `RwPair_win`), and `disc_game5` uses `Rw5` directly.
- Budgets for every implementation of the oracles exclude only adversaries whose counts exceed the
  budget on answers the real oracles never give (for example inconsistent answers to a repeated
  query); such an adversary can cap its own counts and halt on an inconsistency without changing its
  behaviour on the real oracles, so nothing the text covers is lost. The same holds for termination.
- `cA`, `cS`, `c`, `gt0_cA`, `gt0_cS`, `A_cost` (one cost budget): Argon2id calls cost `cA > 0`, seed
  computations `cS > 0`, and their total cost is at most `c` on every run, for every implementation
  of the oracles; the other budgets are as in Theorem 5.
- `Rl_pass`, `Rl_ll`, `D_ll` (selection rules): the rule selects a passing trial by the outcomes
  alone, for every source of trials whose outcomes are recorded (`Rec`); it stops with probability 1
  whenever the source keeps a state in which every trial passes with the same positive probability
  (the state is a predicate on `glob T`, since the pass probability of the generation depends on `S`,
  `T` and `Q`); and the distinguisher of `selection` halts when its oracles do. The distinguisher
  also cannot access the oracle tables or `Gen`. These are the text's four conditions; the text's
  own rule satisfies them (`SeqU_pass`, `SeqU_ll`). In the statements for every covered rule (W2,
  Theorem 5, W5, W7) the rule cannot access the counters or the attack, and the adversary cannot
  access the rule (condition 4).
- Module restrictions (`{-...}`): the adversary cannot read the game's private variables or the
  oracle tables directly. In Corollaries W5 and W6 for the phrase it also cannot access `AW5`, the
  wrapper of the proof that records its guess.

## Premises of the statements

Some lemmas assume that a budget is not negative, since budgets are counts: G3, G4 and Theorem 3
assume `0 <= k_A`, `0 <= q_B`, `0 <= q_H` and `0 <= q_G`; Lemma W2 assumes `0 <= k_S` and
`0 <= q_T`; Theorem 5 and Corollary W5 assume all six budgets non-negative (`bad_TW` needs
`0 <= q_T` and `0 <= q_W`, without which its bound would be negative); `psiC_ge0` and the lemmas of
W4 that use it assume `0 <= k_A`; Theorem 2 assumes `0 <= k`, `0 <= q` and `0 <= l`. Lemma K3 and
Theorem 4 assume `0 <= k_A`; there `0 <= q_B` and `0 <= q_H` are derived from the adversary being
lossless and bounded (`ge0_budgets`), not assumed. Corollary W6 likewise assumes `0 <= k_A` and
derives `0 <= q_B`, `0 <= q_H`, `0 <= k_S` and `0 <= q_W` (`ge0_budgets6`).

The matching attacks assume their candidate lists as the text states them: Corollaries G8 and G10 and
Proposition K5 take distinct candidates (`uniq ws`, `size ws = m + 1`); Proposition W7 takes distinct
passwords and distinct pairs, each pair's password among the passwords (`uniq ws0`, `uniq pairs0`,
`all (fun x => x.1 \in ws0) pairs0`), and `0 <= mode0 <= 2` selects the test of T, of Omega, or of
both.

The top forms of the attacks assume that the candidates exist: `G8_top`, `G10_top` and `K5_top`
assume `m + 1 <= |Pw|`, `W7_top2` assumes `m <= |Pw|`; the brackets `G8_bracket`, `K5_bracket` and
`W7_bracket` have the premises of these top forms. `G0_p1` assumes `r = 0` (a 24-word source). The
one-cost-budget bound assumes `0 <= c` and a bound `T >= 0`. The known-passphrase reading
(`top2_known`, `theorem5_pair_known`) assumes `s_1 = 1`, the text's "`Q` is known". `W7_passes` is
for the test that checks first and asks Ω after a pass (`mode = 2`).

The upper halves of the brackets are Theorem 3, 4 and 5 applied to the attack, so they hold at the
attack's own budget: `q_B = 11m + 1` and `q_H = 12m` beside `k_A = 12m` for G8 and W7, `q_B = 10m + 1`
and `q_H = 11m` beside `k_A = 11m` for K5. The text names only `k_A` there.

`top2_uniform_eq` and `top2_uniform` assume that the password and the passphrase are uniform on their
whole finite types (`N1 = |Pw|`, `N2 = |Pp|`) and that `m` and `n` are not negative.
`theorem5_seed_capped` and `theorem5_pair_capped` hold for every limit `n` of the rule `SeqF`, with
the hypotheses of Theorem 5 on the adversary and the refusal; a rule with a limit is not a covered
rule, since it may select nothing.

Lemma W2, Theorem 5, Corollary W5 and Proposition W7 hold for every covered rule, the text's
sequential rule included. Their proofs use the sequential rule cut off after `2^80` trials (`Seq`),
which is not an assumption: the transfer to a covered rule costs at most `3·2^-256`, which W2's own
constant leaves free inside `δ_gen` (DESIGN.md).

