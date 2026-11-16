# EasyCrypt formalization of the MHFE supplement proofs: scope and plan

Recorded 2026-11-09, before any proof was written.

## Sources

| File | SHA-256 |
| --- | --- |
| `mhfe_spec/README.md` | `50f19a6c7093be3fd3f30393144d8d5539ae58a572e449f0797b31aec1db9a6e` |
| `mhfe_spec/docs/DESIGN-NOTES.md` | `c5f1afdbc83479121e6cf8f6328e2f8a641682fe7372792fe821681edb64caee` |

`mhfe_spec` at commit `68826e1c31a3a5cac8b23a3acfc18302252f3ec3`; the only untracked path is
`docs/drafts/`. The specification, the Markdown proofs and the PDFs are not changed by this work.

## Tools

EasyCrypt r2026.10 (commit `859766e50e936fb9e420fb6fb1ad8824ffb8d83e`), OCaml 5.5.2, Why3 1.8.2,
Alt-Ergo 2.6.4, Z3 5.3.1, CVC5 1.4.2, installed from source on the machine where the development was
written (its installation notes and run wrapper are not published). Every run went through a systemd
scope with at most 4 GiB and no swap, sized to leave 1.5 GiB to the system, and stopped if the whole
system fell below 768 MiB available.

## Independence

The original independence condition was waived on 2026-11-08: the author of this development
(Claude) reviewed Codex's Lean formalization before starting and consulted it while writing, in a
survey of 2026-11-10; neither the review nor the survey is published. This development does not copy
its structure; the two are compared per result at the end
([`docs/verification/COMPARISON.md`](../../docs/verification/COMPARISON.md)).

## Results in scope

From the Deniability section: Lemmas 1-3, Theorem 1, Theorem 2, the corollary on simulating a
prepared disclosure, and the suite 4 forms of Theorems 1 and 2. From appendix A: Theorem 3 with
Lemmas G1-G5, Corollaries G6, G7, G10, Remark G9 and Proposition G8; Theorem 4 with Lemmas K1-K4 and
Proposition K5; Theorem 5 with Lemmas W1-W4, Corollaries W5, W6, Proposition W7 and the
selection-rule paragraph. Heuristic estimates, numerical examples and the open questions of the text
are not results and are not formalized.

Added after the statement review of 2026-11-11, because the text states them as results: the
one-cost-budget bound and the reading for uniform secrets of A.6, the bound `p_1` for a 24-word
source without wallet data (end of A.4), Theorem 1 for fixed functions, and the top forms of the
matching attacks for every test. Added later the same day: the known-passphrase reading of A.6, the
brackets "the best adversary lies between" after G8, K5 and W7, the attainment of `T(x)`, the count
of Ω queries of W7's check-then-Ω test, and instances at every source length the text names (from
the summary of that review, which is not published).

Added on 2026-11-12. For the corrected text (specification commits `6161a3f` to `98620cc`): the
smaller loss of Proposition K5, `k_S` in `δ_gen` in Corollary W5, and Theorem 5 for a generation that
stops at a limit and reports a failure. After the audit AUD-011 of the specification repository: the
exact value of `top2` for uniform secrets, where only its upper bound was stated
([`AUD-011.md`](../../docs/verification/remediation/AUD-011.md)).

Added on 2026-11-13, for specification commit `3d88078`: the number of
trials of the wallet-check profile, for the sequential rule (Theorem 5 (a), (b) and Corollary W5
with `2^-120` added). The general rule with `n` expected trials and `w` workers are out of scope for
now. The exclusion of phrases with another condition needs no statement: the model draws every
phrase by the selection rule alone.

## Rules

1. Statements first. `src/` gets the model, every game and every statement with `admit` proofs; it
   is compared with the text before proofs are written, also by one independent reviewer.
2. Size budget: 4,000-6,000 lines for everything, hard ceiling 8,000. Reaching the ceiling stops the
   work and is reported. On 2026-11-09 the ceiling was lifted (the estimate was 9,000-10,000 lines),
   and the work went on until every proof was done; the code stays as lean as before.
3. One general lemma per technique (fresh sampling, refusal correction, the up-to-bad step), reused.
   No file per variant, no wrapper theorems that only re-apply another, no per-file axiom reports.
4. The finished development has no `admit`. Every assumption is either a parameter of a theory
   (types, widths, distributions) or a hypothesis of a lemma (adversary budgets, losslessness), and
   all are listed in `ASSUMPTIONS.md`. A solver timeout or an open goal is an unfinished check.
5. Checks at the end: a full compile with each of Alt-Ergo, Z3 and CVC5 separately, negative
   controls (a false statement must fail), and one independent review of statements against the
   text. Changed on 2026-11-11, after the newest Why3 and provers left the per-prover results
   unchanged: an `smt` step counts as proved when one of the three provers proves it, so the release
   check is the full compile with all three together; per-prover runs are recorded for information.
6. Results are about ideal random functions and query counts. They say nothing about the real cost of
   Argon2id or PBKDF2 or about any implementation.

## Modelling decisions

- The four functions of A.1 (and `S`, `T`, `Omega`, the record oracle where needed) are lazily
  sampled random oracles from the standard library (`PROM`), which is equivalent to independent
  uniform functions.
- The adversary is an abstract module with access to the oracles through a counting wrapper. Its
  budgets are hypotheses that hold on every run, for every oracle implementation; repeated queries
  count, which is more general than the text's "repeats no query". It may use its own coins.
- `top`, the fractional top `T` and `top2` are the text's ranked sums over the finite sets of
  passwords and passphrases (revised after the statement review; the first skeleton used suprema).
  `mass_top` and Lemma W1 bound the mass of sets that are not ranked.
- Domains are finite as in A.1 (round indices 0..11, normalized passwords). Passphrases are taken
  finite as well, which narrows the text; see `ASSUMPTIONS.md`.
- Bit layout: `pack` and the split of a `G` output into `Trunc_r` and the rest are abstract
  bijections with the stated widths (`ENT + r = 256`), which the concrete bit strings satisfy.
