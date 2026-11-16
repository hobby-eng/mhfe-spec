# Verification

This folder documents the machine-checked proofs of the MHFE specification. The proofs themselves
are in [`proofs/`](../../proofs/):

| Folder | What it proves | Proof system | How to check |
| --- | --- | --- | --- |
| [`proofs/easycrypt/`](../../proofs/easycrypt/) | every numbered theorem, lemma, corollary and proposition of the Deniability section and of appendix A of the [supplement](../DESIGN-NOTES.md), in its idealized model | EasyCrypt at commit `ce19cb6`; Why3 1.9.0 with Alt-Ergo 2.6.5, Z3 5.4.1 and CVC5 1.4.2 | `./check.sh -timeout 20`: every source in strict mode, without caches, refusing `admit` |
| [`proofs/lean/`](../../proofs/lean/) | the same results | Lean 4.35.0 with Mathlib and VCVio | `./check.sh`: the build, its axiom inventory and a kernel replay of every chapter |
| [`proofs/code/`](../../proofs/code/) | the Rust code of `mhfe_core` at `df7ea54` (not released) computes what the specification at `98620cc` says for every function the cipher uses, and its permutation is the cipher of the Lean model; hand translations and models are in its [trusted base](../../proofs/code/README.md#the-trusted-base) | Lean 4.35.0; the code translated by Charon and Aeneas (hax 0.5.0) | `lake build` in `lean/`, then the axiom check of its README |

Each README says what is trusted, which hypotheses the statements take and where a formal statement
is narrower than the text.

## Documents in this folder

- [`COMPARISON.md`](COMPARISON.md): the two developments compared result by result, with the
  differences of their models, domains and adversaries, the corrections of the text that the
  comparison led to and, in its appendix A, the names of every result in both.
- [`LEAN-PORT.md`](LEAN-PORT.md): the port of the Lean development from Lean 4.28.0, in which it was
  written, to Lean 4.35.0. The port itself changed proof scripts, one instance declaration and the
  name of one pattern variable, and added `LegacyPMF.lean`; no statement of a result changed; the
  statements, chapters and scripts added after it are listed in the README of
  [`proofs/lean/`](../../proofs/lean/README.md).
- [`remediation/`](remediation/): the changes made for the findings of the audits AUD-011, AUD-012
  and AUD-013. AUD-013 verified the fixes for AUD-011; the fixes for AUD-012 and AUD-013 have not
  been verified by an audit. AUD-015 verified the fixes for the three findings of AUD-014 and found
  one Low finding, BLD001, whose fix (an accurate message and a test case, 2026-11-16) is not yet
  verified by an audit. The two findings of AUD-016 were fixed in the specification at commit
  `33dba0f`, not yet verified by an audit. The audits are in [`docs/audits/`](../audits/README.md).

These documents were written while the developments lived in machine-local working copies. A note at
the top of each maps their paths to this repository.

## Authors and review

The EasyCrypt development, the code proof, the comparison and the remediation records were written
with Claude (Anthropic). The Lean development was written by Codex (OpenAI) in Lean 4.28 and ported
to Lean 4.35 with Claude, who also added its chapters on the records of Theorem 2 and on the number
of trials, brought Proposition K5 and Corollary W5 to the corrected text and wrote its check
scripts. The audits were made by Codex. The developments are not independent: the model, the games
and the statements of the Lean development were reviewed before the EasyCrypt development was
written and consulted while it was written; the two share no code. No human expert has reviewed the
proofs.

## What the proofs do not cover

The two developments concern the idealized model of the supplement: random functions and counts of
queries. They say nothing about the real cost of Argon2id or PBKDF2, about side channels or about
the generation of randomness. The code proof is about the translation of the Rust code by Charon and
Aeneas; its README lists its trusted base and what it does not cover. The heuristic estimates,
numerical examples and open questions of the supplement are not results and have no formal
statement.

## Checks of the published files

On 2026-11-16 each development was checked again from this repository with the scripts of its
folder:

- EasyCrypt: `./check.sh -timeout 20` checked all 23 sources in strict mode, without caches and
  without `admit`, and `./check-selftest.sh` passed. Two earlier runs with the default time limit
  stopped at the `smt` step of `src/KnownPair.ec` at line 365, which passes alone with the default
  limit; audit AUD-016 had found the same step sensitive to the resources of a run.
- Lean: `./check.sh` built every module, printed `MHFE_COMPLETE_AXIOM_INVENTORY|6185|4003|standard`
  and replayed all 41 chapters through the kernel, and `./check-selftest.sh` passed.
- Code proof: `lake build` built all 3466 jobs, the axioms of the 135 theorems equal `AXIOMS.txt`,
  `tools/test-regeneration.sh` passed, and a regeneration from the LLBC of Charon matched
  `lean/MANIFEST-code.txt`.
