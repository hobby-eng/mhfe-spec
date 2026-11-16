# Lean proof of the `mhfe_core` code

This folder holds a machine-checked proof, in Lean 4.35, that the Rust code of `mhfe_core` computes
what the MHFE specification says, for every function the cipher uses, and that the permutation it
computes is the cipher of the Lean security model. The Rust code is translated to Lean by hax
(Charon and Aeneas); the theorems are about that translation.

Date: 2026-11-12 (UTC). Paths are relative to this folder, `proofs/code/` of the specification
repository.

## Inputs

| Input | Revision |
| --- | --- |
| `mhfe_core` | `df7ea54` (equal to GitHub `main` on 2026-11-12) |
| Specification | `mhfe_spec` `98620cc`. Its four later commits, up to `da3a733` (2026-11-16), keep the cipher, its algorithm and its vectors, but change the wallet-check profile: a generation MAY show the number of trials of its draw and a duration that depends only on the trial outcomes and on randomness independent of the secrets, the functions and the trial values (Theorem 5 and Corollary W5 gain a `2^-120` term for the sequential rule, `2^-136·n` in general); a phrase that must also pass another check on the phrase alone, such as another wallet's phrase check, is excluded; and the coins of a selection rule are independent of the trial values given the secrets and the functions. This proof covers none of these changes: the draw is outside it and the new bounds are not checked here |
| Lean model of the specification | [`../lean`](../lean) (`MhfeLean`, Lean 4.35.0) |
| hax | `cargo-hax` 0.5.0, release binary, SHA-256 checked |
| Charon | `nightly-2026.10.31` (the default of hax 0.5.0) |
| Aeneas | `build-2b9e3ea` (the default of hax 0.5.0), with its Lean library at the same commit |
| Lean | 4.35.0, Mathlib as pinned by the Lean model |

## What is proved

135 theorems, no `sorry`, no axiom beyond Lean's three standard ones (`AXIOMS.txt`: 113 use
`propext`, `Classical.choice` and `Quot.sound`, 14 `propext` and `Quot.sound`, 8 `propext` alone).

| Part of the code | Theorem (namespace `MhfeProofs`) | File |
| --- | --- | --- |
| Work factor: `WorkFactor::new` accepts exactly PIM ≤ 1023 and MEM ≤ 21, PIM checked first; `passes = 12 (PIM + 1)`; `memory_kib = m(MEM)` without overflow | `new_spec`, `passes_spec`, `memory_kib_spec` | `Proofs/Params.lean` |
| Round message `BE32(MEM) ‖ BE32(PIM) ‖ [BE32(ENT)] ‖ BE32(i) ‖ R` | `write_message_spec` | `Proofs/Message.lean` |
| Round salt `Trunc_128(BLAKE2b-256(DS_SALT ‖ m))`, round mask `Trunc_h(HMAC-SHA-256(K, DS_MASK ‖ m))` | `round_salt_spec`, `round_mask_spec` | `Proofs/Round.lean` |
| Workspace: creation, the six parts, `into_state` (keeps the halves, wipes the rest with zeros) | `workspace_new_spec`, `parts_spec`, `into_state_spec` | `Proofs/Workspace.lean` |
| One round, both directions, is the specification's round with `RoundMask(i, ·)` | `round_spec` | `Proofs/Feistel.lean` |
| `Permutation::forward` = `Perm`, `Permutation::inverse` = `Perm^-1` | `forward_spec`, `inverse_spec` | `Proofs/Feistel.lean` |
| Domain strings, `Geometry::of`, `Mhfe::permutation` | `ds3_salt` … `ds4_mask`, `geometry_of_spec`, `permutation_spec` | `Proofs/Geometry.lean` |
| The code's permutation is the cipher of `DeniabilityModel` (both suites) and, inverted in suite 3, the recovery program `Gamma2Model.finalize` | `forward_eq_deniabilityCipher`, `inverse_eq_deniabilityCipher`, `inverse_eq_finalize` | `Proofs/ModelCode.lean` |
| Packing: `pack`, `unpack` (both layouts), `detected_lengths` | `pack_spec`, `unpack_spec`, `unpack_exact`, `detected_lengths_spec` | `Proofs/Packing.lean` |
| `Suite::of_container`, the admission table `admit`, the length rules `lengths`, `Recovery::new` | `of_container_spec`, `admit_spec`, `lengths_spec`, `recovery_new_3`, `recovery_new_4` | `Proofs/Recovery.lean` |
| `Recovery::readings` in both suites | `readings_spec_3`, `readings_spec_4` | `Proofs/Readings.lean` |
| `Mhfe::decrypt`: a suite or a stated length that is not admitted is refused before any Argon2id work (for every engine); the recovered state is `Perm^-1` of the container | `decrypt_suite_not_admitted`, `decrypt_length_not_admitted`, `decrypt_spec` | `Proofs/Cipher.lean` |
| `Mhfe::encrypt`: suite 4 refuses a 24-word original before any work (for every engine); a container is `Perm(X)`, differs from `X`, passed the creation check `Perm^-1(Y) = X` and has three words per four bytes | `encrypt_same_length_needs_short`, `encrypt_spec` | `Proofs/Cipher.lean` |
| A created container selects its own suite and recovers the encrypted state | `created_container_recovers` | `Proofs/RoundTrip.lean` |
| Wallet check: `digest` = `SHA-256(ASCII("MHFE-WALLET-CHECK-SEED-1") ‖ BE32(256) ‖ seed)`, `seed_passes` ⇔ the first 16 bits are zero | `digest_spec`, `seed_passes_spec` | `Proofs/WalletCheck.lean` |
| The results are reached: with an engine whose calls succeed and callbacks that let the work go on, a round returns `Ok`, `forward`/`inverse` return their state, `decrypt` returns a recovery for every admitted container, `encrypt` returns a container unless `Perm(X) = X`; `Perm^-1 ∘ Perm` is the identity; the original of a suite 3 container is among its readings | `round_ok`, `forward_ok`, `inverse_ok`, `decrypt_ok`, `encrypt_ok`, `permInv_perm`, `original_reading` | `Proofs/Success.lean` |

A theorem `f ⦃ r => P r ⦄` is total correctness: `f` returns (no panic, no divergence) and its
result satisfies `P`.

## What the theorems assume

The hypotheses of the theorems are the only assumptions on their inputs:

- `EngineComputes inst A`: the Argon2id engine computes a function `A` of its inputs. It may fail
  (`Err`) and may change its own state, but every key it returns is `A(password, salt, m, t)`.
  Argon2id itself is taken as verified: its parameters (version `0x13`, four
  lanes, empty secret and associated data) are in no statement, and `A` is any function. The
  refusal theorems of `decrypt` and `encrypt` hold for every engine, also one whose calls never
  return.
- `HostCallbackTotal`: the host's callbacks (`on_round`, `on_unchecked`) return, with any decision.
  The theorems speak about the results that continue; a `Break` is any result the host asked for.
- For the theorems of `Success.lean` only: `EngineOk` (every call of the engine succeeds) and
  `HostContinues`/`CallbackContinues` (the callbacks return `Continue`). These make the success
  theorems non-vacuous; the other theorems do not need them. `EngineOk` asks every call to succeed,
  on every state and input, so it describes an idealized engine: the native engine refuses
  parameters out of its range and may run out of memory, and the success theorems are not
  instantiated for it.
- `WorkOk`, `SecretOk`, `PhraseOk`: a work factor that `WorkFactor::new` accepts, a password whose
  secret is well formed, a phrase of 12 to 24 words with its entropy. These are the invariants that
  the constructors of the crate establish.

## The trusted base

1. Lean's kernel, Mathlib and the Lean library of Aeneas (`Aeneas.Std`), which models the Rust
   primitives (integers, slices, arrays, vectors, `Result`, `Option`).
2. Charon and Aeneas: the translation of the Rust code to `MhfeCore/Extraction/Funs.lean` and
   `Types.lean`. Aeneas runs in its own standard-library mode
   (`-filter-trait-methods -loops-to-rec`) because the code it generates for hax's core models does
   not match those models (`tools/aeneas-std.sh`).
3. The extraction harness (`harness/`, made by `tools/make-harness.py`): the original sources read
   through links (SHA-256 of each in `harness/MANIFEST.txt`), except `src/feistel.rs` and
   `src/cipher.rs`, where `&mut dyn Argon2Engine` and `&mut dyn FnMut` become generic parameters
   (`harness/src_*.rs.diff`: types only, no statement changes). The hash crates are replaced by
   shims with the same API and opaque bodies.
4. The hand translations (`lean/MhfeCore/Assumptions/Translations.lean`), placed into
   `lean/MhfeCore/Code.lean` by `tools/splice.py` (order and SHA-256 in `lean/MANIFEST-code.txt`):
   - five functions that Aeneas `build-2b9e3ea` cannot translate, each next to its Rust source:
     `Workspace::parts` (`split_first_chunk_mut().expect`, an `Option` that holds borrows),
     `Permutation::round`, `forward` and `inverse` (loops whose state holds the `&'static [u8]`
     domain strings of `Geometry`), `recovery::lengths` (`Iterator::copied`), with their helpers
     `splitFirstChunkMutExpect`, `swapWithSlice`, `xorZip`, `forwardLoop`, `inverseLoop`;
   - eight closure instances (`R` in the manifest) whose generated declaration disagrees with the
     generated method it names. Two of them, the closures that `encrypt` and `decrypt` pass to
     `stack::cleared`, keep the generated method and change the declared output type only. The six
     others, the `FnOnce` and `FnMut` instances of the three round callbacks (which capture the
     host's callback by `&mut`), are short hand-written adapters around the unchanged generated
     methods: `call_once` returns the output and drops the closure's state; `call_mut` returns the
     output and the state after the call with the generated backward function (the identity here)
     applied. Only the `call_mut` adapters are on a path of the code: `forward` and `inverse` call
     the callbacks through `call_mut`, and nothing calls the `call_once` adapters, which would lose
     the update of the captured callback. `lean/REPLACED-blocks.lean.txt` keeps the generated
     blocks.
5. The models of what the extraction keeps opaque (`lean/MhfeCore/Assumptions/FunsExternal.lean`,
   `TypesExternal.lean`):
   - BLAKE2b-256, SHA-256 and HMAC-SHA-256 (on the 64-byte key block) as opaque functions of their
     input bytes; every theorem holds for every such function. The specification's HMAC with a key
     `K` is the HMAC of the 64-byte block `K ‖ 0…0` (RFC 2104), which is how the code calls it.
   - The standard-library iterators, `Option`/`Result` helpers and `Step` that Aeneas does not
     model; `zeroize` writes the type's zero; the memory pages of `protect::Secret` are their bytes
     (locking and dump exclusion are not values); the stack clearing changes no value.
   - BIP39: a `Phrase` is its word count and its entropy (no words, no checksum);
     `Phrase::encode` gives three words for every four bytes of 16 to 32 bytes; `read_text` is the
     inverse of the text model, so the creation check's decoding of the words always succeeds in
     the model (its test of the encoding is assumed). NFKD, the word list and the checksum are
     outside the proof, and so are the requirements on reading words (`WRD-1` to `WRD-3`, `PCK-1`,
     `REC-1`, `S4-4`), which the construction of a `Phrase` meets before `encrypt` or `decrypt`
     runs.

## Not covered

The repair profile (Reed–Solomon over GF(2^11)), the password check word, NFKD and the Unicode
tables, the BIP39 word list and seed function, the operating-system protections, the native and
WebAssembly engines, `Debug`/`Display`, and the `Break` results of the callbacks beyond "the result
is not a container".

## Files

| Path | Content |
| --- | --- |
| `AXIOMS.txt` | `#print axioms` of every theorem |
| `REPORT.md` | the audit, the analysis and the comparison with the Lean model |
| `harness/` | the record of the extraction harness: `MANIFEST.txt` (the `mhfe_core` commit and the SHA-256 of every file read) and the two type-only diffs; `tools/make-harness.py` writes the rest |
| `lean/MhfeCore/Extraction/` | the output of Aeneas (generated) |
| `lean/MhfeCore/Assumptions/` | the models and the hand translations |
| `lean/MhfeCore/Code.lean` | the code the theorems are about (generated by `tools/splice.py`) |
| `lean/MhfeCore/Spec/` | the byte-level specification and its link to the Lean model |
| `lean/MhfeCore/Proofs/` | the proofs (`Success.lean`: the results are reached) |
| `tools/` | the scripts: `make-harness.py`, `extract.sh`, `extract-all.sh`, `aeneas-std.sh`, `splice.py`, `test-regeneration.sh` (the test of the regeneration gate), `lake.sh`, `lean1.sh`, `run.sh` (memory-capped scopes) |

## Checking

With [elan](https://github.com/leanprover/elan), from `lean/`:

```bash
lake exe cache get   # Mathlib's compiled files
lake build
```

builds every file (3466 jobs), the Lean model in `../../lean` included, which the proof imports. A
file that imports the proofs then prints the axioms of every theorem, which must equal `AXIOMS.txt`:

```bash
cp ../tools/AxiomCheck.lean.txt MhfeCore/AxiomCheck.lean
lake env lean MhfeCore/AxiomCheck.lean | grep "^'MhfeProofs\." | diff - ../AXIOMS.txt
rm MhfeCore/AxiomCheck.lean
```

The scripts of `tools/` expect a workspace that holds this repository, a checkout of `mhfe_core` and
the toolchains in `workingspace/` (`MHFE_WORKSPACE` names another one), and run each job in a
memory-capped scope: `../tools/lake.sh full 10G 120m build` builds, and
`../tools/lean1.sh MhfeCore/AxiomCheck.lean` checks one file.

To regenerate the code from `mhfe_core` at `df7ea54`: `tools/make-harness.py`,
`tools/extract-all.sh` (which also writes the LLBC of Charon to `lean/llbc/`, not kept in the
repository) and `tools/aeneas-std.sh`. `aeneas-std.sh` runs Aeneas into a staging folder and keeps
its full output in `logs/aeneas-std.log`. It exits 1 and replaces nothing in `lean/` when Aeneas
exits nonzero, reports an error or writes no `Types.lean` or `Funs.lean`, or when the SHA-256 of
`Types.lean`, `Funs.lean`, `Translations.lean` and `Code.lean` or the order of the blocks differ
from `lean/MANIFEST-code.txt` (the new manifest is then in `lean/MANIFEST-code.new.txt`). Otherwise
`splice.py` installs the generated files and `Code.lean` one after the other, each written next to
its target and renamed over it: each file is replaced whole or not at all, but a failure between two
files leaves the earlier ones installed, and the script then says that files may already be replaced
(audit AUD-015, finding BLD001; the message and a test of a failed installation were added on
2026-11-16 and are not yet verified by an audit). After a reviewed change,
`tools/aeneas-std.sh --record` records the new manifest. `tools/test-regeneration.sh` runs both
scripts with a fake translator in a mock tree: a failure before output, after partial output, with
and without an error line, an error line (coloured, after a progress bar) with exit 0, missing
output, a different `Types.lean` or `Funs.lean`, a warning, a recording and the runs after it, and a
failure while installing.
