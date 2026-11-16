# The `mhfe_core` code proved in Lean: audit, analysis and comparison with the Lean model

Date: 2026-11-12 (UTC). Subject: `mhfe_core` `df7ea54` (GitHub `main` on 2026-11-12), the
specification `mhfe_spec` `98620cc` (its four later commits, up to `da3a733`, keep the cipher, its
algorithm and its vectors; they let the wallet-check profile show the number of trials, with an
added term in its bounds and conditions on the randomness of the draw, and exclude phrases that must
pass another check on the phrase alone; this proof covers none of these changes), the Lean model
`MhfeLean` (`../lean`). The proof and its README are in this folder (`README.md`). No file of
`mhfe_core` was changed; the changes this report proposes are proposals only.

## 1. Summary

The functions that create a container, recover a state from it and check a wallet seed are proved
in Lean against a byte-level restatement of the specification, through the translation of the Rust
code by hax 0.5.0 (Charon and Aeneas). The proof has 135 theorems, builds from scratch with no
`sorry`, and uses only Lean's standard axioms.

What the theorems establish, for every Argon2id engine that computes a function of its inputs and
for every hash function:

- one round of the code is the specification's round, in both directions; `forward` computes
  `Perm` and `inverse` computes `Perm^-1`, and these are the cipher of the deniability model and,
  in suite 3, the recovery program of the guessing theorems;
- creation returns a container only if it is `Perm(X)` of the packed original, differs from `X`,
  and passed the creation check `Perm^-1(Y) = X`; a created container selects its own suite again
  and recovers `X`;
- recovery refuses a suite or a stated length that is not admitted before any Argon2id work, for
  every engine (also one whose calls never return); the recovered state is `Perm^-1(Y)`; the
  readings follow the length rules and the admission table of the specification;
- packing, unpacking, the detected lengths, the round message, the salt, the mask, the domain
  strings, the work factor, `Suite::of_container` and the wallet check compute what the
  specification says;
- the workspace keeps only the two halves at the end of a permutation and writes zeros over the
  message, the salt, the key and the mask;
- the results are reached: with an engine whose calls all succeed (an idealized engine, section 3.2)
  and callbacks that let the work go on, `forward` and `inverse` return their state, `decrypt` returns a recovery for every admitted
  container, and `encrypt` returns a container for every accepted original unless `Perm(X) = X`;
  the original of a suite 3 container is among the readings of its recovered state.

Outside the proof: reading the words and the BIP39 checksum (`WRD-1` to `WRD-3`, `PCK-1`, `REC-1`,
`S4-4`), which the construction of a `Phrase` performs before `encrypt` or `decrypt` runs; NFKD; the
BIP39 seed; the repair profile; the password check word; the operating-system protections; the
parameters of Argon2id.

No difference between the code and the specification was found in the parts proved. The trusted
base and its weak points are in section 3; the proposals in section 6 are meant to shrink its
hand-written part, which a new run of Aeneas on the changed code has to confirm.

## 2. Method

1. The crate was extracted with `cargo hax into lean` (Charon `nightly-2026.10.31`, Aeneas
   `build-2b9e3ea`), from a harness that reads the original sources through links and differs from
   them only in types: `&mut dyn Argon2Engine` and `&mut dyn FnMut` become generic parameters in
   `feistel.rs` and `cipher.rs` (Aeneas does not translate `dyn` trait objects). The hash crates
   were replaced by shims with the same API.
2. The LLBC was translated again by the same Aeneas in its own standard-library mode, because the
   code generated for hax's core models (`-core-models-lib`) disagrees with the definitions of those
   models at `v0.3.41`.
3. The items the extraction keeps opaque got hand-written Lean definitions: five functions that
   Aeneas cannot translate (translated line by line, the Rust next to each), eight closure
   instances whose generated declaration disagrees with their generated method (two with a
   corrected output type, six with a short adapter around the generated method), and models of the
   standard-library iterators, the hash functions, the memory pages, `zeroize` and BIP39.
4. A byte-level specification (`Spec/Spec.lean`) restates the normative definitions; it is checked
   against the specification's vectors (`Spec/SpecTests.lean`) and proved equal to the cipher of the
   Lean model (`Spec/ModelLink.lean`).
5. The theorems are total-correctness statements (`f ⦃ r => P r ⦄`: `f` returns and `P` holds)
   proved with the Aeneas `step` tactics. A full build of 3,466 jobs and `#print axioms` of every
   theorem close the work (`AXIOMS.txt`).
6. An independent reviewer read the statements against the Rust code and the normative text
   (section 3.3); its main finding led to the success theorems of `Proofs/Success.lean`. A second,
   separate audit (AUD-014) re-ran the extraction and the proof; its findings are in section 3.4.

## 3. Audit of the proof

### 3.1 Checks

| Check | Result |
| --- | --- |
| Full build of the project from the pinned toolchain | passed, 3,466 jobs |
| `sorry`, `admit` (tactic), `native_decide`, `axiom` in the proof and the models | none (the word `admit` occurs only as the name of `recovery::admit`) |
| Axioms of the 135 theorems | `propext`, `Classical.choice`, `Quot.sound` only |
| The code the theorems are about | `Code.lean`, built by `tools/splice.py`, which checks that every generated block appears once and unchanged and that no block precedes one it uses; SHA-256 of its inputs and output in `lean/MANIFEST-code.txt` |
| Regeneration | `tools/aeneas-std.sh` with the pinned Aeneas reproduces `Types.lean`, `Funs.lean`, `Code.lean` and `REPLACED-blocks.lean.txt` byte for byte (2026-11-13); the gate refuses a failed translator, a reported error, missing output and any difference from the manifest, and replaces nothing then (`tools/test-regeneration.sh`: 13 cases pass; 8 of 9 mutated copies of the scripts fail it, the ninth removes the check for missing files, which `splice.py` still refuses; the earlier wrapper fails it too) |
| The harness | SHA-256 of every linked source and of the two rewrites in `harness/MANIFEST.txt`; the rewrites are type-only (`harness/src_*.rs.diff`) |
| `mhfe_core` checkout | unchanged during the work (the extraction script checks it) |

### 3.2 The trusted base, item by item

| Item | What is trusted | Assessment |
| --- | --- | --- |
| Lean, Mathlib, `Aeneas.Std` | the kernel and the library models of integers, slices, arrays, vectors | standard; the integer and slice models are the ones every Aeneas proof uses |
| Charon and Aeneas | that `Funs.lean` is the meaning of the Rust code | the main tool risk; the translation of mutable borrows into backward functions is what the proofs rely on most (workspace parts, `into_state`) |
| Harness rewrites | `dyn` → generics in two files | type-only: a call through `dyn` and a call through a generic dispatch to the same method; no statement changed |
| Hand translations (5 functions + 5 helpers) | that each is the Rust function | the largest item a reader must check by eye; each block quotes the Rust it translates. `round`, `forward` and `inverse` are short; `parts` is six splits; `lengths` follows the match arms in order |
| Replaced closure instances (8) | two (the closures passed to `stack::cleared`): only the declared output type changed; six (`FnOnce` and `FnMut` of the three round callbacks): hand-written adapters around the unchanged generated methods, `call_once` dropping the closure's state and `call_mut` returning the state with the generated backward function applied | `REPLACED-blocks.lean.txt` keeps the generated blocks for comparison; the generated backward functions are the identity; the code reaches only the `call_mut` adapters (`forward`, `inverse`); the `call_once` adapters, which would lose the update of the captured callback, are on no path of the code |
| Hash functions | that the shims call `blake2`, `hmac`, `sha2` with the bytes shown; HMAC on the 64-byte key block | the theorems hold for every function, so no property of the hashes is assumed; the RFC 2104 equality of HMAC under `K` and under `K ‖ 0^32` is a definition of the specification's primitive in terms of the code's |
| Iterator, `Option`, `Result`, `Step` models | that they behave as the standard library | small, written from the library's documented behaviour; the ones the theorems use (`filter`, `map`, `collect` into `Result<Vec>`, `all`, `flatten`) have their own lemmas in the proof |
| Memory pages, `zeroize`, stack clearing | pages are their bytes; `zeroize` writes zeros; clearing the stack changes no value | locking, dump exclusion and the actual wiping of memory are outside the model; the theorem that `into_state` writes zeros is about values, not about the operating system |
| BIP39 and phrases | a `Phrase` is its word count and entropy; `encode` makes three words per four bytes of 16–32; `read_text` inverts the text model | the words, the word list and the checksum are not represented; `read_text` returns `Ok` on every text of two or more bytes, so the creation check's decoding always succeeds in the model and its test of the encoding (NEW-3) is assumed; a real `bip39` failure would make `encrypt` return `CreationCheckFailed`, never a wrong container |
| Engine | `EngineComputes`: every key the engine returns is `A(P, S, m, t)` | Argon2id taken as verified: version `0x13`, four lanes and the empty secret and associated data are in no statement, and `A` is any function; the hypothesis asks the engine to return on every input, not only on the memory and passes of the work factor; the refusal theorems need no hypothesis on the engine at all. `EngineOk`, used by the success theorems only, asks every call to succeed on every state and input: it describes an idealized engine, since the native engine refuses parameters out of its range and may run out of memory, and the success theorems are not instantiated for it |

### 3.3 Independent review

One independent reviewer read the statements, the hand translations, the models and the byte
specification against `mhfe_core` and the normative text. It found
the hand translations, the eight replaced instances, the harness rewrites, the iterator and helper
models and every definition of the byte specification consistent with their sources. Its findings
and what was done:

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| 1 | The main theorems describe only successful results; an engine that always fails, or code that always errs, satisfies them | medium | fixed: `Proofs/Success.lean` proves that the results are reached (`round_ok`, `forward_ok`, `inverse_ok`, `decrypt_ok`, `encrypt_ok`), with `permInv_perm` for the creation check |
| 2 | The docstring of the `read_text` model said it rejects texts that are not phrases; it accepts every text of two or more bytes | low | fixed: docstring corrected; the consequence (the creation check's decoding is assumed) is in section 3.2 |
| 3 | `Phrase` has no words and no checksum; `WRD-*`, `PCK-1`, `REC-1`, `S4-4` are outside the proof | low | stated in sections 1 and 3.2 and in `README.md` |
| 4 | The Argon2id parameters are in no statement; `EngineComputes` asks the engine to return on every input | info | stated in section 3.2; narrowing the hypothesis is a follow-up (section 7) |
| 5 | The docstring of the HMAC model should say it takes the 64-byte key block | info | fixed |
| 6 | The docstring of `ModelCode.lean` overstated the link to the security theorems | low | fixed: it now says that the code computes the model's cipher with instantiated tables, and that the random-table reading is the model's assumption |
| 7 | `layoutMatches` does not check the length of its input | info | documented: it is applied to 32-byte states only |
| 8 | Some links were indirect: `decrypt_spec` uses the code's suite selection, no theorem ran from creation to the readings, the seed derivation is outside | info | `suiteOfContainer_code` ties the code's selection to the specification's; `original_reading` with `created_container_recovers`, `decrypt_ok` and `readings_spec_3` closes the chain at the specification level; the seed derivation stays outside |
| 9 | The vectors check one round, not twelve | info | follow-up (section 7) |

### 3.4 Second audit (AUD-014)

A separate audit (`mhfe_spec/docs/audits/AUD-014-2026-11-13.md`, 2026-11-13) re-ran Charon and
Aeneas without network and got `Types.lean` and `Funs.lean` byte for byte, rebuilt the 28 modules
from their sources, replayed them through the kernel and found the same axioms for the 135
theorems; three control files (an unused axiom, `sorry`, `native_decide`) were refused. It found no
false theorem and no difference from the specification. Its findings, each checked against the
files before it was fixed:

| ID | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| BLD001 | `aeneas-std.sh` ended the Aeneas pipeline with `\|\| true`, so a failing Aeneas (exit 7 after partial output) left exit 0, and `splice.py` built `Code.lean` and overwrote the manifest from the partial files | medium | confirmed and fixed: Aeneas writes into a staging folder with its full log kept; a nonzero exit, a reported error or a missing file stops the script before anything in `lean/` changes; `splice.py` compares with the recorded manifest (now with `Types.lean`), writes only `MANIFEST-code.new.txt` on a difference, and otherwise installs the generated files and `Code.lean` by writing each next to its target and renaming it; `--record` records a reviewed change; `tools/test-regeneration.sh` covers the cases (section 3.1). A reviewer of the fix found gaps in the first version of the test and two small defects (padded `[Warn ]` tags were not shown; a failed copy could leave `Extraction/` half replaced); all were fixed |
| DOC001 | Six of the eight replaced closure instances are hand-written adapters, not type-only changes | low | confirmed and fixed in section 3.2 and `README.md`, which now also say that nothing in `Code.lean` or the models calls the `call_once` adapters (checked by search: the callbacks are called through `call_mut` only) |
| DOC002 | The newer specification `3d88078` adds a permission to show the number of trials and new bounds, so "no requirement change" was wrong | low | confirmed and fixed in the header of this report and in `README.md` |

The audit also noted, without a finding, that `EngineOk` cannot hold for the native engine (now in
section 3.2) and that no single code-level theorem runs `encrypt`, `decrypt` and `readings` in
sequence (the chain is closed at the specification level, finding 8 of section 3.3); both are
follow-ups in section 7.

## 4. Analysis of the code

Properties of the code that the proofs make explicit:

1. **No panic on valid inputs.** Every theorem is total correctness: for a phrase of 12 to 24 words,
   a work factor that `WorkFactor::new` accepts and a well-formed password, `encrypt`, `decrypt`,
   `readings` and the wallet check return. In particular the `expect` in `decrypt` (a phrase always
   selects a suite), the slicing in `Workspace::parts`, the indexing in the round functions and the
   additions on round numbers cannot fail.
2. **Refusals before work.** `decrypt` with a suite the length does not select, or with a stated
   length the admission table refuses, returns its error for every engine; so does `encrypt` in
   suite 4 with a 24-word original. This is the formal form of "before any Argon2id work".
3. **Fixed point and creation check.** A returned container `Y` satisfies `Y ≠ X` and
   `Perm^-1(Y) = X`; the latter is checked by the code on the decoded words, and the proof shows it
   also holds as a property of the specification (`created_container_recovers`).
4. **Wiping.** `Workspace::into_state` truncates the secret to the two halves and writes zeros over
   everything after them (as values; the other `zeroize` calls are not stated in a theorem).
5. **The length rules.** `recovery::lengths`, a cascade of match arms with guards, is exactly the
   bullet list of the specification (`lengthRules`): the proof covers every combination of a stated
   length (none, a detected one, 24, another short one) and zero, one or several detected lengths.
6. **Suite 4 readings.** A recovered suite 4 state has no verifier; `readings` gives the one reading
   of the container's own length, whose entropy is the whole state, and marks it unverified.

Observations, none of them a defect of the specification's behaviour:

- **O1 (tooling).** Five functions are outside what Aeneas can translate today because of three
  Rust patterns: `split_first_chunk_mut().expect(..)` (an `Option` holding borrows), loops whose
  state holds structs with `&'static` references (`Geometry`), and `Iterator::copied`. These
  functions are the ones a reader must check by eye (section 3.2).
- **O2 (tooling).** Closures that capture `&mut` produce, in Aeneas `build-2b9e3ea`, `FnOnce`/`FnMut`
  instances whose declaration disagrees with the generated `call_once` and `call_mut`. This is a bug
  of the tool, not of the crate; eight instances needed a corrected declaration, six of them a short
  adapter around the generated method.
- **O3 (code).** `encrypt`'s inverse-round callback computes `ROUNDS + round` in `u32`; it cannot
  overflow because `inverse` passes 1 to 12, but the bound lives in `inverse`, not in the closure.
- **O4 (code).** `Recovery::readings` reports "no reading" (the length rules give none) as
  `Error::VerifierMismatch`, the same error as a failed verifier. The specification only says "give
  no reading"; a distinct error would let a host tell the two apart.
- **O5 (model).** The theorems show what a result that continues is, and that the work continues
  when the callbacks let it. That a `Break` from `on_round` stops before the next round is not
  proved; nothing a theorem says depends on it.

## 5. Comparison with the Lean model of the specification

| Layer | Object | Link |
| --- | --- | --- |
| Code | `Permutation::forward`/`inverse`, `encrypt`, `decrypt`, `readings` | proved equal to the byte specification (`Proofs/`) |
| Byte specification | `MhfeSpec.perm`/`permInv`, `pack`, `layoutMatches`, `detected`, `lengthRules`, `admitsLength`, `walletCheckPasses` | restated from the normative text; checked on the vectors (`SpecTests.lean`) |
| Lean model | `DeniabilityModel.cipher`, `KnownPairModel.cipher`, `Gamma2Model.finalize` | `perm`/`permInv` proved equal with the tables `a = A`, `b = Trunc_128 ∘ BLAKE2b-256(DS_SALT ‖ ·)`, `h = Trunc_h ∘ HMAC(·, DS_MASK ‖ ·)` (`ModelLink.lean`), and lifted to the code (`ModelCode.lean`) |

What this gives: the theorems of the Lean model about the cipher (Lemmas 1–3 and Theorem 1, the
deniability games of Theorem 2, and the suite 3 guessing theorems that run `Gamma2Model.finalize`)
are statements about the permutation the code computes, once its primitives are read as the
model's tables. The remaining distance is the model's own assumption: the tables are uniformly
random functions, while the code's primitives are fixed functions. The proof neither narrows nor
widens that gap; it removes the question whether the code computes the model's cipher.

Parts of the model that the code proof does not reach:

- the wallet functions and the seed function (`WalletData`, `WalletMatching`, `OrdinaryWallet`):
  the code's wallet check is proved against `walletCheckPasses`, but the BIP39 seed function is
  outside the proof;
- the password and passphrase domains (`PasswordDomains`, `PassphraseDomains`): the theorems take
  the password as the bytes of `Password` after NFKD, which is outside the proof;
- the creation-refusal accounting (`CreationRefusal`): the code's refusal of `Y = X` is proved; the
  probability the model bounds is a property of the ideal tables.

Differences of form, all bridged by proved lemmas: the model's state is a pair of bit vectors of
`8h` bits, the code's a byte string of `2h` bytes (`toBytes`, `halvesOf`); the model indexes the
rounds by `Fin 12`, the code by `u32`; the specification's `perm` reads the right half as
`X[h:]`, the code as `X[h:2h]`, equal on states of `2h` bytes, which are the only ones the code
accepts.

## 6. Proposed changes to the code (not made)

None of these changes fixes a defect: the audits found no error at these places, and the current
`expect` in `parts` relies on a length invariant that `parts_spec` proves. Their purpose is to make
the hand-written part of the trusted base (section 3.2) smaller while the guarantees stay the same,
so they belong to a separate stage, one change at a time: change the Rust with its tests, re-run
the extraction, check that Aeneas now translates the function, and close the proofs again. A change
is worth keeping only if the hand-written part really shrinks.

1. Make the engine and the callbacks generic (`E: Argon2Engine`, `F: FnMut(..)`). `Permutation`
   and `feistel` are `pub(crate)`, so their signatures are free. `Mhfe::encrypt` and
   `Mhfe::decrypt` are public and take `&mut dyn FnMut`; to keep that API exactly, they can stay as
   one-line forwarders to generic internal functions, which are what the extraction then reads.
   (Generic public parameters would also accept `&mut dyn FnMut` and closures, but would break a
   caller that names the parameter type.) Removes the harness rewrites; costs one monomorphization
   per engine and callback type.
2. In `Workspace::parts`, split with `split_at_mut` and keep the salt and key parts as slices (a
   `try_from(..).expect(..)` into array references may meet the same Aeneas limit as
   `split_first_chunk_mut`). Would let Aeneas translate `parts`.
3. Keep the domain strings out of the loop state: store `Geometry` by value with `[u8; N]` arrays or
   with a suite tag and look the strings up in `round_salt`/`round_mask`. Would let Aeneas translate
   `round`, `forward` and `inverse`.
4. Write `recovery::lengths` without `iter().copied().chain(..)`, for example
   `let mut all = detected.to_vec(); all.push(STATE_WORDS); Ok(all)`. Would let Aeneas translate it.
5. Optional: give "no reading" its own error variant (O4), only if a caller needs to tell it from a
   failed verifier; it is a diagnostic improvement, not a correction.

Whether 1–4 remove the five hand translations of functions is a prediction until Aeneas has been
run on the changed code. Even then the trusted base keeps the models of the external libraries
(hashes, BIP39, iterators, memory pages) and, unless Aeneas is fixed, the eight closure instances
(O2), which should be reported to Aeneas.

## 7. Follow-ups

- Prove the `Break` semantics of the callbacks (O5).
- Check all twelve rounds of a transcript against `forwardRounds`/`backwardRounds` in
  `SpecTests.lean` (review finding 9).
- Narrow `EngineComputes` to the memory and passes of the work factor (review finding 4), and
  `EngineOk` to the calls the code makes (a 16-byte salt, the memory and passes of an accepted work
  factor), so that the success theorems can be instantiated for a real engine that succeeds there.
- A code-level theorem that runs `encrypt`, then `decrypt` and `readings` on its container, and
  concludes that the original is among the readings (AUD-014).
- Extend the proof to the repair profile and the password check word, which the plan left out.
- Re-run the extraction and the proof against `mhfe_core` `main` after any change to the cipher
  modules; the scripts in `tools/` regenerate `Code.lean` and its manifest.
