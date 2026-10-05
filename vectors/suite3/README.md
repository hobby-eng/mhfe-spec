# Suite 3 public vectors

These fixtures describe `MHFE-BIP39-256-EXPERIMENTAL-3`. They contain public passwords and round
keys deliberately; never use their phrases or passwords for funds. They are released under
[CC0-1.0](../LICENSE-CC0-1.0).

The corpus contains **17 positive transcripts, six recovery cases and 54 fast conformance cases**.
The source implementation records completed independent full-cost verification of all 17 positive
transcripts in both directions and the six recovery cases. The import checks below confirm the
published bytes against that record and recompute the transcripts and the fast cases. The corpus is
interoperability evidence, not a cryptographic security proof, and suite 3 remains experimental.

## Source and provenance

Imported on 2026-09-30 from the reference implementation at immutable revision
[`46112d2b4bec0b9eba34cbbb9d632df099e11672`](https://github.com/hobby-eng/mhfe/tree/46112d2b4bec0b9eba34cbbb9d632df099e11672).
The source paths and related generator/verifier files were clean at this revision during the import.

- The 17 positive JSON files, `negative-cases.json` and `SHA256SUMS` are byte-for-byte copies of
  `tests/fixtures/suite3-vectors/`.
- `validation-cases.json` is a byte-for-byte copy of `tests/fixtures/validation-cases.json` from the
  same revision. Its SHA-256 is `92ced6ea44f3bcc912ff1aff50d1c5e1e249268678818a1e1f10a9178db0fecd`.
- The unchanged source `SHA256SUMS` contains exactly 18 entries for the positive/recovery JSON
  files. Its SHA-256 is `d69f6386d81ae1c6e44acef9fb8e4887b046f370731cd05637b59bf5f97e4be8`.
- Each positive transcript and recovery case identifies generator `mhfe test-vectors`, version
  `0.4.0`, and the reference C Argon2 engine at `P-H-C/phc-winner-argon2` commit
  `f57e61e19229e23c4445b85494dbf7c07de721cb`.

The generator and verifier source files at the pinned revision have these hashes:

| Source file                                                                                                                                      | SHA-256                                                            |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------ |
| [`src/vectors.rs`](https://github.com/hobby-eng/mhfe/blob/46112d2b4bec0b9eba34cbbb9d632df099e11672/src/vectors.rs)                               | `f6ed9de536d5505972956eb9e9531eb4d4cf23e0dc0d9f8df579e59aa0439e6f` |
| [`scripts/independent-suite3.py`](https://github.com/hobby-eng/mhfe/blob/46112d2b4bec0b9eba34cbbb9d632df099e11672/scripts/independent-suite3.py) | `25d578eec0c81c42f5ae831fe99d960b94d09ca4300ef27c6f62cd92d9a66550` |

The source
[independent verification record](https://github.com/hobby-eng/mhfe/blob/46112d2b4bec0b9eba34cbbb9d632df099e11672/tests/fixtures/suite3-vectors/independent-verification.json)
is linked as provenance rather than copied into this corpus. Its SHA-256 is
`9c0afe58c6f7f9f0682dbcff238e5e8f96abbc02cfd44921612d05f1b3df7cef`. It identifies Python **3.14.4**,
`cryptography` **46.0.5** and **OpenSSL 3.5.5 (27 Jan 2026)**, and names the verifier hash above.
All 18 files have a `full` entry, covering the 17 positive transcripts and the six-case recovery
file; the positive transcripts additionally have `recorded-argon2-keys` entries. These are two
checks of the same transcripts, not additional distinct vectors.

## Contents and coverage

The positive schema is `mhfe-suite-3-vector-v2`. Each transcript records the original and normalized
password bytes, packing, Argon2 settings, container and recovery results, and 12 rounds in each
direction. Every round includes `salt_input_hex` and `mask_input_hex`, as well as the salt, Argon2
output, mask and before/after state. There are 408 round records across the 17 transcripts.

| Files                                    | Cases | Coverage                                                             |
| ---------------------------------------- | ----: | -------------------------------------------------------------------- |
| `zero-{12,15,18,21,24}.json`             |     5 | Every source length, zero entropy, default settings                  |
| `nonzero-{12,15,18,21,24}.json`          |     5 | Every source length, nonzero public BIP39 entropy                    |
| `zero-12-pim-1.json`                     |     1 | Nonzero PIM                                                          |
| `zero-12-memory-level-1.json`            |     1 | Memory level 1                                                       |
| `zero-{12,24}-pim-1-memory-level-1.json` |     2 | Nonzero PIM and memory level together                                |
| `unicode-password.json`                  |     1 | Non-ASCII password changed by NFKD                                   |
| `spaces-password.json`                   |     1 | Leading, repeated and trailing spaces preserved                      |
| `ambiguous-12-21.json`                   |     1 | Multiple short-length matches and unverified 24-word interpretation  |
| `negative-cases.json`                    |     6 | Wrong password/settings and distinct recovery modes                  |
| `validation-cases.json`                  |    54 | Fast input, settings, phrase, packing and serialization expectations |

The recovery file is an array of `mhfe-suite-3-negative-case-v2` records. It covers a wrong password
with automatic detection and with 12 words selected, wrong PIM, wrong memory level, a wrong password
for a 24-word source, and the correct password with 24 words manually selected for a 12-word source.
Five records expect an unverified 24-word result; the selected-short-length mismatch expects
`VERIFIER_MISMATCH`. Thus the filename does not imply that every case must produce an error.

The fast fixture uses `mhfe-validation-cases-v2` and contains:

- 33 password cases, including rejection of NUL, TAB, CR, LF, U+0085, U+2028 and U+2029; canonical
  equivalents with equal normalized bytes; Private Use acceptance; invalid Unicode/UTF-8; preserved
  spaces/case; exactly 1024/1025 normalized bytes; and normalization expansion/contraction
  boundaries;
- one JavaScript unpaired-surrogate case;
- five settings cases;
- six phrase cases;
- eight source-length detection cases;
- one `verifier_serialization` object, counted as one case rather than an array.

These fields close the earlier corpus's documented gaps for full salt/mask messages, the named
Unicode cases, canonical equivalence and explicit manual 24-word recovery. The obsolete
`spaces-and-nul-password.json` has been replaced by `spaces-password.json`; NUL and TAB now have
rejection expectations. The independent record supplies full-cost trace/recovery evidence. The 54
fast cases run no Argon2 and are outside that 18-file record; the import checks below recomputed
them.

## Import checks

Two reviewers checked the imported files on 2026-09-30.

Codex checked source and destination byte identity, all 18 SHA-256 entries against both the source
manifest and independent record, the record's verifier-source hash, JSON schema identifiers, case
counts and the presence of the documented message fields.

Claude, in a separate session, checked the same bytes, taken from `git show 46112d2:<path>` in
`mhfe`. Everything passed:

- `scripts/independent-suite3.py` from that revision reproduced all 17 transcripts with their
  recorded Argon2id keys, 408 round records in both directions, and replayed `spaces-password.json`,
  the one new transcript, at full cost in both directions: 24 OpenSSL Argon2id calls at the default
  settings.
- [`notation_check.py`](../../docs/audits/AUD-003-harnesses/notation_check.py), which recomputes the
  vectors from this repository's formulas with its own code, reproduced all 17 transcripts and the
  nine archived suite 2 vectors.
- An ad hoc script confirmed that every `salt_input_hex` and `mask_input_hex` is the 68-byte string
  `DS_SALT || BE32(MEM) || BE32(PIM) || BE32(i) || R`, or the same with `DS_MASK`, and gives the
  recorded salt and mask: 408 round records.
- An ad hoc script recomputed the 33 password, one JavaScript and five settings cases with Node
  26.10.0 and Unicode 17.0, and the six phrase, eight length-detection and one
  verifier-serialization cases with Python: all 54 cases match.
- Apart from the new schema fields, every value of the 16 transcripts and five recovery cases kept
  from the earlier corpus is unchanged.

The full-cost replay of the six recovery cases is the one in the source record. The two ad hoc
scripts are not part of this repository.

From this directory, the imported file identities can be checked:

```sh
sha256sum --check SHA256SUMS
printf '%s  %s\n' 92ced6ea44f3bcc912ff1aff50d1c5e1e249268678818a1e1f10a9178db0fecd validation-cases.json | sha256sum --check
```

Checksums establish byte identity, not algorithm correctness or complete implementation conformance.
The archived suite 2 files in [`../archive/suite-2/`](../archive/suite-2/) are preserved separately
and are not covered by this manifest.
