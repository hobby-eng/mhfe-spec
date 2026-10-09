# Suite 3 public vectors

These fixtures describe `MHFE-BIP39-256-EXPERIMENTAL-3`. They contain public passwords and round
keys deliberately; never use their phrases or passwords for funds. They are released under
[CC0-1.0](../LICENSE-CC0-1.0).

The corpus contains **17 positive transcripts, seven recovery cases and 54 fast conformance cases**.
The source implementation records completed independent full-cost verification of all 17 positive
transcripts in both directions and the seven recovery cases. The import checks below confirm the
published bytes against that record and recompute the transcripts and the fast cases. The corpus is
interoperability evidence, not a cryptographic security proof, and suite 3 remains experimental.

## Source and provenance

Imported on 2026-09-30 from the reference implementation at immutable revision
[`cc91b0bab58f51c08a3562a5ef441e7faab726b4`](https://github.com/hobby-eng/mhfe/tree/cc91b0bab58f51c08a3562a5ef441e7faab726b4).
The source paths and related generator/verifier files were clean at this revision during the import.
On 2026-10-09, `negative-cases.json` and `SHA256SUMS` were updated from revision
[`3a705db6945b35f8c248c44893e71ddc36902af4`](https://github.com/hobby-eng/mhfe/tree/3a705db6945b35f8c248c44893e71ddc36902af4),
which adds the `stated-24-words` case; the other files are unchanged and identical at both
revisions.

- The 17 positive JSON files, `negative-cases.json` and `SHA256SUMS` are byte-for-byte copies of
  `tests/fixtures/suite3-vectors/` at revision `3a705db6`. `negative-cases.json` has the SHA-256
  `3cdc998e3a1a3b7ca20304336cbb6e01015e6909e1011f86e86dc864145b6985`.
- `validation-cases.json` is a byte-for-byte copy of `tests/fixtures/validation-cases.json` from the
  same revision. Its SHA-256 is `92ced6ea44f3bcc912ff1aff50d1c5e1e249268678818a1e1f10a9178db0fecd`.
- The source `SHA256SUMS` contains exactly 18 entries for the positive/recovery JSON files. Its
  SHA-256 is `1a58d974e57a94592d757516925c7ea75078e0c8c92bd52a98202c4c0a42fc61`.
- Each positive transcript and recovery case identifies generator `mhfe test-vectors`, version
  `0.4.0` (`stated-24-words`: version `0.6.0`), and the reference C Argon2 engine at
  `P-H-C/phc-winner-argon2` commit `f57e61e19229e23c4445b85494dbf7c07de721cb`.

The generator and verifier source files at revision `3a705db6` have these hashes:

| Source file                                                                                                                                      | SHA-256                                                            |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------ |
| [`src/vectors.rs`](https://github.com/hobby-eng/mhfe/blob/3a705db6945b35f8c248c44893e71ddc36902af4/src/vectors.rs)                               | `24b53e45b66a1571a0c9f11271a4c94cc4df253cf493a946f8ad528c4d0a100e` |
| [`scripts/independent-suite3.py`](https://github.com/hobby-eng/mhfe/blob/3a705db6945b35f8c248c44893e71ddc36902af4/scripts/independent-suite3.py) | `544649a43b5c524e6e766b937f9011b98f3c331c14b45c0262abfea1b66bdc74` |

The source
[independent verification record](https://github.com/hobby-eng/mhfe/blob/3a705db6945b35f8c248c44893e71ddc36902af4/tests/fixtures/suite3-vectors/independent-verification.json)
is linked as provenance rather than copied into this corpus. Its SHA-256 is
`0ecbbd4fa3cd166862e6270fe5cad779c619dfea7f493d0d2f33a124ebd64da6`. It identifies Python **3.14.4**,
`cryptography` **46.0.5**, `unicodedata2` **17.0.1 (Unicode 17.0.0)** and **OpenSSL 3.5.5 (27
Jan 2026)**, and names the verifier hash above. All 18 files have a `full` entry, covering the 17
positive transcripts and the seven-case recovery file. The verifier applies the current length rules
to `stated-24-words` and keeps the historical single reading for `selected-24-words`. The earlier
record at revision `cc91b0ba` also had `recorded-argon2-keys` entries for the positive transcripts;
those were a second check of the same transcripts, not additional vectors.

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
| `ambiguous-12-21.json`                   |     1 | Multiple short-length matches and the unverified 24-word reading     |
| `negative-cases.json`                    |     7 | Wrong password or settings, with and without a stated length         |
| `validation-cases.json`                  |    54 | Fast input, settings, phrase, packing and serialization expectations |

The recovery file is an array of `mhfe-suite-3-negative-case-v2` records. It covers a wrong password
with no length stated and with 12 words stated, wrong PIM, wrong memory level, a wrong password for
a 24-word source, and twice the correct password with 24 words stated for a 12-word source, under
the historical and the current rules. Six records contain an unverified 24-word result; the two
24-words-stated records are explained [below](#current-recovery-expectations). The
stated-short-length mismatch expects `VERIFIER_MISMATCH`. Thus the filename does not imply that
every case must produce an error.

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
Unicode cases, canonical equivalence and explicit 24-word recovery with a stated length. The
obsolete `spaces-and-nul-password.json` has been replaced by `spaces-password.json`; NUL and TAB now
have rejection expectations. The independent record supplies full-cost trace/recovery evidence. The
54 fast cases run no Argon2 and are outside that 18-file record; the import checks below recomputed
them.

## Current recovery expectations

`selected-24-words` and `stated-24-words` decrypt the same container with the same password and
settings, with 24 words stated. `selected-24-words` keeps the result of the manual mode of version
0.4.0, which the current rules removed: only the 24-word reading. `stated-24-words` is the current
conformance case and returns both readings in this order under
[Recovering a mnemonic](../../README.md#recovering-a-mnemonic):

| Order | Words | Short source verifier      | Phrase                                                                                                                                                                     |
| ----: | ----: | -------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
|     1 |    12 | Passes (`verified: true`)  | `abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about`                                                                            |
|     2 |    24 | Absent (`verified: false`) | `abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about inner love zone until oven protect tray movie front reopen emerge bachelor` |

An implementation that follows the current rules reproduces `stated-24-words`; from
`selected-24-words` it reproduces the 24-word reading as the second reading. The 12-word reading
reports that 24 words were stated. The 24-word reading is labelled as not verified unless an
independent wallet-identity reference confirms it. With no BIP39 passphrase supplied, its source
check uses the empty passphrase and fails (the digest begins `0f9e2012`); this failure is not a
recovery error. The 12-word reading does not use that source check. The 24-word readings of the
other negative cases fail the same check with the empty passphrase: `wrong-password-detect`
(`1d8a88b4`), `wrong-pim` (`8d4927e3`), `wrong-memory-level` (`a08e73ba`) and
`wrong-password-24-words` (`9afb047d`). The records do not hold these check results; they follow
from the recorded phrases.

## Import checks

Two reviewers checked the imported files on 2026-09-30.

Codex checked source and destination byte identity, all 18 SHA-256 entries against both the source
manifest and independent record, the record's verifier-source hash, JSON schema identifiers, case
counts and the presence of the documented message fields.

Claude, in a separate session, checked the same bytes, read with `git show` from the pinned revision
in `mhfe`. Everything passed:

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

On 2026-10-09 Claude imported `negative-cases.json` and `SHA256SUMS` from revision `3a705db6` and
checked:

- both files and the independent verification record match the hashes above, and the manifest passes
  `sha256sum --check`;
- the 17 positive transcripts and `validation-cases.json` are identical at revisions `cc91b0ba` and
  `3a705db6`, and the six earlier recovery records are unchanged;
- the two readings of `stated-24-words` follow from the packed state of `zero-12.json`: only its
  12-word verifier passes, and the 12- and 24-word encodings equal the recorded phrases.

The full-cost replay of the recovery cases is the one in the source record. The two ad hoc scripts
are not part of this repository.

From this directory, the imported file identities can be checked:

```sh
sha256sum --check SHA256SUMS
printf '%s  %s\n' 92ced6ea44f3bcc912ff1aff50d1c5e1e249268678818a1e1f10a9178db0fecd validation-cases.json | sha256sum --check
```

Checksums establish byte identity, not algorithm correctness or complete implementation conformance.
The archived suite 2 files in [`../archive/suite-2/`](../archive/suite-2/) are preserved separately
and are not covered by this manifest.
