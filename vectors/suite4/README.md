# Suite 4 public vectors

These fixtures describe `MHFE-BIP39-LP-EXPERIMENTAL-4`, the length-preserving suite. They contain
public passwords and round keys deliberately; never use their phrases or passwords for funds. They
are released under [CC0-1.0](../LICENSE-CC0-1.0).

The corpus contains **10 positive transcripts, four recovery cases and 67 fast conformance cases**.
The source implementation records completed independent full-cost verification of all 10 transcripts
in both directions and the four recovery cases. The import checks below confirm the published bytes
against that record and recompute the transcripts, except Argon2id, and the fast cases from this
repository's text. The corpus is interoperability evidence, not a cryptographic security proof, and
suite 4 remains experimental.

## Source and provenance

Imported on 2026-10-02 from the reference implementation at revision
`21c43df2fbb116ea30b929c2478060110d74530a`. That commit was replaced the same day and is not in the
published history. Commit
[`aedd4cee4301c794af3693b64017083386115adc`](https://github.com/hobby-eng/mhfe/tree/aedd4cee4301c794af3693b64017083386115adc)
of release `v0.5.0` holds the same files, byte for byte.

- All files here are byte-for-byte copies of `tests/fixtures/suite4-vectors/` at that revision.
- `SHA256SUMS` contains exactly 11 entries: the 10 transcripts and `negative-cases.json`. Its
  SHA-256 is `9433eff33a494436e6f4709e0d003472c3c9b53b528b0f770f9769ae47fd583e`.
- `validation-cases.json` runs no Argon2 and is outside that manifest. Its SHA-256 is
  `541826d453b845d7be51ed41dbf967814ea965b0e3127ae8b6ea57dc2f5e7e40`.
- Each transcript and recovery case identifies generator `mhfe test-vectors`, version `0.5.0`, and
  the reference C Argon2 engine at `P-H-C/phc-winner-argon2` commit
  `f57e61e19229e23c4445b85494dbf7c07de721cb`.

The generator and verifier source files at the pinned revision have these hashes:

| Source file                                                                                                                                      | SHA-256                                                            |
| ------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------ |
| [`src/vectors.rs`](https://github.com/hobby-eng/mhfe/blob/aedd4cee4301c794af3693b64017083386115adc/src/vectors.rs)                               | `283570803e74dc1858101586258c98ba9a85423edf88f9c4860fb8495d66f4dd` |
| [`scripts/independent-suite4.py`](https://github.com/hobby-eng/mhfe/blob/aedd4cee4301c794af3693b64017083386115adc/scripts/independent-suite4.py) | `72a9b15b92d06da82e185417c8d23bc443f401110e543b1a972d777ccebc1cbd` |

The source
[independent verification record](https://github.com/hobby-eng/mhfe/blob/aedd4cee4301c794af3693b64017083386115adc/tests/fixtures/suite4-vectors/independent-verification.json)
is linked as provenance rather than copied into this corpus. Its SHA-256 is
`a0f0eb9b8f2ac7bc654c7530514e39d0e4b01695cf4b6ff9862a06113f2e7555`. It identifies Python **3.14.4**,
`cryptography` **46.0.5** and **OpenSSL 3.5.5 (27 Jan 2026)**, and names the verifier hash above.
All 11 files of the manifest have a `full` entry: every Argon2id call recomputed, in both
directions.

## Contents and coverage

The positive schema is `mhfe-suite-4-vector-v1`. Each transcript records the original and normalized
password bytes, the Argon2 settings, the state and its half width, the container and the recovery,
and 12 rounds in each direction. Every round includes `salt_input_hex` and `mask_input_hex`, as well
as the salt, Argon2 output, mask and before/after halves. There are 240 round records across the 10
transcripts.

| Files                                           | Cases | Coverage                                                    |
| ----------------------------------------------- | ----: | ----------------------------------------------------------- |
| `same-length-zero-{12,15,18,21}.json`           |     4 | Every source length, zero entropy, default settings         |
| `same-length-nonzero-{12,21}.json`              |     2 | Nonzero public BIP39 entropy, shortest and longest halves   |
| `same-length-zero-12-pim-1.json`                |     1 | Nonzero PIM                                                 |
| `same-length-zero-12-memory-level-1.json`       |     1 | Memory level 1                                              |
| `same-length-zero-12-pim-1-memory-level-1.json` |     1 | Nonzero PIM and memory level together                       |
| `same-length-unicode-password.json`             |     1 | Non-ASCII password changed by NFKD, 15-word source          |
| `negative-cases.json`                           |     4 | Wrong password, PIM and memory level; another chosen length |
| `validation-cases.json`                         |    67 | `ENT` separation and every refusal of the recovery table    |

The recovery file is an array of `mhfe-suite-4-negative-case-v1` records. A wrong password, PIM or
memory level gives another valid 12-word phrase, labelled as not verified, with no error; choosing
another length for a 12-word container gives `LENGTH_CHOICE_NOT_APPLICABLE` before any Argon2id
work.

The fast fixture `mhfe-suite-4-validation-cases-v1` contains four `ENT`-separation cases, one for
each source length, with equal settings, round and half content: their salt and mask messages differ
only in `BE32(ENT)`. Its 63 refusals are the encryption of a 24-word source under suite 4 and 62
recovery inputs that the specification's
[recovery table](../../README.md#suite-4-length-preserving-containers) does not admit.

## Import checks

Claude checked the imported files on 2026-10-02, taken from `git show 21c43df:<path>` in `mhfe`.
Everything passed:

- `sha256sum --check SHA256SUMS`: all 11 entries; the source manifest, the verification record and
  the two source files have the hashes above, and the record's verifier hash matches.
- An ad hoc script written from this repository's suite 4 section, without code from `mhfe`,
  recomputed every transcript except the Argon2id calls, using their recorded outputs: the BIP39
  decoding and the state, every `salt_input_hex` and `mask_input_hex` with `BE32(ENT)`, the
  BLAKE2b-256 salts truncated to 128 bits, the HMAC-SHA-256 masks truncated to `h` bits, both
  Feistel directions, the container words with their own checksum and the recovered phrase: 240
  round records in 10 transcripts.
- The same script recomputed the four `ENT`-separation cases, and checked that the 62 recovery
  refusals are exactly the combinations of chosen suite, chosen length and container length that the
  recovery table does not admit, with none missing.

The full-cost Argon2id replay is the one in the source record; this import did not repeat it. The ad
hoc script is not part of this repository.

From this directory, the imported file identities can be checked:

```sh
sha256sum --check SHA256SUMS
printf '%s  %s\n' 541826d453b845d7be51ed41dbf967814ea965b0e3127ae8b6ea57dc2f5e7e40 validation-cases.json | sha256sum --check
```

Checksums establish byte identity, not algorithm correctness or complete implementation conformance.
