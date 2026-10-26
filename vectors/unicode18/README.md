# Unicode 18 password-encoding cases

This corpus supplements the unchanged suite 3 and suite 4 corpora for specification 0.7.0. It tests
their shared password encoding, not a new encryption format. Specification releases 0.4.0 to 0.6.0
use the Unicode 17.0.0 password repertoire for these suites.

## Cases and expected outcomes

[`password-encoding.json`](password-encoding.json) contains eight public cases:

- three newly assigned characters with exact NFKD UTF-8 bytes;
- a new combining class that reorders an existing mark;
- normalized lengths of exactly 1024 and 1025 bytes after a new decomposition;
- a code point still unassigned in Unicode 18;
- a forbidden control character alongside a newly assigned character.

The `passwords` array uses the same field conventions as the historical validation files. An input
is either `input_utf8_hex` or `repeat_utf8_hex` repeated `count` times. Accepted output is
`expected_nfkd_utf8_hex` or its length in `expected_nfkd_bytes`; `expected_error` gives a required
stable refusal code. The bytes and lengths are measured after NFKD. The 1025-byte case is refused,
never truncated. These cases apply identically to both suites and require no Argon2id call.

Previously valid passwords remain covered by the unchanged
[suite 3 password cases](../suite3/validation-cases.json) and the non-ASCII round transcripts of
both suites. These records must retain their original bytes and historical verification metadata.

## Provenance and implementation identity

The eight-case file is byte-for-byte identical to `tests/fixtures/unicode18-passwords.json` of the
checked `mhfe-core` 0.1.0 source archive. It is copied as public test data, not regenerated from the
implementation under test. Its SHA-256 is:

```text
d9ba60250e6ac9cd0e5afee52c4f152ad9d11e5c120a96c34aa06be4e9c3159a
```

[`SHA256SUMS`](SHA256SUMS) covers this JSON file only. The cases and their data are released under
[CC0-1.0](../LICENSE-CC0-1.0), as the other specification vectors are.

The implementation target is the checked pre-publication `mhfe-core` 0.1.0 archive, SHA-256:

```text
ccbac8ac1686c6f43a04f385c2328a56a8dfeb947f3619c08bbee5f3e71842ae
```

Core's AUD-001 records the corresponding 145-file source fingerprint:

```text
bf1048479b2d8b58b299885923d1a3064b03584204592e025bac892b7a57864e
```

These are source/artifact identities, not a specification commit or release identifier. Core's
package version 0.1.0 and this specification's version 0.7.0 identify different artifacts. No
registry or GitHub publication is implied by these identities alone.

The subsequently published `mhfe-core` 0.1.0 release records an earlier reviewed draft of the
specification 0.7.0 README with SHA-256
`9c2c8c6b6110d18234bd12e034c0798ff0f504fa6e6b931b9d33a87ac44c5548`. The implementation-link wording
was updated and the specification was rewritten for readability after that review. The release
record still identifies those earlier exact document bytes; it does not claim that Core reviewed the
later wording. The pre-publication archive identity above remains a historical verification target.

## Verification and limits

Expected mappings and combining classes come from the Unicode 18.0.0 character database. The
independent Python checker uses `unicodedata2` 18.0.0; the Rust encoder uses `unicode-normalization`
0.1.26. Core's AUD-001 retains the larger scalar/official-corpus comparison and its controls. Those
are Core verification records, not newly published specification vectors or a fresh replay of every
cryptographic transcript by this repository.

The focused import checks compare this JSON to the archived fixture, run the independent checker on
these eight cases and the 33 historical suite 3 password cases, and exercise Core's fast password
known-answer check. They do not repeat production-cost Argon2, enumerate every string, prove
normalization memory cleanup or establish cryptographic security.

The focused checks on 2026-10-25 reproduced all 8 new and 33 historical password cases. Core's
`password::known_answers::tests::the_password_encoding_passes` passed. Two altered expected-value
controls were refused with the required diagnostic: a wrong normalized byte and a wrong refusal
code. These controls test the checker, not additional password inputs.

From the specification root, the independent check is:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python CARGO_HOME=../workingspace/cargo \
  python3 ../mhfe_core/scripts/independent-suite3.py passwords \
  vectors/unicode18/password-encoding.json vectors/suite3/validation-cases.json
```

Use the pinned checker environment, including `unicodedata2` 18.0.0. The checked script SHA-256 is
`36b3681f3a68cf817bf69e48bbcc938950a41225cc5f3ce391d28db808065680`; its argument parser SHA-256 is
`83243abd9af623c4f8dfdba1813df76edfe56b53922c43c8b170956caecff654`. The existing native test
executable used for the focused check has SHA-256
`6950ba2dcdd9a6d73efdf7d9f88d053a4be6b34618cc8e87c19332492b883ce2`.

The BIP39 passphrase is a separate input: its ordinary NFKD does not apply the MHFE password's
unassigned-character rejection. These password cases do not remove the
[BIP39 compatibility caveat](../../README.md#optional-source-profile-a-recovery-check-for-new-24-word-phrases).
