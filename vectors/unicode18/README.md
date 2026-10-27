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

The eight-case file was copied from `tests/fixtures/unicode18-passwords.json` of an earlier
pre-publication source archive, identified below, before the released `mhfe-core` 0.1.0 existed. It
is public test data, not regenerated from the implementation under test. Its SHA-256 is:

```text
d9ba60250e6ac9cd0e5afee52c4f152ad9d11e5c120a96c34aa06be4e9c3159a
```

[`SHA256SUMS`](SHA256SUMS) covers this JSON file only. The cases and their data are released under
[CC0-1.0](../LICENSE-CC0-1.0), as the other specification vectors are.

The released implementation is `mhfe-core` 0.1.0, tag
[`v0.1.0`](https://github.com/hobby-eng/mhfe_core/releases/tag/v0.1.0) at commit
[`c6eaa706866b9868cb51048d64b3d21752abce44`](https://github.com/hobby-eng/mhfe_core/commit/c6eaa706866b9868cb51048d64b3d21752abce44).
Its tests read this folder from this repository through the submodule `tests/spec`, which pins
commit `6f7537e8c268e010c710a889175e353ec02f66e1`, and its `tests/passwords.rs` replays the eight
cases. The vector files and checksums of that commit are those of this release. Core's crates.io
package, which leaves out the tests, has SHA-256:

```text
d44e15ab9e3f25c1c787a0b10f6b8467441463dd57b137940a97a1deb390247d
```

Core's tag, commit and package checksum identify the implementation, not a specification release.
Core's package version 0.1.0 and this specification's version 0.7.0 identify different artifacts.

The checks of 2026-10-25, before the released 0.1.0 existed, used a pre-publication source archive
with SHA-256 `ccbac8ac1686c6f43a04f385c2328a56a8dfeb947f3619c08bbee5f3e71842ae`. The audit AUD-001
of that earlier work, which is not part of the released repository, gives its 145-file source
fingerprint `bf1048479b2d8b58b299885923d1a3064b03584204592e025bac892b7a57864e`. A 0.1.0 package
published from the same work, with another checksum, was later withdrawn from crates.io. Its release
record identifies an earlier reviewed draft of the specification 0.7.0 README, SHA-256
`9c2c8c6b6110d18234bd12e034c0798ff0f504fa6e6b931b9d33a87ac44c5548`; the implementation links were
reworded and the specification was rewritten for readability after that review. These earlier
identities remain a historical verification record. The released 0.1.0 is a different package with a
history of its own.

## Verification and limits

Expected mappings and combining classes come from the Unicode 18.0.0 character database. The
independent Python checker, from mhfe, uses `unicodedata2` 18.0.0. Core's Rust encoder uses
`unicode-normalization` 0.1.26, and Core's tests replay Unicode's `NormalizationTest.txt` 18.0.0.
That replay is Core's own check; it is not a newly published specification vector or a fresh replay
of every cryptographic transcript by this repository.

The checks confirm that Core's submodule holds this JSON file and `SHA256SUMS` unchanged, run the
independent checker on these eight cases and the 33 historical suite 3 password cases, and run
Core's password tests. They do not repeat production-cost Argon2, enumerate every string, prove
normalization memory cleanup or establish cryptographic security.

The checks on 2026-10-27 used Core's repository at the released commit. Its submodule held this JSON
file and `SHA256SUMS` unchanged, and its tests
`the_unicode_18_passwords_encode_or_are_refused_as_recorded` and
`the_suite_3_passwords_encode_or_are_refused_as_recorded` passed. The independent checker
`scripts/independent-suite3.py` of [mhfe](https://github.com/hobby-eng/mhfe) at commit
[`8be344293a184a91f7d7a2260c5fdcceb229ec3d`](https://github.com/hobby-eng/mhfe/commit/8be344293a184a91f7d7a2260c5fdcceb229ec3d),
SHA-256 `54f8906c0ed4a4c94194b77f3ae9c1b195850a2166710ae9b6d7d2942ae7c037`, reproduced all 8 new and
33 historical password cases, and so did its copy in this repository's [`scripts/`](../../scripts/),
which adds the emergency commands. Two altered expected-value controls were refused with the
required diagnostic: a wrong normalized byte and a wrong refusal code. These controls test the
checker, not additional password inputs.

The checks of 2026-10-25 reproduced the same cases with the pre-publication archive's copy of the
checker, SHA-256 `36b3681f3a68cf817bf69e48bbcc938950a41225cc5f3ce391d28db808065680`, and argument
parser, SHA-256 `83243abd9af623c4f8dfdba1813df76edfe56b53922c43c8b170956caecff654`. The archive's
`password::known_answers::tests::the_password_encoding_passes` passed in the native test executable
with SHA-256 `6950ba2dcdd9a6d73efdf7d9f88d053a4be6b34618cc8e87c19332492b883ce2`, and the same two
controls were refused.

From the specification root, the independent check is:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python \
  python3 scripts/independent-suite3.py passwords \
  vectors/unicode18/password-encoding.json vectors/suite3/validation-cases.json
```

Install the checker's pinned packages, including `unicodedata2` 18.0.0, from
[`scripts/independent-suite3-requirements.txt`](../../scripts/independent-suite3-requirements.txt).
The checker reads the BIP39 English word list from `scripts/bip39-english.txt`.

The BIP39 passphrase is a separate input: its ordinary NFKD does not apply the MHFE password's
unassigned-character rejection. These password cases do not remove the
[BIP39 compatibility caveat](../../README.md#optional-source-profile-a-recovery-check-for-new-24-word-phrases).
