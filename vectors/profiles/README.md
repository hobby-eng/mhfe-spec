# Optional MHFE profile vectors

These are public test inputs and expected results, not wallets or passwords for use. The profile
definitions are in the [specification](../../README.md#specification). The vectors are released
under [CC0-1.0](../LICENSE-CC0-1.0). Paths shown in the tables are relative to the repository root.

## Contents

- [Optional source check: MHFE-WALLET-CHECK-SEED-1](#optional-source-check-mhfe-wallet-check-seed-1)
- [Repair words: MHFE-REPAIR-1](#repair-words-mhfe-repair-1)
- [Password check word: MHFE-PASSWORD-CHECK-1](#password-check-word-mhfe-password-check-1)

## Optional source check: MHFE-WALLET-CHECK-SEED-1

Public vectors for
[MHFE-WALLET-CHECK-SEED-1](../../README.md#optional-source-profile-a-recovery-check-for-new-24-word-phrases).

These inputs are public test data, not wallets for use. In each row, `E` is 192 zero bits followed
by the stated counter as a 64-bit big-endian integer:

| Counter | BIP39 passphrase | SHA-256 digest `T`                                                 |
| ------- | ---------------- | ------------------------------------------------------------------ |
| 76562   | `TREZOR`         | `0000e86481bdfe6dbf45e6e41fba4f309fcf09d3f0af2fe3f46736c663840853` |
| 98918   | empty string     | `0000ede77b44fbd62025e1d36a45ebe3846cf48f7b3e76ca6a91495fdadc1fb2` |

Both pass. Counter 98918 encodes as "abandon" 21 times followed by "absorb another spoil". Counter
76562 with the empty passphrase gives a digest beginning `ebd07f71` and fails; counter 98918 with
`TREZOR` gives `8d2b97fb` and fails. Omitting `BE32(256)` from the first row gives `f2c9f765` and
fails.

## Repair words: MHFE-REPAIR-1

Public vectors for [MHFE-REPAIR-1](../../README.md#optional-repair-words-mhfe-repair-1).

Repair words for `k` = 2 / 4 / 6 / 8:

| Container                                    | Repair words                                                                                                                                        |
| -------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------- |
| `vectors/suite3/zero-12.json`                | `labor extra` / `shaft pupil patient jewel` / `credit buzz orbit tired sail coffee` / `appear include vicious move uphold tiger song satoshi`       |
| `vectors/suite4/same-length-nonzero-12.json` | `motor renew` / `pitch lonely onion erode` / `toe rather ribbon run enforce notice` / `tilt object execute change cube domain vehicle hour`         |
| `vectors/suite4/same-length-nonzero-21.json` | `glove blossom` / `share mask pave crystal` / `slow issue fame census cabbage clarify` / `potato enemy similar myself check gesture fortune shiver` |
| `abandon` 23 times, then `art`               | `clever gravity` / `letter wealth borrow cable` / `clap try lift setup innocent gather` / `mirror coffee census note proof zebra begin barrel`      |

Word positions count from 1. With the four repair words of the first row, the container phrase of
`vectors/suite3/zero-12.json` is repaired in three cases: when its words 3 and 17 are unreadable,
which restores `tower` and `cycle`; when word 10 is replaced by `zoo` and word 5 is unreadable,
which restores `rib` and `iron`; and, exactly at the bound `2e + s = k`, when words 3 and 17 are
replaced by `zoo` and `abandon`.

## Password check word: MHFE-PASSWORD-CHECK-1

Public vectors for
[MHFE-PASSWORD-CHECK-1](../../README.md#optional-password-check-word-mhfe-password-check-1).

Each row gives five dice rolls, the check index and the resulting password:

| Dice rolls                      | Check index | Password                                            |
| ------------------------------- | ----------- | --------------------------------------------------- |
| `11111 11112 11113 11114 11115` | 104         | `abacus abdomen abdominal abide abiding aids`       |
| `66666 66666 66666 66666 66666` | 7739        | `zoom zoom zoom zoom zoom yelling`                  |
| `35214 62431 15543 44126 21365` | 4150        | `jovial trailing chokehold pavilion cresting ninth` |
| `24255 61534 11111 66622 26522` | 5527        | `drop-down t-shirt abacus yo-yo felt-tip rubble`    |

In the third row, an erased third word is recovered as `chokehold`.
