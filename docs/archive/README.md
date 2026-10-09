# Archive

Historical documents kept for reference. They are not normative for suite 3 and must not be used to
implement the current protocol. The current specification is [`README.md`](../../README.md), and its
analysis is [`docs/DESIGN-NOTES.md`](../DESIGN-NOTES.md).

## Suite 2, release v0.3.0

[`suite-2-v0.3.0/`](suite-2-v0.3.0/) holds the two documents of release
[v0.3.0](https://github.com/hobby-eng/mhfe-spec/releases/tag/v0.3.0) (tag `v0.3.0`, commit
`61033431380c7d5e8ad58f493ebc22a4ff8e69b4`), which defines suite `MHFE-BIP39-256-EXPERIMENTAL-2`:

| File                                                              | Contents                                    | SHA-256 of the released file                                       |
| ----------------------------------------------------------------- | ------------------------------------------- | ------------------------------------------------------------------ |
| [`README.md`](suite-2-v0.3.0/README.md)                           | Suite 2 specification and design discussion | `42763f68042c597b057a22f9b15fe0ef850c000e0526a209382ea608deddf8fa` |
| [`SPECIFICATION-PLAIN.md`](suite-2-v0.3.0/SPECIFICATION-PLAIN.md) | Plain-language description of suite 2       | `35524ef91413bbeb4d332093e98bba2021b51dc30f0002ba837c5244fe2fe7df` |

Each file begins with a note of eight lines, the last of them empty, added for this archive.
Everything after it is the released file, except that its links to `mhfe` commits were updated.
Relative links inside refer to the layout of that release, so some of them no longer resolve. The
released bytes remain in tag `v0.3.0`; from the repository root, they are checked against the hashes
above with:

```sh
git show v0.3.0:README.md | sha256sum
git show v0.3.0:SPECIFICATION-PLAIN.md | sha256sum
```

The suite 2 test vectors are archived in
[`vectors/archive/suite-2/`](../../vectors/archive/suite-2/); see the
[vectors index](../../vectors/README.md#archived-suite-2) for which of them were published with
release v0.3.0.

The final-word-preserving profile `MHFE-BIP39-256-EXPERIMENTAL-2-CYCLE-WALK-FINAL-WORD` was drafted
and implemented for suite 2 after this release and was never released. Its text is in the history of
this repository, in commit
[`5270a89`](https://github.com/hobby-eng/mhfe-spec/blob/5270a89ceaa18d87d0c982156b1aa735f16260f4/README.md).
The [supplement](../DESIGN-NOTES.md#final-word-preserving-cycle-walking-research-idea) keeps its
analysis as a research idea for suite 3.
