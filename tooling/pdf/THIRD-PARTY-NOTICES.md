# Document tool dependencies

The PDF tool reads public specification files; it performs no wallet operation. Versions and
checksums of its Rust dependencies are recorded in `Cargo.lock`. Cargo fetches these as build-time
dependencies. Their upstream licenses apply separately from the specification's license.

| Direct dependency                                                            | Use                                              | Upstream license  |
| ---------------------------------------------------------------------------- | ------------------------------------------------ | ----------------- |
| [png](https://github.com/image-rs/image-png)                                 | Decode and compare page images                   | MIT OR Apache-2.0 |
| [pulldown-cmark](https://github.com/pulldown-cmark/pulldown-cmark)           | Identify literal Markdown code and source ranges | MIT               |
| [regex](https://github.com/rust-lang/regex)                                  | Parse notation and supported source syntax       | MIT OR Apache-2.0 |
| [roxmltree](https://github.com/RazrFalcon/roxmltree)                         | Inspect MathML and Poppler text geometry         | MIT OR Apache-2.0 |
| [serde](https://github.com/serde-rs/serde)                                   | Serialize conversion evidence                    | MIT OR Apache-2.0 |
| [serde_json](https://github.com/serde-rs/json)                               | Read and write document ASTs and reports         | MIT OR Apache-2.0 |
| [sha2](https://github.com/RustCrypto/hashes)                                 | Bind inputs, tools and outputs by SHA-256        | MIT OR Apache-2.0 |
| [unicode-normalization](https://github.com/unicode-rs/unicode-normalization) | Compare equivalent rendered characters           | MIT OR Apache-2.0 |

The container also includes these programs, with their own licenses:

- [Typst](https://github.com/typst/typst): Apache-2.0. The official executable bundles fonts;
  [font assets and their licenses](https://github.com/typst/typst-assets/tree/main/files/fonts)
  remain subject to their respective licenses. The template uses bundled New Computer Modern math and DejaVu Sans Mono. Body text uses
  separately supplied Microsoft Times New Roman fonts; their license is in the original core-font
  distribution. No Times New Roman files are committed to this repository or copied into its
  rendering image. `fonts.json` records the original archive and the four face checksums.
- [Pandoc](https://github.com/jgm/pandoc): GPL-2.0-or-later. It runs as a separate process; the build
  does not link Pandoc into the Rust program.
- [Poppler](https://poppler.freedesktop.org/): GPL-2.0-or-later. Its command-line tools inspect PDF
  text and render independent page images.
- Rust, Cargo, Debian and the ordinary container utilities retain their upstream licenses.

Archive and executable hashes for Typst and Pandoc are in `toolchain.json`. Docker image digests
are in `Dockerfile`. Downloading tools belongs to installation and image construction; document
rendering in the container has no network access. See [`docs/PDF-BUILD.md`](../../docs/PDF-BUILD.md)
for verification limits and retained evidence.
