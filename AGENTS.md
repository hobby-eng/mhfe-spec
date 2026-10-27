# mhfe_spec agent instructions

This repository is part of the `bip_tools` workspace. If a workspace `AGENTS.md` exists one
directory above this repository, read and follow it first. Its core rules: edit only this checkout
in place, never create another copy or worktree, never delete project directories, do not commit or
push without an explicit request, and write everything in English only (code, comments, commits,
documentation).

This is the specification for the `../mhfe` implementation. Its document build produces PDFs; it
does not build or execute the encryption implementation.

## Checks

- Every vector in `vectors/` must be reproducible by the current `mhfe` implementation; verify with
  its test suite before changing a vector or a specified parameter.
- Security and performance claims in `README.md` (the specification) and `docs/` must match `mhfe`'s
  code and `SECURITY.md`; report mismatches instead of editing one side silently.
- A specification release records the implementation revision it was checked against in
  `CHANGELOG.md`; keep `CITATION.cff` consistent.
- Document and analysis checks: `python3 scripts/check-spec.py documents <english.rs>` and
  `python3 scripts/check-spec.py analysis <english.rs> vectors/suite3/zero-12.json`, with the
  `bip39` crate's `src/language/english.rs` from the Cargo registry in `../workingspace/cargo`
  (`scripts/README.md`).
- Requirement identifiers: `python3 scripts/check-requirements.py --self-test`. A new requirement
  sentence gets the next free number of its section's code, and the appendix range grows with it;
  never renumber, reuse or move an identifier, and record changed or retired ones in `CHANGELOG.md`.
  A retired identifier stays in its appendix range as "`X-1` to `X-9`; retired: `X-4`". A
  requirement that moves to another section retires its old identifier and takes the next number of
  its new code.
- Profile vectors: `python3 scripts/check-profile-vectors.py <english.rs> <eff_large_wordlist.txt>`,
  with the EFF list from `../mhfe/vendor/eff-large-wordlist/`. The JSON files in `vectors/profiles/`
  and the tables of its README hold the same cases; change both together and regenerate
  `SHA256SUMS`.
- Format Markdown with `pnpm format` and check it with `pnpm format:check` (Prettier 3.9.9, 100
  columns, prose wrapped). The formatter is local only: `package.json`, `pnpm-lock.yaml`,
  `.node-version`, `.prettierrc.json`, `.prettierignore` and `node_modules/` are listed in
  `.git/info/exclude` and must never be committed. Vector JSON files and `docs/audits/` are excluded
  from formatting on purpose.
- PDF build and converter regression checks: `node scripts/build-pdfs.mjs` (Docker, network disabled
  during rendering). See `docs/PDF-BUILD.md`. Its published, pinned toolchain is in `tooling/pdf/`;
  unlike the root formatter configuration, that manifest and lockfile are tracked. Build output and
  conversion evidence stay in ignored `output/`. The owner explicitly requested tracked PDF copies:
  refresh both files and `SHA256SUMS` in `docs/pdf/` after a successful build and visual review, as
  described in `docs/PDF-BUILD.md`. Do not claim that automated rendering checks prove mathematical
  correctness or replace visual review.
