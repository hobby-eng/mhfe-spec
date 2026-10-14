# mhfe_spec agent instructions

This repository is part of the `bip_tools` workspace. If a workspace `AGENTS.md` exists one
directory above this repository, read and follow it first. Its core rules: edit only this checkout
in place, never create another copy or worktree, never delete project directories, do not commit or
push without an explicit request, and write everything in English only (code, comments, commits,
documentation).

This is the specification for the `../mhfe` implementation. There is no build.

## Checks

- Every vector in `vectors/` must be reproducible by the current `mhfe` implementation; verify with
  its test suite before changing a vector or a specified parameter.
- Security and performance claims in `README.md` (the specification) and `docs/` must match `mhfe`'s
  code and `SECURITY.md`; report mismatches instead of editing one side silently.
- A specification release records the implementation revision it was checked against in
  `CHANGELOG.md`; keep `CITATION.cff` consistent.
- Document and analysis checks: `python3 scripts/check-spec.py documents <english.rs>` and
  `python3 scripts/check-spec.py analysis <english.rs> ../mhfe/tests/fixtures/suite3-vectors/zero-12.json`,
  with the `bip39` crate's `src/language/english.rs` from the Cargo registry in
  `../workingspace/cargo` (`scripts/README.md`).
- Format Markdown with `pnpm format` and check it with `pnpm format:check` (Prettier 3.9.9, 100
  columns, prose wrapped). The formatter is local only: `package.json`, `pnpm-lock.yaml`,
  `.node-version`, `.prettierrc.json`, `.prettierignore` and `node_modules/` are listed in
  `.git/info/exclude` and must never be committed. Vector JSON files and `docs/audits/` are excluded
  from formatting on purpose.
