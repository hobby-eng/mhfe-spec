#!/usr/bin/env bash
# Translates the LLBC that `cargo hax into lean` produced (lean/llbc/mhfe_core.llbc, made by Charon)
# with the same Aeneas, but on its own standard library instead of hax's core models
# (`-core-models-lib`), whose definitions disagree with the code this Aeneas generates (see
# README.md). Then builds lean/MhfeCore/Code.lean with tools/splice.py.
#   tools/aeneas-std.sh            regenerate and check against lean/MANIFEST-code.txt
#   tools/aeneas-std.sh --record   regenerate and record a new manifest (after a reviewed change)
# Aeneas writes into a staging folder. Nothing in lean/ is replaced unless Aeneas exits 0, reports
# no error, writes Types.lean and Funs.lean, and splice.py accepts the result; otherwise the script
# exits 1. splice.py then installs the staged files and Code.lean together (each written next to its
# target, then renamed over it). The full output of Aeneas is kept in logs/aeneas-std.log.
# The workspace holds mhfe_spec, the mhfe_core checkout and the toolchains in workingspace/;
# MHFE_WORKSPACE overrides it.
WS_ROOT=${MHFE_WORKSPACE:-$(cd "$(dirname "$0")/../../../.." && pwd)}
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
case "${1:-}" in
  "") mode=() ;;
  --record) mode=(--record) ;;
  *) echo "usage: tools/aeneas-std.sh [--record]" >&2; exit 2 ;;
esac
A=$WS_ROOT/workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas
mkdir -p "$here/logs"
log=$here/logs/aeneas-std.log
stage=$(mktemp -d "$here/logs/aeneas-stage.XXXXXX")
trap 'rm -rf "$stage"' EXIT
staged=$stage/MhfeCore/Extraction
status=0
"$A" -backend lean -split-files -filter-trait-methods -loops-to-rec "$here/lean/llbc/mhfe_core.llbc" \
  -dest "$stage" -subdir MhfeCore/Extraction >"$log" 2>&1 || status=$?
# Aeneas colours and pads its levels (`[Info ]`) and draws progress bars with carriage returns and
# cursor codes: strip the terminal codes, split at carriage returns, allow the padding.
diagnostics=$(sed 's/\x1b\[[0-9;?]*[A-Za-z]//g; s/\r/\n/g' "$log" | grep -E '^\[(Error|Warn) *\]' || true)
if [ -n "$diagnostics" ]; then printf '%s\n' "$diagnostics"; fi
fail() {
  echo "aeneas-std.sh: $1 (full output: $log); nothing in lean/ was replaced" >&2
  exit 1
}
[ "$status" -eq 0 ] || fail "Aeneas exited with status $status"
if grep -qE '^\[Error *\]' <<<"$diagnostics"; then fail "Aeneas reported an error"; fi
for kind in Types Funs; do
  [ -s "$staged/$kind.lean" ] || fail "Aeneas wrote no $kind.lean"
  printf 'module\n\npublic import MhfeCore.Assumptions.%sExternal\n' "$kind" > "$staged/${kind}External.lean"
done
# splice.py checks everything before it writes. A failure while it renames its outputs into place
# leaves the earlier ones installed: each file is replaced whole or not at all.
if ! python3 -I "$here/tools/splice.py" --extraction "$staged" "${mode[@]}"; then
  echo "aeneas-std.sh: splice.py refused the result or failed while installing it" \
    "(full output: $log); after a failure while installing, files of lean/ may already be" \
    "replaced: compare them with lean/MANIFEST-code.txt" >&2
  exit 1
fi
