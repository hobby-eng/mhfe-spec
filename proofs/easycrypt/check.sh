#!/usr/bin/env bash
# Checks the whole development from scratch. Every file of src/ is compiled as the main input, in
# strict mode, with every configured prover and without cached results. The script stops at the
# first failure, names the file and returns a nonzero status.
#
# Usage: ./check.sh [ARGUMENTS OF "easycrypt compile"...]
#   for example: ./check.sh -why3 /path/to/why3.conf
#   EASYCRYPT    the EasyCrypt command, one executable (default: easycrypt)
#
# Exit status: 0 every source checked; 1 a source failed; 2 the check did not start.
#
# The check does not start when src/ holds a compiled cache (*.eco). EasyCrypt accepts an
# up-to-date cache without checking the proofs again, with -no-eco too, and whether a strict or a
# weak check wrote it. The script deletes nothing: remove the caches yourself and run it again.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
src="$root/src"
easycrypt="${EASYCRYPT:-easycrypt}"

shopt -s nullglob
sources=("$src"/*.ec)
if [ "${#sources[@]}" -eq 0 ]; then
  echo "check.sh: no sources in $src" >&2
  exit 2
fi

caches=("$src"/*.eco)
if [ "${#caches[@]}" -ne 0 ]; then
  echo "check.sh: not started, src/ holds compiled caches; remove them and run again:" >&2
  printf '  %s\n' "${caches[@]}" >&2
  exit 2
fi

# A skipped proof or a weak check in a source would make a pass meaningless.
if grep -nE '\<(admit|admitted)\>|Proofs:weak' "${sources[@]}"; then
  echo "check.sh: not started, a source holds admit or a weak-check pragma (lines above)" >&2
  exit 2
fi

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

checked=0
for file in "${sources[@]}"; do
  name="$(basename "$file")"
  if "$easycrypt" compile -no-eco "$@" -I "$src" "$file" >"$log" 2>&1; then
    checked=$((checked + 1))
    echo "ok      $name"
  else
    status=$?
    echo "FAILED  $name (easycrypt exit status $status); the end of its output:" >&2
    tr '\r' '\n' <"$log" | tail -n 20 >&2
    exit 1
  fi
done

caches=("$src"/*.eco)
if [ "${#caches[@]}" -ne 0 ]; then
  echo "check.sh: the check wrote a cache, which -no-eco should prevent:" >&2
  printf '  %s\n' "${caches[@]}" >&2
  exit 1
fi

echo "All $checked sources checked: strict mode, no cache, no admit."
