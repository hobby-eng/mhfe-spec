#!/usr/bin/env bash
# Checks every proof of the development from its sources:
#   1. builds all modules with Lake (the elaborator and the kernel check every declaration);
#   2. requires the line that Checkpoint.lean prints after it has found no unchecked declaration,
#      no axiom of the development and no axiom other than propext, Classical.choice, Quot.sound;
#   3. replays every compiled chapter through Lean's kernel with leanchecker, one module at a time.
#
# Usage: ./check.sh        LAKE names another lake executable (default: lake).
# Exit status: 0 every step passed; 1 a step failed, named on standard error; 2 the check did not
# start.
#
# The script does not start when compiled modules of the development exist: Lake keeps a compiled
# module whose source is unchanged, so its source would not be checked again. It deletes nothing.
set -u
cd "$(dirname "$0")" || exit 2
lake=${LAKE:-lake}
build=.lake/build

shopt -s nullglob
chapters=(MhfeLean/Chapters/*.lean)
shopt -u nullglob
if [ "${#chapters[@]}" -eq 0 ]; then
  echo "check.sh: no chapter found in MhfeLean/Chapters" >&2
  exit 2
fi
if ! command -v "$lake" >/dev/null 2>&1; then
  echo "check.sh: '$lake' not found; install elan or set LAKE" >&2
  exit 2
fi
if [ -d "$build" ] && [ -n "$(find "$build" -name '*.olean' -print -quit)" ]; then
  echo "check.sh: $build holds compiled modules of an earlier build. Lake would keep them" >&2
  echo "without checking their sources again. Remove the folder (rm -rf $build) and run the" >&2
  echo "script again." >&2
  exit 2
fi

log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT

echo "== build"
"$lake" build 2>&1 | tee "$log"
code=${PIPESTATUS[0]}
if [ "$code" -ne 0 ]; then
  echo "FAILED    lake build (exit $code)" >&2
  exit 1
fi
inventory=$(grep -o 'MHFE_COMPLETE_AXIOM_INVENTORY|[0-9]*|[0-9]*|standard' "$log" | sort -u)
if [ "$(printf '%s\n' "$inventory" | grep -c .)" -ne 1 ]; then
  echo "FAILED    the build did not print exactly one axiom inventory line" >&2
  exit 1
fi

echo "== kernel replay"
for file in "${chapters[@]}"; do
  module=MhfeLean.Chapters.$(basename "$file" .lean)
  "$lake" env leanchecker "$module"
  code=$?
  if [ "$code" -ne 0 ]; then
    echo "FAILED    $module (leanchecker exit $code)" >&2
    exit 1
  fi
  printf 'replayed  %s\n' "$module"
done

echo "== result"
echo "$inventory"
echo "all ${#chapters[@]} chapters built and replayed"
