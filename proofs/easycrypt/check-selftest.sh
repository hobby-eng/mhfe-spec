#!/usr/bin/env bash
# Tests check.sh on cases it must refuse, in a temporary copy that holds only synthetic sources:
#   1. a failing compiler gives a nonzero status and stops the run at the failing file;
#   2. a false theorem with a cache from a weak check is refused before any proof is accepted;
#   3. the same false theorem without its cache fails;
#   4. a true theorem alone passes.
# Cases 2 to 4 run EasyCrypt. Usage: ./check-selftest.sh [ARGUMENTS OF "easycrypt compile"...]
#   EASYCRYPT    the EasyCrypt command, one executable (default: easycrypt)
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
easycrypt="${EASYCRYPT:-easycrypt}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

mkdir "$work/src"
cp "$root/check.sh" "$work/check.sh"
printf 'require import AllCore.\nlemma true_fact : 1 + 1 = 2.\nproof. by []. qed.\n' >"$work/src/Right.ec"
printf 'require import AllCore.\nlemma false_fact : 0 = 1.\nproof. smt(). qed.\n' >"$work/src/Wrong.ec"

expect() { # expect STATUS DESCRIPTION COMMAND...
  local want="$1" what="$2" got=0
  shift 2
  "$@" >"$work/out.txt" 2>&1 || got=$?
  if [ "$got" -ne "$want" ]; then
    echo "FAILED  $what: exit status $got, expected $want" >&2
    cat "$work/out.txt" >&2
    exit 1
  fi
  echo "ok      $what (exit status $got)"
}

printf '#!/usr/bin/env bash\nexit 7\n' >"$work/failing-compiler"
chmod +x "$work/failing-compiler"
expect 1 "a failing compiler stops the check" env EASYCRYPT="$work/failing-compiler" "$work/check.sh" "$@"
if [ "$(grep -c '^FAILED' "$work/out.txt")" -ne 1 ] || grep -q '^ok ' "$work/out.txt"; then
  echo "FAILED  the run did not stop at the first failing file" >&2
  exit 1
fi

(cd "$work/src" && "$easycrypt" compile -pragmas Proofs:weak "$@" -I . Wrong.ec >/dev/null 2>&1) || true
if [ ! -f "$work/src/Wrong.eco" ]; then
  echo "FAILED  the weak check wrote no cache, so case 2 tests nothing" >&2
  exit 1
fi
expect 2 "a false theorem with a weak-check cache is refused" env EASYCRYPT="$easycrypt" "$work/check.sh" "$@"

rm "$work/src/Wrong.eco"
expect 1 "the false theorem without its cache fails" env EASYCRYPT="$easycrypt" "$work/check.sh" "$@"

rm "$work/src/Wrong.ec"
expect 0 "a true theorem alone passes" env EASYCRYPT="$easycrypt" "$work/check.sh" "$@"

echo "check.sh behaves as documented."
