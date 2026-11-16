#!/usr/bin/env bash
# Tests check.sh itself on a synthetic project with a stand-in for lake. No Lean is needed.
# Cases: a failing build; a build without the axiom inventory line; a module that the kernel
# replay rejects; compiled modules left by an earlier build; a run in which every step passes.
# Exit status: 0 when every case gives the expected status, 1 otherwise.
set -u
here=$(cd "$(dirname "$0")" && pwd) || exit 1
work=$(mktemp -d) || exit 1
trap 'rm -rf "$work"' EXIT
failures=0

# The stand-in reads its behaviour from the environment:
#   STUB_BUILD     exit status of "lake build"
#   STUB_INVENTORY 1 prints the inventory line, 0 prints none
#   STUB_REJECT    module that "lake env leanchecker" rejects (empty: none)
cat > "$work/lake" <<'EOF'
#!/usr/bin/env bash
case "$1" in
  build)
    [ "${STUB_INVENTORY:-1}" = 1 ] && echo "info: Checkpoint.lean: MHFE_COMPLETE_AXIOM_INVENTORY|2|1|standard"
    exit "${STUB_BUILD:-0}" ;;
  env)
    [ "$2" = leanchecker ] || exit 64
    [ "$3" = "${STUB_REJECT:-}" ] && { echo "leanchecker found a problem in $3" >&2; exit 1; }
    echo "$3" >> "$STUB_LOG"
    exit 0 ;;
  *) exit 64 ;;
esac
EOF
chmod +x "$work/lake"

project() {  # a fresh synthetic project with two chapters
  rm -rf "$work/project"
  mkdir -p "$work/project/MhfeLean/Chapters"
  cp "$here/check.sh" "$work/project/check.sh"
  : > "$work/project/MhfeLean/Chapters/Alpha.lean"
  : > "$work/project/MhfeLean/Chapters/Beta.lean"
  : > "$work/replayed"
}

expect() {  # name, expected status, then the environment of the run
  local name=$1 want=$2; shift 2
  env LAKE="$work/lake" STUB_LOG="$work/replayed" "$@" "$work/project/check.sh" > "$work/out" 2> "$work/err"
  local got=$?
  if [ "$got" -eq "$want" ]; then
    printf 'ok      %s (status %s)\n' "$name" "$got"
  else
    printf 'WRONG   %s: status %s, expected %s\n' "$name" "$got" "$want"
    sed 's/^/        /' "$work/err"
    failures=$((failures + 1))
  fi
}

project
expect "a failing build" 1 STUB_BUILD=7
if [ -s "$work/replayed" ]; then echo "WRONG   a failing build was followed by a replay"; failures=$((failures + 1)); fi

project
expect "a build without the inventory line" 1 STUB_INVENTORY=0

project
expect "a module that the kernel replay rejects" 1 STUB_REJECT=MhfeLean.Chapters.Alpha
if ! grep -q 'FAILED    MhfeLean.Chapters.Alpha' "$work/err"; then
  echo "WRONG   the rejected module is not named"; failures=$((failures + 1))
fi
if grep -q Beta "$work/replayed"; then
  echo "WRONG   the replay continued after a rejected module"; failures=$((failures + 1))
fi

project
mkdir -p "$work/project/.lake/build/lib/lean"
: > "$work/project/.lake/build/lib/lean/MhfeLean.olean"
expect "compiled modules of an earlier build" 2
if [ -s "$work/replayed" ]; then echo "WRONG   a refused start was followed by a replay"; failures=$((failures + 1)); fi

project
expect "every step passes" 0
if [ "$(sort "$work/replayed" | tr '\n' ' ')" != "MhfeLean.Chapters.Alpha MhfeLean.Chapters.Beta " ]; then
  echo "WRONG   not every chapter was replayed exactly once"; failures=$((failures + 1))
fi

if [ "$failures" -eq 0 ]; then
  echo "check.sh behaves as expected in all five cases"
else
  echo "$failures deviation(s)"
  exit 1
fi
