#!/usr/bin/env bash
# Regression test of the regeneration gate (tools/aeneas-std.sh and tools/splice.py). It copies the
# two scripts into a mock tree under logs/, puts a fake Aeneas where the scripts look for it, and
# checks that every failure of the translator or difference from the recorded manifest exits
# nonzero and leaves the recorded files unchanged, while a successful and identical regeneration
# passes and a recording installs the new files. The real lean/ folder is not touched.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$here/logs"
work=$(mktemp -d "$here/logs/regen-test.XXXXXX")
trap 'rm -rf "$work"' EXIT
# The scripts find the workspace four levels above tools/: mock/repo/proofs/code/tools.
unset MHFE_WORKSPACE
art=$work/mock/repo/proofs/code
lean=$art/lean
fake=$work/mock/workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas
mkdir -p "$art/tools" "$lean/llbc" "$lean/MhfeCore/Assumptions" "$lean/MhfeCore/Extraction" "$(dirname "$fake")"
cp "$here/tools/aeneas-std.sh" "$here/tools/splice.py" "$art/tools/"
echo '{}' > "$lean/llbc/mhfe_core.llbc"
printf '/-- A translated block. -/\ndef helper : Nat := 1\n' > "$lean/MhfeCore/Assumptions/Translations.lean"
: > "$lean/MhfeCore/Assumptions/CodePrelude.lean.txt"
echo '-- a stale generated file' > "$lean/MhfeCore/Extraction/Stale.lean"
# The fake translator. FAKE_MODE selects what it does; FAKE_DEF is the body of its one definition
# and FAKE_TYPES the text of Types.lean. Its level tags are coloured and padded as Aeneas does.
cat > "$fake" <<'EOF'
#!/usr/bin/env python3
import os, sys
from pathlib import Path
args = sys.argv[1:]
out = Path(args[args.index("-dest") + 1]) / args[args.index("-subdir") + 1]
mode = os.environ["FAKE_MODE"]
def level(name, colour):
    return f"[\x1b[{colour}m{name}\x1b[39m{' ' * (5 - len(name))}]"
print(level("Info", 92) + " Imported: mhfe_core.llbc")
if mode == "fail-early":
    print(level("Error", 91) + " failure before any output")
    sys.exit(7)
if mode == "missing-output":
    sys.exit(0)
out.mkdir(parents=True, exist_ok=True)
(out / "Types.lean").write_text(os.environ.get("FAKE_TYPES", "-- types\n"))
(out / "Funs.lean").write_text("module\npublic import MhfeCore.Extraction.FunsExternal\nnamespace mhfe_core\n"
                               "/-- A generated block. -/\ndef sample : Nat := " + os.environ.get("FAKE_DEF", "0")
                               + "\nend mhfe_core\n")
if mode == "fail-partial":
    print(level("Error", 91) + " failure after partial output")
    sys.exit(7)
if mode == "fail-silent":
    sys.exit(7)
if mode == "error-exit-0":
    print("\x1b[?25l progress\r" + level("Error", 91) + " an error reported with status 0")
if mode == "warn":
    print(level("Warn", 93) + " a warning")
sys.exit(0)
EOF
chmod +x "$fake"
fails=0
failed() { echo "FAIL $1"; fails=$((fails + 1)); }
snapshot() { (cd "$lean" && find . -type f ! -name 'MANIFEST-code.new.txt' -print0 | sort -z | xargs -0 sha256sum); }
run() { # run <name> <expected: 0 or nonzero> <mode> [--record]
  local name=$1 expect=$2 mode=$3; shift 3
  local before after status=0
  before=$(snapshot)
  FAKE_MODE=$mode bash "$art/tools/aeneas-std.sh" "$@" >"$work/$name.log" 2>&1 || status=$?
  after=$(snapshot)
  if [ "$expect" = 0 ]; then
    if [ "$status" -eq 0 ]; then echo "ok   $name: exit 0"; else failed "$name: exit $status"; fi
  elif [ "$status" -ne 0 ] && [ "$before" = "$after" ]; then
    echo "ok   $name: exit $status, recorded files unchanged"
  else
    failed "$name: exit $status, files changed: $([ "$before" = "$after" ] && echo no || echo yes)"
  fi
}
has() { grep -q "$2" "$lean/$1" 2>/dev/null; }
# A first recording installs the extraction and writes Code.lean and the manifest.
run record 0 ok --record
has MhfeCore/Code.lean 'def sample : Nat := 0' || failed "record: Code.lean"
has MhfeCore/Extraction/Funs.lean 'def sample : Nat := 0' || failed "record: Extraction/Funs.lean"
has MhfeCore/Extraction/Types.lean '^-- types$' || failed "record: Extraction/Types.lean"
has MhfeCore/Extraction/FunsExternal.lean 'Assumptions.FunsExternal' || failed "record: FunsExternal.lean"
[ ! -e "$lean/MhfeCore/Extraction/Stale.lean" ] || failed "record: stale file kept"
has MANIFEST-code.txt '^Types.lean ' || failed "record: no Types.lean in the manifest"
run identical 0 ok
run warning 0 warn
grep -q '^\[Warn \] a warning' "$work/warning.log" || failed "warning: not shown"
run fail-early nonzero fail-early
run fail-partial nonzero fail-partial
run fail-silent nonzero fail-silent
run missing-output nonzero missing-output
run error-exit-0 nonzero error-exit-0
FAKE_TYPES='-- other types' run types-different nonzero ok
FAKE_DEF=1 run funs-different nonzero ok
[ -s "$lean/MANIFEST-code.new.txt" ] || failed "funs-different: no MANIFEST-code.new.txt"
# Recording a change installs it, and the next identical run passes against the new manifest.
FAKE_DEF=1 run record-change 0 ok --record
has MhfeCore/Code.lean 'def sample : Nat := 1' || failed "record-change: Code.lean"
has MhfeCore/Extraction/Funs.lean 'def sample : Nat := 1' || failed "record-change: Extraction/Funs.lean"
[ ! -e "$lean/MANIFEST-code.new.txt" ] || failed "record-change: MANIFEST-code.new.txt left"
FAKE_DEF=1 run identical-after-change 0 ok
run old-output-after-change nonzero ok
[ -z "$(find "$lean" -name '*.splice-tmp')" ] || failed "temporary files left"
# A failure while splice.py installs (a directory where Code.lean goes) can leave earlier files
# installed; the script must exit nonzero and say that files may already be replaced.
mv "$lean/MhfeCore/Code.lean" "$work/Code.lean.saved"
mkdir "$lean/MhfeCore/Code.lean"
status=0
FAKE_MODE=ok FAKE_DEF=2 bash "$art/tools/aeneas-std.sh" --record >"$work/install-error.log" 2>&1 || status=$?
if [ "$status" -ne 0 ] && grep -q 'may already be replaced' "$work/install-error.log"; then
  echo "ok   install-error: exit $status, a partial installation is reported"
else
  failed "install-error: exit $status, a partial installation is not reported"
fi
if [ "$fails" -ne 0 ]; then echo "$fails failures"; exit 1; fi
echo "all cases pass"
