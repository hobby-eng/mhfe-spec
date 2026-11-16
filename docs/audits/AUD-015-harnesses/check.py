#!/usr/bin/env python3
"""Execute the corrected regeneration gate only in synthetic tool fixtures, without source edits."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["regression", "regression-no-file-guard", "real", "install-error"])
    parser.add_argument("artifact", type=Path)
    parser.add_argument("new_scratch", type=Path)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--label")
    args = parser.parse_args()
    artifact, scratch, evidence = (p.resolve() for p in [args.artifact, args.new_scratch, args.evidence])
    workspace = Path(__file__).resolve().parents[4]
    spec = importlib.util.spec_from_file_location("audit_guard", Path(__file__).resolve().parents[1] /
                                               "AUD-014-harnesses/check_lean.py")
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    scratch.mkdir(parents=True, exist_ok=False)
    package = scratch / "mock/tmp/artifact"
    (package / "tools").mkdir(parents=True)
    # Only tool scripts are fixture copies; no Rust/Lean project checkout is copied.
    for name in ["aeneas-std.sh", "splice.py", "test-regeneration.sh"]:
        (package / "tools" / name).write_bytes((artifact / "tools" / name).read_bytes())
    env = dict(os.environ)
    if args.phase.startswith("regression"):
        label = "regression13" if args.phase == "regression" else "regression13-no-file-guard"
        if args.phase != "regression":
            wrapper = package / "tools/aeneas-std.sh"
            source = wrapper.read_text()
            needle = '  [ -s "$staged/$kind.lean" ] || fail "Aeneas wrote no $kind.lean"'
            assert source.count(needle) == 1
            wrapper.write_text(source.replace(needle, "  : # Synthetic mutation: remove only the explicit file guard"))
        status = guard.guarded(label, ["unshare", "-rn", "bash", str(package / "tools/test-regeneration.sh")],
                               env, package, evidence)
        log = (evidence / (label + ".log")).read_text()
        cases = [line for line in log.splitlines() if line.startswith("ok   ")]
        result = {"exitCode": status, "cases": cases, "caseCount": len(cases)}
        assert status == 0 and len(cases) == 13 and "all cases pass" in log
    elif args.phase == "install-error":
        lean = package / "lean"
        extraction = lean / "MhfeCore/Extraction"
        models = lean / "MhfeCore/Assumptions"
        extraction.mkdir(parents=True)
        models.mkdir(parents=True)
        (lean / "llbc").mkdir()
        (lean / "llbc/mhfe_core.llbc").write_text("{}\n")
        (models / "Translations.lean").write_text("/-- Synthetic helper. -/\ndef helper : Nat := 1\n")
        (models / "CodePrelude.lean.txt").write_text("")
        executable = scratch / "mock/workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas"
        executable.parent.mkdir(parents=True)
        executable.write_text('''#!/usr/bin/env python3
import os, sys
from pathlib import Path
args = sys.argv[1:]
out = Path(args[args.index("-dest") + 1]) / args[args.index("-subdir") + 1]
out.mkdir(parents=True, exist_ok=True)
(out / "Types.lean").write_text("-- synthetic types\\n")
(out / "Funs.lean").write_text("module\\npublic import MhfeCore.Extraction.FunsExternal\\nnamespace mhfe_core\\n/-- Synthetic extraction. -/\\ndef sample : Nat := " + os.environ["SYNTHETIC_VALUE"] + "\\nend mhfe_core\\n")
''')
        executable.chmod(0o755)
        env["SYNTHETIC_VALUE"] = "0"
        first = guard.guarded("install-control", ["unshare", "-rn", "bash", str(package / "tools/aeneas-std.sh"), "--record"],
                              env, package, evidence)
        assert first == 0
        before_funs = sha(extraction / "Funs.lean")
        before_manifest = sha(lean / "MANIFEST-code.txt")
        # Fault: an ordinary conflicting output-directory entry makes a later rename fail.
        # The fixture's earlier valid generated files and manifest remain present.
        (lean / "MhfeCore/Code.lean").unlink()
        (lean / "MhfeCore/Code.lean").mkdir()
        env["SYNTHETIC_VALUE"] = "1"
        status = guard.guarded("install-error", ["unshare", "-rn", "bash", str(package / "tools/aeneas-std.sh"), "--record"],
                               env, package, evidence)
        log = (evidence / "install-error.log").read_text()
        result = {"exitCode": status, "controlExit": first,
                  "reportedNothingReplaced": "nothing in lean/ was replaced" in log,
                  "funsBeforeSha256": before_funs, "funsAfterSha256": sha(extraction / "Funs.lean"),
                  "funsChanged": before_funs != sha(extraction / "Funs.lean"),
                  "manifestUnchanged": before_manifest == sha(lean / "MANIFEST-code.txt"),
                  "codeTargetStillDirectory": (lean / "MhfeCore/Code.lean").is_dir(),
                  "renameErrorSeen": "IsADirectoryError" in log}
        assert status != 0 and result["reportedNothingReplaced"] and result["funsChanged"]
        assert result["manifestUnchanged"] and result["renameErrorSeen"]
    else:
        lean = package / "lean"
        extraction = lean / "MhfeCore/Extraction"
        models = lean / "MhfeCore/Assumptions"
        extraction.mkdir(parents=True)
        models.mkdir(parents=True)
        (lean / "llbc").mkdir()
        (lean / "llbc/mhfe_core.llbc").symlink_to(artifact / "lean/llbc/mhfe_core.llbc")
        for name in ["Translations.lean", "CodePrelude.lean.txt"]:
            (models / name).symlink_to(artifact / "lean/MhfeCore/Assumptions" / name)
        (lean / "MANIFEST-code.txt").write_bytes((artifact / "lean/MANIFEST-code.txt").read_bytes())
        executable = scratch / "mock/workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas"
        executable.parent.mkdir(parents=True)
        executable.symlink_to(workspace / "workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas")
        input_before = sha(artifact / "lean/llbc/mhfe_core.llbc")
        status = guard.guarded(args.label or "real-wrapper", ["unshare", "-rn", "bash", str(package / "tools/aeneas-std.sh")],
                               env, package, evidence)
        comparisons = []
        for relative in ["MhfeCore/Extraction/Types.lean", "MhfeCore/Extraction/Funs.lean",
                         "MhfeCore/Code.lean", "REPLACED-blocks.lean.txt", "MANIFEST-code.txt"]:
            target = lean / relative
            comparisons.append({"path": relative, "expected": sha(artifact / "lean" / relative),
                                "actual": sha(target) if target.exists() else None})
        result = {"exitCode": status, "files": comparisons, "inputLLBCSha256": input_before,
                  "inputUnchangedDuringRun": input_before == sha(artifact / "lean/llbc/mhfe_core.llbc")}
        assert status == 0 and all(r["expected"] == r["actual"] for r in comparisons)
        assert result["inputUnchangedDuringRun"]
    (evidence / (args.phase + "-result.json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
