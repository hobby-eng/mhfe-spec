#!/usr/bin/env python3
"""Exercise the real regeneration/splice scripts with a failing synthetic translator only."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("new_scratch", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    args.new_scratch.mkdir(parents=True, exist_ok=False)
    root = args.new_scratch.resolve() / "mockroot"
    package = root / "tmp/synthetic-artifact"
    (package / "tools").mkdir(parents=True)
    models = package / "lean/MhfeCore/Assumptions"
    models.mkdir(parents=True)
    (package / "lean/MhfeCore/Extraction").mkdir(parents=True)
    (package / "lean/llbc").mkdir(parents=True)
    (package / "lean/llbc/mhfe_core.llbc").write_text("{}\n")
    (models / "Translations.lean").write_text("/-- Synthetic helper. -/\ndef helper : Nat := 1\n")
    (models / "CodePrelude.lean.txt").write_text("")
    for filename in ["aeneas-std.sh", "splice.py"]:
        # Two script fixtures, not a copy/checkout of any Rust or Lean project tree.
        (package / "tools" / filename).write_bytes((args.artifact / "tools" / filename).read_bytes())
    translator = root / "workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas"
    translator.parent.mkdir(parents=True)
    translator.write_text('''#!/usr/bin/env python3
from pathlib import Path
import sys
args = sys.argv[1:]
out = Path(args[args.index("-dest") + 1]) / args[args.index("-subdir") + 1]
out.mkdir(parents=True, exist_ok=True)
(out / "Funs.lean").write_text("module\\npublic import MhfeCore.Extraction.FunsExternal\\nnamespace mhfe_core\\n/-- Synthetic partial output. -/\\ndef sample : Nat := 0\\nend mhfe_core\\n")
(out / "Types.lean").write_text("-- synthetic partial types\\n")
print("[Error] synthetic translator failure after partial output")
sys.exit(7)
''')
    translator.chmod(0o755)
    process = subprocess.run(["bash", str(package / "tools/aeneas-std.sh")],
                             cwd=package, capture_output=True, text=True)
    log = args.evidence / "pipeline-probe-inner.log"
    log.write_text(process.stdout + process.stderr)
    code = package / "lean/MhfeCore/Code.lean"
    result = {"translatorExit": 7, "wrapperExit": process.returncode,
              "diagnosticSeen": "synthetic translator failure" in process.stdout,
              "downstreamCodeCreated": code.exists(),
              "containsSyntheticDefinition": code.exists() and "def sample : Nat := 0" in code.read_text(),
              "rawLogSha256": hashlib.sha256(log.read_bytes()).hexdigest()}
    (args.evidence / "pipeline-probe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    return int(not (result["wrapperExit"] == 0 and result["diagnosticSeen"] and
                    result["downstreamCodeCreated"] and result["containsSyntheticDefinition"]))


if __name__ == "__main__":
    raise SystemExit(main())
