#!/usr/bin/env python3
"""Regenerate compiler outputs from existing inputs into new evidence; never overwrite proof sources."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import sys

from check_lean import guarded, memory


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["aeneas", "charon", "fresh-aeneas"])
    parser.add_argument("artifact", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    artifact, evidence = args.artifact.resolve(), args.evidence.resolve()
    workspace = Path(__file__).resolve().parent.parents[3]
    tools = workspace / "workingspace"
    env = dict(os.environ, CARGO_HOME=str(tools / "cargo"), RUSTUP_HOME=str(tools / "rustup"),
               XDG_CACHE_HOME=str(tools / "hax/cache"), CARGO_NET_OFFLINE="true", RUSTUP_NO_UPDATE_CHECK="1",
               PATH=str(tools / "cargo/bin") + ":" + os.environ["PATH"])
    evidence.mkdir(parents=True, exist_ok=True)
    state = memory()
    reserve = state["MemTotal"] // 20
    env["CARGO_BUILD_JOBS"] = str(max(1, min(os.cpu_count() or 1,
        (state["MemAvailable"] - reserve - 2 * 1024 * 1024) // (768 * 1024))))
    if args.phase == "charon":
        line = next(line for line in (artifact / "logs/extract-all.log").read_text().splitlines()
                    if "cmd > " in line)
        command = shlex.split(line.split("cmd > ", 1)[1])
        output = evidence / "charon/mhfe_core.llbc"
        output.parent.mkdir(parents=True, exist_ok=True)
        command[command.index("--dest-file") + 1] = str(output)
        command.extend(["--locked", "--offline"])
        env["CARGO_TARGET_DIR"] = str(evidence / "charon-target")
        code = guarded("regenerate-charon", ["unshare", "-rn", *command], env,
                       artifact / "harness", evidence)
        if code:
            return code
        value = json.loads(output.read_text())
        assert value.get("has_errors") is False
        (evidence / "charon-result.json").write_text(json.dumps(
            {"exitCode": code, "file": str(output), "sha256": digest(output),
             "hasErrors": value.get("has_errors"), "topLevelKeys": sorted(value)}, indent=2) + "\n")
        return 0
    source = (artifact / "lean/llbc/mhfe_core.llbc" if args.phase == "aeneas"
              else evidence / "charon/mhfe_core.llbc")
    destination = evidence / args.phase
    destination.mkdir(parents=True, exist_ok=True)
    binary = tools / "hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas"
    command = ["unshare", "-rn", str(binary), "-backend", "lean", "-split-files",
               "-filter-trait-methods", "-loops-to-rec", str(source), "-dest", str(destination),
               "-subdir", "MhfeCore/Extraction"]
    code = guarded("regenerate-" + args.phase, command, env, evidence, evidence)
    comparisons = []
    for filename in ["Funs.lean", "Types.lean"]:
        generated = destination / "MhfeCore/Extraction" / filename
        original = artifact / "lean/MhfeCore/Extraction" / filename
        comparisons.append({"file": filename, "originalSha256": digest(original),
                            "generatedSha256": digest(generated) if generated.exists() else None})
    (evidence / (args.phase + "-result.json")).write_text(json.dumps(
        {"exitCode": code, "inputSha256": digest(source), "binarySha256": digest(binary),
         "files": comparisons}, indent=2) + "\n")
    return code or int(not all(row["originalSha256"] == row["generatedSha256"] for row in comparisons))


if __name__ == "__main__":
    sys.exit(main())
