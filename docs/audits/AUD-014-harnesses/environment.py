#!/usr/bin/env python3
"""Record existing tool identities and recheck the frozen code-proof inputs, without installing."""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    workspace, evidence = args.workspace.resolve(), args.evidence.resolve()
    snapshot = json.loads((evidence / "snapshot.json").read_text())
    for row in snapshot["files"]:
        assert digest(workspace / row["path"]) == row["sha256"], row["path"]
    context = json.loads((evidence / "model-context.json").read_text())
    baseline = json.loads((evidence.parent / "AUD-012-evidence/snapshot.json").read_text())
    old = baseline["files"]
    if isinstance(old, list):
        old = {row["path"]: row["sha256"] for row in old}
    for row in context["files"]:
        assert digest(workspace / row["path"]) == row["sha256"] == old[row["path"]], row["path"]
    binaries = {
        "lean": ("workingspace/lean/lean-4.35.0-linux/bin/lean", ["--version"]),
        "lake": ("workingspace/lean/lean-4.35.0-linux/bin/lake", ["--version"]),
        "cargo-hax": ("workingspace/hax/bin-0.5.0/cargo-hax", ["hax", "--version"]),
        "charon": ("workingspace/hax/cache/hax/tools/charon/nightly-2026.10.31/charon", ["version"]),
        "aeneas": ("workingspace/hax/cache/hax/tools/aeneas/build-2b9e3ea/aeneas", ["-version"]),
    }
    identities = []
    for name, (relative, flags) in binaries.items():
        path = workspace / relative
        result = subprocess.run([str(path), *flags], capture_output=True, text=True)
        identities.append({"name": name, "path": relative, "sha256": digest(path),
                           "versionArgv": [relative, *flags], "versionExit": result.returncode,
                           "versionOutput": result.stdout + result.stderr})
    repositories = {}
    for name in ["mhfe_core", "mhfe_spec"]:
        def git(*argv):
            return subprocess.check_output(["git", "-C", str(workspace / name), *argv], text=True).strip()
        repositories[name] = {"head": git("rev-parse", "HEAD"),
                              "originMain": git("rev-parse", "origin/main"),
                              "trackedStatus": git("status", "--short", "--untracked-files=no")}
    data = {"capturedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "identities": identities, "repositories": repositories,
            "unchangedFrozenInputs": len(snapshot["files"]),
            "unchangedImportedModelSourcesAgainstAUD012": len(context["files"])}
    (evidence / "environment.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
