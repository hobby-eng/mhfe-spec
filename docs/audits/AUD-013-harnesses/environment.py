#!/usr/bin/env python3
"""Record the installed release/main EasyCrypt identities without installing or changing tools."""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    tools = args.workspace.resolve() / "workingspace"
    data = []
    for label, switch, suffix in [("release r2026.10", "mhfe-easycrypt", ""),
                                  ("main ce19cb6", "mhfe-easycrypt-main", "-main")]:
        binary = tools / "opam-easycrypt" / switch / "bin/easycrypt"
        config = tools / "easycrypt-provers" / ("why3" + suffix + ".conf")
        commit = subprocess.check_output(["git", "-C", str(tools / "opam-easycrypt" / switch /
                                          ".opam-switch/sources/easycrypt"), "rev-parse", "HEAD"], text=True).strip()
        versions = {}
        for name, path in [("why3", tools / "opam-easycrypt" / switch / "bin/why3"), *[
            (name, tools / "easycrypt-provers" / ("bin" + suffix) / name)
            for name in ["alt-ergo", "z3", "cvc5"]]]:
            version = subprocess.check_output([str(path), "--version"], text=True).strip()
            versions[name] = {"versionOutput": version,
                              "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        data.append({"label": label, "binary": str(binary),
                     "binarySha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
                     "sourceCommit": commit, "why3Config": str(config),
                     "configSha256": hashlib.sha256(config.read_bytes()).hexdigest(), "tools": versions})
    args.output.write_text(json.dumps({"capturedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                      "toolchains": data}, indent=2) + "\n")
    print(json.dumps([{key: item[key] for key in ["label", "sourceCommit", "binarySha256"]} for item in data]))


if __name__ == "__main__":
    main()
