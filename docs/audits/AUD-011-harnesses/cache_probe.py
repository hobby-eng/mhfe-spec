#!/usr/bin/env python3
"""Demonstrate that an existing weak EasyCrypt cache bypasses -no-eco checking.

Diagnostic only: weak checking applies exclusively to a new false synthetic file.
Never use the deliberately produced cache as proof evidence.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    """Retain all three phases and fail if the observed statuses change."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("easycrypt", type=Path)
    parser.add_argument("why3_config", type=Path)
    parser.add_argument("new_scratch", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    args.new_scratch.mkdir(parents=True, exist_ok=False)
    source = args.new_scratch.resolve() / "AuditCacheFalse.ec"
    source.write_text("require import AllCore.\nlemma audit_cache_false : false.\nproof. smt(). qed.\n")
    memory = dict(
        (line.split(":", 1)[0], int(line.split()[1]))
        for line in Path("/proc/meminfo").read_text().splitlines()
        if line.startswith(("MemTotal:", "MemAvailable:"))
    )
    if memory["MemAvailable"] < memory["MemTotal"] // 20 + 1024 * 1024:
        raise RuntimeError("Not enough machine-wide headroom for the bounded diagnostic")
    base = [
        "systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=1G",
        "-p", "MemorySwapMax=0", str(args.easycrypt.resolve()), "compile",
        "-why3", str(args.why3_config.resolve()),
    ]
    observed = []
    for name, options in [
        ("cache-create-weak", ["-pragmas", "Proofs:weak"]),
        ("cache-strict-replay", ["-no-eco"]),
        ("cache-without-cache", ["-no-eco"]),
    ]:
        if name == "cache-without-cache":
            cache = source.with_suffix(".eco")
            cache.rename(cache.with_suffix(".eco.retained"))
        command = [sys.executable, str(Path(__file__).with_name("record.py")),
                   str(args.evidence), name, *base, *options, str(source)]
        observed.append(subprocess.run(command).returncode)
    print(json.dumps({"observed": observed, "expected": [0, 0, 1],
                      "admissionMemoryKiB": memory}))
    return int(observed != [0, 0, 1])


if __name__ == "__main__":
    sys.exit(main())
