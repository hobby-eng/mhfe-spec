#!/usr/bin/env python3
"""Strictly check selected EasyCrypt sources in place with local command evidence."""

import argparse
import datetime
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import time


def memory():
    """Read physical memory accounting, including reclaimable cache."""
    values = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, value = line.split(":", 1)
        if key in {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}:
            values[key] = int(value.split()[0])
    return values


def main():
    """Compile every requested source without copying it or trusting cached proofs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("runner", type=Path)
    parser.add_argument("--include", action="append", type=Path, default=[])
    parser.add_argument("names", nargs="+")
    args = parser.parse_args()
    source, evidence, runner = (
        args.source.resolve(), args.evidence.resolve(), args.runner.resolve()
    )
    evidence.mkdir(parents=True, exist_ok=True)
    cached = list(source.glob("*.eco"))
    if cached:
        raise RuntimeError(
            "Refusing cached source directory; -no-eco does not bypass existing caches: "
            + ", ".join(path.name for path in cached)
        )
    reserve = math.ceil(memory()["MemTotal"] / 20 / 1024)
    launch = (
        "import importlib.util,sys; "
        "s=importlib.util.spec_from_file_location('audit_resource_runner',sys.argv.pop(1)); "
        "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
        f"m.FLOOR_MIB=max(m.FLOOR_MIB,{reserve}); m.main()"
    )
    results = []
    for name in args.names:
        path = source / f"{name}.ec"
        if path.with_suffix(".eco").exists():
            raise RuntimeError(f"Refusing cached root: {path.name}")
        command = [
            sys.executable, "-c", launch, str(runner), "compile", "-no-eco",
            "-I", str(source),
        ]
        for include in args.include:
            command.extend(["-I", str(include.resolve())])
        command.append(str(path))
        log = evidence / f"strict-{name}.log"
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        before = time.monotonic()
        with log.open("wb") as output, (evidence / "resources.jsonl").open("a") as samples:
            process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT)
            while process.poll() is None:
                samples.write(json.dumps({
                    "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "module": name, **memory(),
                }) + "\n")
                samples.flush()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
        record = {
            "name": name, "command": command, "cwd": str(Path.cwd()),
            "startedUtc": start,
            "endedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "elapsedSeconds": round(time.monotonic() - before, 3),
            "exitCode": process.returncode,
            "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        }
        (evidence / f"strict-{name}.command.json").write_text(
            json.dumps(record, indent=2) + "\n"
        )
        results.append(record)
        print(json.dumps(record), flush=True)
    (evidence / "compile-summary.json").write_text(json.dumps(results, indent=2) + "\n")
    return int(any(result["exitCode"] != 0 for result in results))


if __name__ == "__main__":
    sys.exit(main())
