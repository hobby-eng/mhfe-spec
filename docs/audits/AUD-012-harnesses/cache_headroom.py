#!/usr/bin/env python3
"""Relieve measured cache pressure in this audit's scopes without spending the system reserve."""

import argparse
import datetime
import json
from pathlib import Path
import subprocess
import time


def adjust_once(evidence, only_unit=None):
    """Rebalance cache pressure, optionally restricted to one exact owned unit."""
    result = subprocess.run(
        ["systemctl", "--user", "show", "mhfe-proof-audit-*",
         "--property=Id,MemoryCurrent,MemoryMax,ControlGroup"],
        capture_output=True, text=True, check=True,
    )
    for block in result.stdout.strip().split("\n\n"):
        data = dict(line.split("=", 1) for line in block.splitlines() if "=" in line)
        if not data.get("Id", "").startswith("mhfe-proof-audit-"):
            continue
        if only_unit is not None and data["Id"] != only_unit:
            continue
        if not data.get("MemoryMax", "").isdigit():
            continue
        current, old = int(data["MemoryCurrent"]), int(data["MemoryMax"])
        group = Path("/sys/fs/cgroup") / data["ControlGroup"].lstrip("/")
        try:
            stat = dict(line.split() for line in (group / "memory.stat").read_text().splitlines())
            events = dict(line.split() for line in (group / "memory.events").read_text().splitlines())
        except FileNotFoundError:
            continue
        if current < old * 85 // 100 or int(stat["file"]) < current // 2 or int(events["max"]) == 0:
            continue
        memory = {line.split(":", 1)[0]: int(line.split()[1]) * 1024
                  for line in Path("/proc/meminfo").read_text().splitlines()
                  if line.startswith(("MemTotal:", "MemAvailable:"))}
        reserve = (memory["MemTotal"] + 19) // 20
        # Existing mapped/cache charges are already present, not new private allocation.
        # Only the increment consumes the newly admitted machine-wide headroom.
        desired = min(4 * 1024**3, current + memory["MemAvailable"] - reserve - 256 * 1024**2)
        desired = desired // 1024**2 * 1024**2
        if desired <= old + 128 * 1024**2:
            continue
        update = subprocess.run(["systemctl", "--user", "set-property", "--runtime",
                                 data["Id"], f"MemoryMax={desired}"], capture_output=True, text=True)
        record = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "unit": data["Id"], "currentBytes": current, "fileBytes": int(stat["file"]),
                  "oldLimitBytes": old, "newLimitBytes": desired,
                  "availableBytes": memory["MemAvailable"], "reserveBytes": reserve,
                  "exitCode": update.returncode}
        with (evidence / "memory-adjustments.jsonl").open("a") as output:
            output.write(json.dumps(record) + "\n")
        print(json.dumps(record), flush=True)


def main():
    """Watch the original recorded source phase until its completion record exists."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    while not (evidence / "fresh-source-check.command.json").exists():
        adjust_once(evidence)
        time.sleep(5)


if __name__ == "__main__":
    main()
