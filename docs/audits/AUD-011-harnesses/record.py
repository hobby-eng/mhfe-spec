#!/usr/bin/env python3
"""Record a proof-audit command and its unmodified output as local evidence."""

import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    """Run the supplied argument vector and retain its result, including failures."""
    evidence = Path(sys.argv[1]).resolve()
    name = sys.argv[2]
    command = sys.argv[3:]
    evidence.mkdir(parents=True, exist_ok=True)
    log = evidence / f"{name}.log"
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    before = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    record = {
        "command": command,
        "cwd": str(Path.cwd()),
        "startedUtc": start,
        "endedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "elapsedSeconds": round(time.monotonic() - before, 3),
        "exitCode": result.returncode,
        "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    }
    (evidence / f"{name}.command.json").write_text(
        json.dumps(record, indent=2) + "\n"
    )
    print(json.dumps({"name": name, **record}), flush=True)
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
