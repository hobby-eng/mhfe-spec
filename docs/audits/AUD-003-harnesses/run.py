"""Runs one audit command and retains its evidence.

Usage: python3 run.py <name> <working-directory> -- <command ...>

Writes <name>.log (combined stdout and stderr) and <name>.command.json (exact command, working
directory relative to the workspace, UTC start and end, exit code, SHA-256 of the log) next to
this harnesses/ folder. User home paths are replaced by /home/user in the retained files.
"""

import datetime
import hashlib
import json
import os
import subprocess
import sys

EVIDENCE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HOME = os.path.expanduser("~")


def scrub(text):
    return text.replace(HOME, "/home/user")


def main():
    name, workdir = sys.argv[1], sys.argv[2]
    command = sys.argv[sys.argv.index("--") + 1 :]
    start = datetime.datetime.now(datetime.timezone.utc)
    result = subprocess.run(command, cwd=workdir, capture_output=True, text=True)
    end = datetime.datetime.now(datetime.timezone.utc)
    log = scrub(result.stdout + result.stderr)
    log_path = os.path.join(EVIDENCE, f"{name}.log")
    with open(log_path, "w") as handle:
        handle.write(log)
    record = {
        "name": name,
        "command": scrub(" ".join(command)),
        "workingDirectory": scrub(os.path.abspath(workdir)),
        "startUtc": start.isoformat(timespec="seconds"),
        "endUtc": end.isoformat(timespec="seconds"),
        "exitCode": result.returncode,
        "logSha256": hashlib.sha256(log.encode()).hexdigest(),
    }
    with open(os.path.join(EVIDENCE, f"{name}.command.json"), "w") as handle:
        json.dump(record, handle, indent=2)
        handle.write("\n")
    print(log, end="")
    print(f"[{name}] exit {result.returncode}")


if __name__ == "__main__":
    main()
