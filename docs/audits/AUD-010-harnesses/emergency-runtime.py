"""Run the new emergency CLIs on two public default-cost fixtures, sequentially.

Run through record.py from the repository root. No cryptographic parameters are
reduced. Each child has a 2.75 GiB address-space cap; at least 6.75 GiB must be available
before it starts. This is a focused CLI integration check, not a full vector replay.
"""

import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = (
    (3, "vectors/suite3/zero-12.json"),
    (4, "vectors/suite4/same-length-nonzero-12.json"),
)


def memory_limit():
    limit = 11 * 1024**3 // 4
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def run(command, lines):
    available = next(int(line.split()[1]) * 1024 for line in
                     Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    if available < 27 * 1024**3 // 4:
        raise RuntimeError(f"need 6.75 GiB available before the next child; have {available} bytes")
    started = time.monotonic()
    child = subprocess.run(
        command, input="\n".join(lines) + "\n", text=True, cwd=ROOT,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        capture_output=True, timeout=900, preexec_fn=memory_limit,
    )
    print(json.dumps({"command": command, "exitCode": child.returncode,
                      "elapsedSeconds": round(time.monotonic() - started, 3),
                      "stdout": child.stdout, "stderr": child.stderr}), flush=True)
    if child.returncode:
        raise RuntimeError("emergency command failed")
    return child.stdout


def main():
    selected = set(sys.argv[1:]) or {"3-encrypt", "3-decrypt", "4-encrypt", "4-decrypt"}
    allowed = {"3-encrypt", "3-decrypt", "4-encrypt", "4-decrypt"}
    if not selected <= allowed:
        raise SystemExit("optional operations: 3-encrypt 3-decrypt 4-encrypt 4-decrypt")
    for suite, fixture in FIXTURES:
        vector = json.loads((ROOT / fixture).read_text())
        source = vector["inputs"]["phrase"]
        password = vector["inputs"]["password"]
        container = vector["container"]
        script = f"scripts/independent-suite{suite}.py"
        if f"{suite}-encrypt" in selected:
            output = run([sys.executable, "-B", script, "encrypt"],
                         [source, password, password])
            if container not in output.splitlines():
                raise AssertionError("container differs from the public fixture")
        # Exercise four-letter expansion and case conversion, without changing
        # the passwords. Suite 3's explicit source-length argument is also new.
        abbreviated = " ".join(word[:4].upper() for word in container.split())
        command = [sys.executable, "-B", script, "decrypt"]
        if suite == 3:
            command.append("12")
        if f"{suite}-decrypt" in selected:
            output = run(command, [abbreviated, password])
            expected = (f"12 words, verified: {source}" if suite == 3 else
                        f"not verified, compare a known address: {source}")
            if output.splitlines() != [expected]:
                raise AssertionError("recovered phrase differs from the public fixture")
        print(f"PASS suite {suite}: selected default-cost operations {sorted(selected)}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
