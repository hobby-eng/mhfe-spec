#!/usr/bin/env python3
"""Expose the existing bounded EasyCrypt runner to the package's synthetic self-test."""

import os
from pathlib import Path
import sys
import uuid


def main():
    """Keep the system-wide reserve while using the installed runner and toolchain unchanged."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "AUD-012-harnesses"))
    from check_lean import guarded

    binary = Path(os.environ["MHFE_AUDIT_EC_BINARY"]).resolve()
    evidence = Path(os.environ["MHFE_AUDIT_EVIDENCE"]).resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    args = list(sys.argv[1:])
    if args and args[0] == "compile" and "-why3" not in args:
        args[1:1] = ["-why3", os.environ["MHFE_AUDIT_WHY3_CONFIG"]]
    env = dict(os.environ, PATH=os.environ["MHFE_AUDIT_PROVERS_BIN"] + ":" +
               str(binary.parent) + ":" + os.environ["PATH"])
    # Preserve the caller's cache options: the self-test deliberately creates a weak cache.
    code = guarded("selftest-" + uuid.uuid4().hex[:12], [str(binary), *args],
                   env, Path.cwd(), evidence)
    sys.exit(code)


if __name__ == "__main__":
    main()
