"""Run retained specification checks and fail if any reported check fails.

Use only public wordlists and test vectors. The audit harnesses are immutable evidence;
this runner checks their result lists instead of trusting their original exit status.
"""

import argparse
import os
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parent.parent
HARNESSES = ROOT / "docs" / "audits" / "AUD-003-harnesses"
CHECKS = {
    "documents": "document_checks.py",
    "analysis": "addendum_checks.py",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=CHECKS)
    parser.add_argument("wordlist", type=Path, help="public BIP39 English wordlist in Rust source form")
    parser.add_argument("vector", type=Path, nargs="?", help="public suite 3 zero-12.json (analysis only)")
    args = parser.parse_args()
    if (args.check == "analysis") != (args.vector is not None):
        parser.error("analysis requires a vector; documents accepts only the wordlist")

    # Resolve inputs before entering the repository: the retained harnesses use relative paths.
    inputs = [args.wordlist.resolve()]
    if args.vector is not None:
        inputs.append(args.vector.resolve())
    for path in inputs:
        if not path.is_file():
            parser.error(f"input file does not exist: {path}")

    harness = HARNESSES / CHECKS[args.check]
    previous_directory, previous_argv = Path.cwd(), sys.argv
    previous_bytecode_setting = sys.dont_write_bytecode
    try:
        os.chdir(ROOT)
        sys.argv = [str(harness), *(str(path) for path in inputs)]
        sys.dont_write_bytecode = True
        namespace = runpy.run_path(str(harness), run_name="__main__")
    finally:
        os.chdir(previous_directory)
        sys.argv = previous_argv
        sys.dont_write_bytecode = previous_bytecode_setting

    # An absent, empty or malformed result list must not silently count as a passing run.
    results = namespace.get("results")
    if not isinstance(results, list) or not results or any(type(value) is not bool for value in results):
        print("ERROR: the harness did not return a non-empty list of boolean results", file=sys.stderr)
        return 1
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
