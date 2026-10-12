"""Replay published Suite 3/archived Suite 2 equations with recorded Argon2 keys."""

import argparse
import json
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wordlist", type=Path)
    args = parser.parse_args()
    old = runpy.run_path(str(ROOT / "docs/audits/AUD-003-harnesses/notation_check.py"))
    words = old["load_wordlist"](args.wordlist)
    counts = {}
    for directory, schema, function in (
        ("vectors/suite3", "mhfe-suite-3-vector-v2", "check_suite3"),
        ("vectors/archive/suite-2", None, "check_suite2"),
    ):
        count = 0
        for path in sorted((ROOT / directory).glob("*.json")):
            if path.name in ("negative-cases.json", "validation-cases.json"):
                continue
            data = json.loads(path.read_text())
            if schema is not None and data.get("schema") != schema:
                raise AssertionError("unexpected positive transcript schema: " + path.name)
            old[function](path, words)
            count += 1
        counts[directory] = count
    if counts != {"vectors/suite3": 17, "vectors/archive/suite-2": 9}:
        raise AssertionError("unexpected positive transcript inventory")
    print(json.dumps({"outcome": "passed", "transcripts": counts, "argon2Calls": 0,
                      "limitation": "Uses recorded keys; does not verify Argon2 outputs."}))


if __name__ == "__main__":
    main()
