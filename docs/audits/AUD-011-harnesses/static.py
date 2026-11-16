#!/usr/bin/env python3
"""Inventory EasyCrypt proof sources and reproduce the README verifier exit defect."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def uncomment(text):
    """Remove nested EasyCrypt comments while preserving line numbers."""
    result, depth, index = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "(*":
            depth += 1
            result.append("  ")
            index += 2
        elif pair == "*)" and depth:
            depth -= 1
            result.append("  ")
            index += 2
        else:
            result.append(text[index] if not depth or text[index] == "\n" else " ")
            index += 1
    assert depth == 0, "Unclosed source comment"
    return "".join(result)


def main():
    """Fail when source integrity or strictness checks fail; retain the known README defect."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    files, axioms, forbidden = [], [], []
    for source in sorted((args.proof / "src").glob("*.ec")):
        original = source.read_text()
        clean = uncomment(original)
        lemmas = len(re.findall(r"^\s*(?:(?:local|abstract)\s+)?lemma\s", clean, re.M))
        for line, content in enumerate(clean.splitlines(), 1):
            match = re.match(r"\s*(declare\s+)?axiom\s+(\w+)", content)
            if match:
                axioms.append({"file": source.name, "line": line,
                               "name": match[2], "sectionHypothesis": bool(match[1])})
            if re.search(r"\b(?:admit|abort)\b|^\s*pragma\s", content):
                forbidden.append({"file": source.name, "line": line, "text": content})
        files.append({"file": source.name, "lines": len(original.splitlines()),
                      "lemmas": lemmas, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
    checksum = subprocess.run(
        ["sha256sum", "-c", "../SHA256SUMS"], cwd=args.proof / "src",
        capture_output=True, text=True,
    )
    command = (
        'easycrypt() { return 7; }; '
        'for f in First.ec Second.ec; do easycrypt compile -no-eco -I . "$f" '
        '|| { echo "FAILED: $f"; break; }; done'
    )
    broken = subprocess.run(["bash", "-c", command], capture_output=True, text=True)
    corrected = subprocess.run(
        ["bash", "-c", command.replace("break;", "exit 1;")],
        capture_output=True, text=True,
    )
    record = {"files": files, "axioms": axioms, "forbidden": forbidden,
              "checksum": {"exitCode": checksum.returncode, "stdout": checksum.stdout,
                           "stderr": checksum.stderr},
              "readmeLoop": {"command": command, "exitCode": broken.returncode,
                             "stdout": broken.stdout, "correctedExitCode": corrected.returncode}}
    args.evidence.mkdir(parents=True, exist_ok=True)
    (args.evidence / "static-inventory.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"files": len(files), "lines": sum(x["lines"] for x in files),
                      "lemmas": sum(x["lemmas"] for x in files), "directAxioms": len(axioms),
                      "sectionHypotheses": sum(x["sectionHypothesis"] for x in axioms),
                      "forbidden": forbidden, "checksumExit": checksum.returncode,
                      "readmeFailureExit": broken.returncode,
                      "correctedFailureExit": corrected.returncode}, indent=2))
    assert len(files) == 18 and not forbidden
    assert checksum.returncode == 0
    assert broken.returncode == 0 and "FAILED: First.ec" in broken.stdout
    assert corrected.returncode == 1


if __name__ == "__main__":
    main()
