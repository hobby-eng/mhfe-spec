#!/usr/bin/env python3
"""Reproduce existing textual port comparison and exercise its parser limits."""

import argparse
import collections
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parents[3]
HERE = None
REVIEW = None
RECORDS = []


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, args, allowed=(0,)):
    started = datetime.datetime.now(datetime.timezone.utc)
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    ended = datetime.datetime.now(datetime.timezone.utc)
    log = HERE / (label + ".log")
    log.write_text(result.stdout + result.stderr)
    record = {"label": label, "command": args, "cwd": str(ROOT), "exitCode": result.returncode,
              "startedUtc": started.isoformat(), "endedUtc": ended.isoformat(),
              "elapsedSeconds": round((ended-started).total_seconds(), 6), "logSha256": digest(log)}
    RECORDS.append(record)
    (HERE / (label + ".command.json")).write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode not in allowed:
        raise RuntimeError(result.stderr)
    print(label + ": " + ("difference recorded" if label.startswith("gnu-") else result.stdout.strip()))
    return result.stdout


def functions():
    source = (REVIEW / "tools/decls.py").read_text()
    prefix = source.split("d, out = sys.argv[1], sys.argv[2]\n")[0]
    namespace = {}
    exec(compile(prefix, str(REVIEW / "tools/decls.py"), "exec"), namespace)
    return namespace


def comparison(old, new):
    def grouped(rows):
        result = collections.OrderedDict()
        for row in rows:
            result.setdefault(row[0], []).append(row)
        return result
    left, right = grouped(old), grouped(new)
    counts = collections.Counter()
    for key, rows in left.items():
        if key not in right:
            counts["removed"] += 1
        elif [(row[3], row[1]) for row in rows] == [(row[3], row[1]) for row in right[key]]:
            counts["same"] += 1
        else:
            counts["changed"] += 1
    counts["added"] = sum(key not in left for key in right)
    return dict(counts)


def main():
    global HERE, REVIEW
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("review", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    REVIEW, HERE = args.review.resolve(), args.evidence.resolve()
    HERE.mkdir(parents=True, exist_ok=True)
    for label, directory in [("snapshot", "snapshot"), ("port", "port-v4.35")]:
        run(label, [sys.executable, str(REVIEW / "tools/decls.py"),
                    str(REVIEW / directory), str(HERE / (label + ".tsv"))])
    run("diff", [sys.executable, str(REVIEW / "tools/decldiff.py"),
                 str(HERE / "snapshot.tsv"), str(HERE / "port.tsv"), str(HERE / "diff.tsv")])
    original = REVIEW / "out-v4.35/decls"
    equality = {name: (HERE / name).read_bytes() == (original / name).read_bytes()
                for name in ["snapshot.tsv", "port.tsv", "diff.tsv"]}
    assert all(equality.values()), equality
    print("retained_outputs_equal", equality)
    api = functions()
    pairs = {
        "named_argument_regression": (
            "namespace Demo\ndef ident {N : Nat} (x : Fin N) := x\ntheorem fixed (N : Nat) (x : Fin N) : ident (N := N) x = x := rfl\nend Demo\n",
            "namespace Demo\ndef ident {N : Nat} (x : Fin N) := x\ntheorem fixed (N : Nat) (x : Fin N) : ident (N := N) x = ident x := rfl\nend Demo\n"),
        "context_type": (
            "namespace Demo\nvariable (n : Nat)\ntheorem reflexive : n = n := rfl\nend Demo\n",
            "namespace Demo\nvariable (n : Int)\ntheorem reflexive : n = n := rfl\nend Demo\n"),
        "explicit_definition_body": (
            "namespace Demo\ndef rounds : Nat := 11\nend Demo\n",
            "namespace Demo\ndef rounds : Nat := 12\nend Demo\n"),
        "inferred_definition_type": (
            "namespace Demo\ndef value := (1 : Nat)\nend Demo\n",
            "namespace Demo\ndef value := True\nend Demo\n"),
        "structure_field": (
            "namespace Demo\nstructure Box where\n  value : Nat\nend Demo\n",
            "namespace Demo\nstructure Box where\n  value : Int\nend Demo\n"),
        "later_equation_clause": (
            "namespace Demo\ndef choose : Bool → Nat\n  | true => 1\n  | false => 0\nend Demo\n",
            "namespace Demo\ndef choose : Bool → Nat\n  | true => 1\n  | false => 2\nend Demo\n"),
        "string_assignment_token": (
            'namespace Demo\ntheorem literal : "x:=alpha" = "x:=alpha" := rfl\nend Demo\n',
            'namespace Demo\ntheorem literal : "x:=beta" = "x:=beta" := rfl\nend Demo\n'),
        "string_whitespace": (
            'namespace Demo\ntheorem literal : "a b" = "a b" := rfl\nend Demo\n',
            'namespace Demo\ntheorem literal : "a  b" = "a  b" := rfl\nend Demo\n'),
        "string_comment_token": (
            'namespace Demo\ndef marker : String := "ordinary"\ntheorem kept : True := True.intro\nend Demo\n',
            'namespace Demo\ndef marker : String := "/-"\ntheorem kept : True := True.intro\nend Demo\n'),
        "attribute": (
            "namespace Demo\ndef value : Nat := 1\nend Demo\n",
            "namespace Demo\n@[reducible] def value : Nat := 1\nend Demo\n"),
        "named_instance": (
            "namespace Demo\ninstance named : Inhabited Nat := inferInstance\nend Demo\n",
            "namespace Demo\ninstance named : Inhabited Int := inferInstance\nend Demo\n"),
        "unnamed_namespace_end": (
            "namespace A\ntheorem first : True := True.intro\nend\nnamespace B\ntheorem second : True := True.intro\nend\n",
            "namespace A\ntheorem first : True := True.intro\nend A\nnamespace B\ntheorem second : True := True.intro\nend B\n"),
    }
    results = []
    for label, texts in pairs.items():
        parsed = []
        for side, text in zip(["old", "new"], texts):
            path = HERE / (label + "-" + side + ".lean")
            path.write_text(text)
            parsed.append(api["parse"](str(path)))
        entry = {"case": label, "comparison": comparison(*parsed),
                 "oldRows": parsed[0], "newRows": parsed[1]}
        for side, rows in zip(["old", "new"], parsed):
            (HERE / (label + "-" + side + ".tsv")).write_text(
                "".join("\t".join(str(value) for value in row) + "\n" for row in rows))
        run("probe-diff-" + label,
            [sys.executable, str(REVIEW / "tools/decldiff.py"),
             str(HERE / (label + "-old.tsv")), str(HERE / (label + "-new.tsv")),
             str(HERE / (label + "-diff.tsv"))])
        entry["actualDecldiffOutput"] = (HERE / ("probe-diff-" + label + ".log")).read_text().strip()
        if label == "named_argument_regression":
            entry["oldFirstAssignmentPrefixesEqual"] = (
                texts[0].split("theorem fixed", 1)[1].split(":=", 1)[0] ==
                texts[1].split("theorem fixed", 1)[1].split(":=", 1)[0])
        results.append(entry)
        print("probe", label, entry["comparison"])
    (HERE / "parser-probes.json").write_text(json.dumps(results, indent=2) + "\n")
    totals = {"additions": 0, "deletions": 0, "changedFiles": 0}
    old_dir = REVIEW / "snapshot/MhfeLean/Chapters"
    new_dir = REVIEW / "port-v4.35/MhfeLean/Chapters"
    for name in sorted({p.name for p in old_dir.glob("*.lean")} | {p.name for p in new_dir.glob("*.lean")}):
        old, new = old_dir / name, new_dir / name
        output = run("gnu-" + name[:-5], ["diff", "-u", str(old) if old.exists() else "/dev/null",
                     str(new) if new.exists() else "/dev/null"], (0, 1))
        if output:
            totals["changedFiles"] += 1
        totals["additions"] += sum(line.startswith("+") and not line.startswith("+++") for line in output.splitlines())
        totals["deletions"] += sum(line.startswith("-") and not line.startswith("---") for line in output.splitlines())
    assert totals == {"additions": 661, "deletions": 384, "changedFiles": 37}, totals
    (HERE / "gnu-diff-stats.json").write_text(json.dumps(totals, indent=2) + "\n")
    inputs = [REVIEW / "tools/decls.py", REVIEW / "tools/decldiff.py", REVIEW / "PORT-v4.35.md"]
    inputs += sorted((REVIEW / "out-v4.35/decls").glob("*.tsv"))
    (HERE / "commands.json").write_text(json.dumps(RECORDS, indent=2) + "\n")
    (HERE / "input-hashes.json").write_text(json.dumps(
        {str(path.relative_to(ROOT)): digest(path) for path in inputs}, indent=2) + "\n")


if __name__ == "__main__":
    main()
