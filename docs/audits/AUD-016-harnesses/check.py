#!/usr/bin/env python3
"""Freshly check the current Lean graph and strict EasyCrypt package with recorded bounded jobs."""

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
WORKSPACE = HERE.parents[3]
spec = importlib.util.spec_from_file_location("guard", AUDITS / "AUD-014-harnesses/check_lean.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


def stable(evidence):
    for row in json.loads((evidence / "snapshot.json").read_text())["files"]:
        assert hashlib.sha256((WORKSPACE / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]


def graph(project):
    sources = {"MhfeLean.Chapters." + p.stem: p for p in (project / "MhfeLean/Chapters").glob("*.lean")}
    sources["MhfeLean"] = project / "MhfeLean.lean"
    deps = {name: [m for m in re.findall(r"^(?:public\s+)?import\s+(\S+)", p.read_text(), re.M)
                   if m in sources] for name, p in sources.items()}
    order, seen, active = [], set(), set()
    def visit(name):
        if name in seen:
            return
        assert name not in active, name
        active.add(name)
        for dep in deps[name]:
            visit(dep)
        active.remove(name)
        seen.add(name)
        order.append(name)
    for name in sorted(sources):
        visit(name)
    return sources, deps, order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["lean", "kernel", "ec", "ec-controls", "lean-controls", "inventory"])
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--shares", type=int, default=3)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    stable(evidence)
    env = dict(os.environ)
    project = WORKSPACE / "tmp/lean-review-2026-11-11/port-v4.35"
    toolchain = WORKSPACE / "workingspace/lean/lean-4.35.0-linux"
    ec = WORKSPACE / "tmp/easycrypt-mhfe-2026-11-09"
    binary = WORKSPACE / "workingspace/opam-easycrypt/mhfe-easycrypt-main/bin/easycrypt"
    why3 = WORKSPACE / "workingspace/easycrypt-provers/why3-main.conf"
    def run(label, command, cwd=evidence, custom_env=env):
        return guard.guarded(label, command, custom_env, cwd, evidence, shares=args.shares)
    if args.phase in {"ec", "ec-controls"}:
        env["PATH"] = str(WORKSPACE / "workingspace/easycrypt-provers/bin-main") + ":" + str(binary.parent) + ":" + env["PATH"]
        assert not list((ec / "src").glob("*.eco")), "Cached EC proofs are forbidden"
        if args.phase == "ec-controls":
            return run("ec-checker-selftest", ["unshare", "-rn", "bash", str(ec / "check-selftest.sh"), "-why3", str(why3)],
                       ec, dict(env, EASYCRYPT=str(binary)))
        prior_path = evidence / "ec-summary.json"
        prior = json.loads(prior_path.read_text()) if prior_path.exists() else []
        if prior:
            attempt = 1
            archive = evidence / "ec-initial-summary.json"
            while archive.exists():
                attempt += 1
                archive = evidence / ("ec-attempt-" + str(attempt) + "-summary.json")
            archive.write_text(json.dumps(prior, indent=2) + "\n")
        results = [row for row in prior if row["exitCode"] == 0]
        completed = {row["file"] for row in results}
        for path in sorted((ec / "src").glob("*.ec")):
            if path.name in completed:
                continue
            assert not re.search(r"\b(?:admit|admitted)\b|Proofs:weak", path.read_text())
            label = ("ec-resume-" if any(r["file"] == path.name for r in prior) else "ec-") + path.stem
            retry = 1
            while (evidence / (label + ".command.json")).exists():
                retry += 1
                label = "ec-retry" + str(retry) + "-" + path.stem
            status = run(label, [str(binary), "compile", "-no-eco", "-why3", str(why3), "-I", str(ec / "src"), str(path)])
            results.append({"file": path.name, "exitCode": status})
            (evidence / "ec-summary.json").write_text(json.dumps(results, indent=2) + "\n")
            if status:
                return status
        assert len(results) == 23 and not list((ec / "src").glob("*.eco"))
        stable(evidence)
        return 0
    env["PATH"] = str(toolchain / "bin") + ":" + env["PATH"]
    result = subprocess.run([str(toolchain / "bin/lake"), "--no-cache", "env", "printenv", "LEAN_PATH"],
                            cwd=project, env=env, capture_output=True, text=True, check=True)
    (evidence / ("lake-path-" + args.phase + ".log")).write_text(result.stderr)
    old = (project / ".lake/build/lib/lean").resolve()
    libraries = [(project / p).resolve() for p in result.stdout.strip().split(":")]
    env["LEAN_PATH"] = ":".join([str(evidence / "freshlib"), *(str(p) for p in libraries if p != old)])
    sources, deps, order = graph(project)
    value = {"order": order, "dependencies": deps, "leanPath": env["LEAN_PATH"], "excludedOldBuild": str(old)}
    graph_path = evidence / "module-graph.json"
    if graph_path.exists():
        assert json.loads(graph_path.read_text()) == value
    else:
        graph_path.write_text(json.dumps(value, indent=2) + "\n")
    assert len(order) == 42
    if args.phase == "lean":
        assert not (evidence / "lean-summary.json").exists(), "Use a new output for a new run"
        done, running, results = set(), {}, []
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            while len(done) != len(order):
                for name in order:
                    if name in done or name in running.values() or len(running) >= 2 or not set(deps[name]) <= done:
                        continue
                    output = evidence / "freshlib" / (name.replace(".", "/") + ".olean")
                    output.parent.mkdir(parents=True, exist_ok=True)
                    command = [str(toolchain / "bin/lean"), "-j{JOBS}", "--root=" + str(project), "-o", str(output), str(sources[name])]
                    running[pool.submit(run, "lean-" + name, command)] = name
                assert running, "No ready graph node"
                finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                failure = 0
                for job in finished:
                    name = running.pop(job)
                    status = job.result()
                    results.append({"module": name, "exitCode": status})
                    if status == 0:
                        done.add(name)
                    else:
                        failure = status
                (evidence / "lean-summary.json").write_text(json.dumps(results, indent=2) + "\n")
                if failure:
                    for job, name in running.items():
                        results.append({"module": name, "exitCode": job.result()})
                    (evidence / "lean-summary.json").write_text(json.dumps(results, indent=2) + "\n")
                    return failure
        stable(evidence)
        return 0
    compiled = json.loads((evidence / "lean-summary.json").read_text())
    assert len(compiled) == 42 and all(r["exitCode"] == 0 for r in compiled)
    if args.phase == "kernel":
        adapter = (AUDITS / "AUD-012-harnesses/SequentialReplay.lean").read_text()
        driver = evidence / "kernel-replay.lean"
        driver.write_text(adapter + "\n#eval MhfeAudit.replay [" + ", ".join("`" + n for n in order) + "]\n")
        status = run("kernel-exact", [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)])
        observed = re.findall(r"^REPLAY_OK\|(.+)$", (evidence / "kernel-exact.log").read_text(), re.M)
        (evidence / "kernel-summary.json").write_text(json.dumps({"requested": order, "observed": observed, "exitCode": status}, indent=2) + "\n")
        return status or int(observed != order)
    if args.phase == "lean-controls":
        template = (HERE / "Inventory.lean").read_text()
        results = []
        for label, decl, marker in [("UnusedAxiom", "axiom AuditUnused : True", "AuditUnused"),
                                   ("Sorry", "theorem AuditSorry : False := by sorry", "sorryAx"),
                                   ("Native", "theorem AuditNative : (2 : Nat) + 2 = 4 := by native_decide", "_native")]:
            driver = evidence / ("Control" + label + ".lean")
            driver.write_text(template.replace("namespace TrialAudit", "namespace MhfeLean\n" + decl + "\nend MhfeLean\nnamespace TrialAudit", 1))
            status = run("control-" + label, [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)])
            log = (evidence / ("control-" + label + ".log")).read_text()
            results.append({"name": label, "exitCode": status, "markerFound": marker in log,
                            "gateRejected": "Local axioms" in log or "Unexpected proof axioms" in log})
        (evidence / "control-summary.json").write_text(json.dumps(results, indent=2) + "\n")
        return int(not all(r["exitCode"] == 1 and r["markerFound"] and r["gateRejected"] for r in results))
    driver = HERE / "Inventory.lean"
    return run("full-inventory", [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)])


if __name__ == "__main__":
    sys.exit(main())
