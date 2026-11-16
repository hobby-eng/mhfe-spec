#!/usr/bin/env python3
"""Compile existing Lean sources in place into fresh evidence, then replay their kernel terms."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid

from cache_headroom import adjust_once


def memory():
    """Use machine-wide available physical memory rather than free pages or summed RSS."""
    return {line.split(":", 1)[0]: int(line.split()[1])
            for line in Path("/proc/meminfo").read_text().splitlines()
            if line.startswith(("MemTotal:", "MemAvailable:", "SwapTotal:", "SwapFree:"))}


def temperature():
    """Apply the workspace thermal rule only to the specified laptop model."""
    if Path("/sys/class/dmi/id/board_name").read_text().strip() != "NP950QED-KA2DE":
        return 0
    values = []
    for zone in Path("/sys/class/thermal").glob("thermal_zone*"):
        if (zone / "type").read_text().strip() in {"acpitz", "TCPU", "x86_pkg_temp"}:
            values.append(int((zone / "temp").read_text()))
    return max(values, default=0)


def guarded(name, command, env, cwd, evidence):
    """Admit one bounded job and retain exact command metadata through AUD-011's recorder."""
    while True:
        state = memory()
        reserve = (state["MemTotal"] + 19) // 20
        cap = min(4 * 1024, (state["MemAvailable"] - reserve - 256 * 1024) // 1024)
        if cap >= 768 and temperature() < 90000:
            break
        time.sleep(5)
    jobs = max(1, min(os.cpu_count() or 1, cap // 768))
    command = [part.replace("{JOBS}", str(jobs)) for part in command]
    unit = "mhfe-proof-audit-" + uuid.uuid4().hex[:12]
    scope = ["systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}",
             "-p", f"MemoryMax={cap}M", "-p", "MemorySwapMax=0", *command]
    recorder = Path(__file__).resolve().parents[1] / "AUD-011-harnesses/record.py"
    process = subprocess.Popen([sys.executable, str(recorder), str(evidence), name, *scope],
                               cwd=cwd, env=env)
    stopped, frozen = False, False
    with (evidence / "resources.jsonl").open("a") as samples:
        while process.poll() is None:
            current = memory()
            samples.write(json.dumps({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                      "job": name, "capMiB": cap, "jobs": jobs, **current}) + "\n")
            samples.flush()
            adjust_once(evidence, unit + ".scope")
            temp = temperature()
            if current["MemAvailable"] < reserve:
                subprocess.run(["systemctl", "--user", "thaw", unit + ".scope"], capture_output=True)
                subprocess.run(["systemctl", "--user", "stop", unit + ".scope"], capture_output=True)
                stopped = True
            elif not frozen and temp >= 90000:
                subprocess.run(["systemctl", "--user", "freeze", unit + ".scope"], check=True)
                frozen = True
            elif frozen and temp <= 85000:
                subprocess.run(["systemctl", "--user", "thaw", unit + ".scope"], check=True)
                frozen = False
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
    if stopped:
        raise RuntimeError("Resource recovery required; this is not a proof failure")
    return process.returncode


def module_order(project):
    """Topologically order all chapter sources and the actual package entry point."""
    sources = {"MhfeLean.Chapters." + path.stem: path for path in
               (project / "MhfeLean/Chapters").glob("*.lean")}
    sources["MhfeLean"] = project / "MhfeLean.lean"
    imports = {name: re.findall(r"^import\s+(MhfeLean(?:\.\w+)*)", path.read_text(), re.M)
               for name, path in sources.items()}
    result, active, seen = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in active:
            raise RuntimeError("Cyclic local imports: " + name)
        active.add(name)
        for dependency in imports[name]:
            visit(dependency)
        active.remove(name)
        seen.add(name)
        result.append(name)

    for name in sorted(sources):
        visit(name)
    return sources, result


def main():
    """Run one complete source or kernel phase without using old local proof outputs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["compile", "kernel", "kernel_batch", "lake", "probes"])
    parser.add_argument("project", type=Path)
    parser.add_argument("toolchain", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    project, toolchain, evidence = (p.resolve() for p in
                                   [args.project, args.toolchain, args.evidence])
    evidence.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(toolchain / "bin") + ":" + os.environ["PATH"])
    libraries = subprocess.check_output([str(toolchain / "bin/lake"), "env", "printenv", "LEAN_PATH"],
                                        cwd=project, env=env, text=True).strip().split(":")
    original = (project / ".lake/build/lib/lean").resolve()
    libraries = [path for path in libraries if Path(path).resolve() != original]
    fresh = evidence / "freshlib"
    env["LEAN_PATH"] = ":".join([str(fresh), *libraries])
    (evidence / "effective-paths.json").write_text(json.dumps(
        {"fresh": str(fresh), "externalLibraries": libraries, "excludedOldBuild": str(original)}, indent=2) + "\n")
    if args.phase == "lake":
        return guarded("lake-build", [str(toolchain / "bin/lake"), "--no-cache", "build"], env, project, evidence)
    if args.phase in {"kernel", "kernel_batch"}:
        _, order = module_order(project)
        source = json.loads((evidence / "compile-summary.json").read_text())
        assert len(source) == len(order) == 40 and all(item["exitCode"] == 0 for item in source)
        prior_path = evidence / "kernel-summary.json"
        prior = json.loads(prior_path.read_text()) if prior_path.exists() else []
        archive = evidence / "kernel-interrupted-summary.json"
        if any(item["exitCode"] != 0 for item in prior) and not archive.exists():
            archive.write_text(json.dumps(prior, indent=2) + "\n")
        accepted = [item for item in prior if item["exitCode"] == 0]
        completed = {item["module"] for item in accepted}
        remaining = [name for name in order if name not in completed]
        template = (Path(__file__).resolve().parent / "SequentialReplay.lean").read_text()
        driver = evidence / "kernel-exact-replay.lean"
        driver.write_text(template + "\n#eval MhfeAudit.replay [" +
                          ", ".join("`" + name for name in remaining) + "]\n")
        command = [str(toolchain / "bin/lean"), "-j{JOBS}", "--root=" + str(evidence), str(driver)]
        code = guarded("kernel-exact-batch", command, env, evidence, evidence)
        log = (evidence / "kernel-exact-batch.log").read_text()
        observed = re.findall(r"^REPLAY_OK\|(.+)$", log, re.M)
        (evidence / "kernel-batch-manifest.json").write_text(json.dumps(
            {"completedCli": sorted(completed), "requested": remaining, "observed": observed,
             "driverSha256": hashlib.sha256(driver.read_bytes()).hexdigest(),
             "exitCode": code}, indent=2) + "\n")
        if code != 0 or observed != remaining:
            return code or 1
        summary = accepted + [{"module": name, "exitCode": 0, "record": "kernel-exact-batch"}
                              for name in remaining]
        assert {item["module"] for item in summary} == set(order)
        prior_path.write_text(json.dumps(summary, indent=2) + "\n")
        return 0
    if args.phase == "probes":
        probes = Path(__file__).resolve().parent / "probes"
        results = []
        for name, marker in [("AxiomControl", "AuditAxiom"), ("SorryControl", "sorryAx"),
                             ("NativeControl", "_native")]:
            label = "probe-" + name
            command = [str(toolchain / "bin/lean"), "-j{JOBS}", "--root=" + str(probes),
                       str(probes / (name + ".lean"))]
            code = guarded(label, command, env, evidence, evidence)
            log = (evidence / (label + ".log")).read_text()
            rejected = ("Unexpected proof axioms" in log or "Local axioms are forbidden" in log)
            results.append({"name": name, "exitCode": code, "gateRejected": rejected,
                            "markerFound": marker in log})
        (evidence / "probe-summary.json").write_text(json.dumps(results, indent=2) + "\n")
        return int(not all(item["exitCode"] == 1 and item["gateRejected"] and item["markerFound"]
                           for item in results))
    sources, order = module_order(project)
    summary = []
    for name in order:
        output = fresh / (name.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(toolchain / "bin/lean"), "-j{JOBS}", "--root=" + str(project),
                   "-o", str(output), str(sources[name])]
        label = args.phase + "-" + name
        code = guarded(label, command, env, evidence, evidence)
        summary.append({"module": name, "exitCode": code})
        (evidence / (args.phase + "-summary.json")).write_text(json.dumps(summary, indent=2) + "\n")
        if code:
            return code
    return 0


if __name__ == "__main__":
    sys.exit(main())
