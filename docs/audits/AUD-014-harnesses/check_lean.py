#!/usr/bin/env python3
"""Freshly elaborate the active code-proof import graph and replay its exact kernel modules."""

import argparse
import concurrent.futures
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


def memory():
    """Read machine-wide available physical memory, not free pages or summed RSS."""
    return {line.split(":", 1)[0]: int(line.split()[1])
            for line in Path("/proc/meminfo").read_text().splitlines()
            if line.startswith(("MemTotal:", "MemAvailable:", "SwapTotal:", "SwapFree:"))}


def swap_pages():
    return {line.split()[0]: int(line.split()[1])
            for line in Path("/proc/vmstat").read_text().splitlines()
            if line.startswith(("pswpin ", "pswpout "))}


def memory_stalled():
    """Page-ins of previously swapped desktop pages alone are not new swap pressure."""
    fields = Path("/proc/pressure/memory").read_text().splitlines()
    return any(float(line.split()[1].split("=", 1)[1]) > 0 for line in fields)


def temperature():
    """Apply the special thermal rule only to its named board model."""
    if Path("/sys/class/dmi/id/board_name").read_text().strip() != "NP950QED-KA2DE":
        return 0
    return max((int((zone / "temp").read_text())
                for zone in Path("/sys/class/thermal").glob("thermal_zone*")
                if (zone / "type").read_text().strip() in {"acpitz", "TCPU", "x86_pkg_temp"}), default=0)


def guarded(name, command, env, cwd, evidence, shares=1):
    """Run only this audit's bounded scope, with five-second memory/swap/thermal monitoring."""
    reserve = (memory()["MemTotal"] + 19) // 20
    while True:
        state = memory()
        cap = min(4096, (state["MemAvailable"] - reserve - 256 * 1024) // (1024 * shares))
        if cap >= 1536 and temperature() < 90000:
            break
        time.sleep(5)
    jobs = max(1, min((os.cpu_count() or 1) // shares, cap // 768))
    args = [value.replace("{JOBS}", str(jobs)) for value in command]
    unit = "mhfe-code-audit-" + uuid.uuid4().hex[:12] + ".scope"
    scope = ["systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
             "-p", f"MemoryMax={cap}M", "-p", "MemorySwapMax=0", "-p", f"CPUQuota={jobs * 100}%", *args]
    recorder = Path(__file__).resolve().parents[1] / "AUD-011-harnesses/record.py"
    process = subprocess.Popen([sys.executable, str(recorder), str(evidence), name, *scope],
                               cwd=cwd, env=env)
    previous, swapping, frozen, stopped = swap_pages(), 0, False, False
    with (evidence / (name + ".resources.jsonl")).open("a") as samples:
        while process.poll() is None:
            state, current, temp = memory(), swap_pages(), temperature()
            delta_in = current["pswpin"] - previous["pswpin"]
            delta_out = current["pswpout"] - previous["pswpout"]
            pressure = delta_out > 0 or (delta_in > 0 and memory_stalled())
            swapping = swapping + 1 if pressure else 0
            samples.write(json.dumps({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                      "job": name, "unit": unit, "capMiB": cap, "jobs": jobs,
                                      "swapInPages": delta_in, "swapOutPages": delta_out,
                                      "swapActiveSamples": swapping,
                                      "temperatureMilliC": temp, **state}) + "\n")
            samples.flush()
            previous = current
            if state["MemAvailable"] < reserve or swapping >= 3:
                subprocess.run(["systemctl", "--user", "thaw", unit], capture_output=True)
                subprocess.run(["systemctl", "--user", "stop", unit], capture_output=True)
                stopped = True
            elif not frozen and temp >= 90000:
                subprocess.run(["systemctl", "--user", "freeze", unit], check=True)
                frozen = True
            elif frozen and temp <= 85000:
                subprocess.run(["systemctl", "--user", "thaw", unit], check=True)
                frozen = False
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
    if stopped:
        (evidence / (name + ".resource-stop.json")).write_text(json.dumps(
            {"reason": "system reserve or sustained global swap activity", "unit": unit,
             "notMathematicalFailure": True}, indent=2) + "\n")
        return 75
    return process.returncode


def graph(project):
    """Select the real root's transitive local imports; raw templates are not proof inputs."""
    paths = {"MhfeCore": project / "MhfeCore.lean"}
    paths.update({"MhfeCore." + str(path.relative_to(project / "MhfeCore")).removesuffix(".lean").replace("/", "."): path
                  for path in (project / "MhfeCore").rglob("*.lean")})
    dependencies, active, order = {}, set(), []

    def visit(name):
        if name in dependencies:
            return
        if name in active:
            raise RuntimeError("Cyclic local imports: " + name)
        active.add(name)
        imports = re.findall(r"^(?:public\s+)?import\s+(\S+)", paths[name].read_text(), re.M)
        local = [value for value in imports if value in paths]
        for value in local:
            visit(value)
        active.remove(name)
        dependencies[name] = local
        order.append(name)

    visit("MhfeCore")
    return {name: paths[name] for name in order}, dependencies, order


def compile_sources(project, toolchain, evidence, env, sources, dependencies, order):
    """Build ready DAG nodes into separate fresh artifacts, at most two memory-budgeted jobs."""
    state = memory()
    workers = 2 if state["MemAvailable"] > state["MemTotal"] // 20 + 5 * 1024 * 1024 + 256 * 1024 else 1
    prior_path = evidence / "compile-summary.json"
    prior = json.loads(prior_path.read_text()) if prior_path.exists() else []
    if prior:
        snapshot = json.loads((evidence / "snapshot.json").read_text())
        workspace = Path(__file__).resolve().parent.parents[3]
        for row in snapshot["files"]:
            assert hashlib.sha256((workspace / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
        archive = evidence / "compile-interrupted-summary.json"
        if not archive.exists():
            archive.write_text(json.dumps(prior, indent=2) + "\n")
    results = [row for row in prior if row["exitCode"] == 0]
    completed, running = {row["module"] for row in results}, {}
    fresh = evidence / "freshlib"
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        while len(completed) < len(order):
            for name in order:
                if name in completed or name in running.values() or len(running) >= workers:
                    continue
                if not set(dependencies[name]) <= completed:
                    continue
                output = fresh / (name.replace(".", "/") + ".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                args = [str(toolchain / "bin/lean"), "-j{JOBS}", "--root=" + str(project),
                        "-o", str(output), str(sources[name])]
                label = ("compile-resume-" if any(row["module"] == name for row in prior) else "compile-") + name
                future = pool.submit(guarded, label, args, env, evidence, evidence, workers)
                running[future] = name
            if not running:
                raise RuntimeError("No ready DAG node")
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            failure = 0
            for future in done:
                name = running.pop(future)
                code = future.result()
                results.append({"module": name, "exitCode": code})
                if code == 0:
                    completed.add(name)
                else:
                    failure = code
                (evidence / "compile-summary.json").write_text(json.dumps(results, indent=2) + "\n")
            if failure:
                # Running independent scopes finish and retain their original results.
                for future, name in running.items():
                    results.append({"module": name, "exitCode": future.result()})
                (evidence / "compile-summary.json").write_text(json.dumps(results, indent=2) + "\n")
                return failure
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["compile", "kernel", "inventory", "controls", "witnesses", "lake"])
    parser.add_argument("project", type=Path)
    parser.add_argument("toolchain", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    project, toolchain, evidence = (p.resolve() for p in [args.project, args.toolchain, args.evidence])
    evidence.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(toolchain / "bin") + ":" + os.environ["PATH"])
    result = subprocess.run([str(toolchain / "bin/lake"), "--no-cache", "env", "printenv", "LEAN_PATH"],
                            cwd=project, env=env, capture_output=True, text=True, check=True)
    (evidence / ("lake-path-" + args.phase + "-diagnostics.log")).write_text(result.stderr)
    old = (project / ".lake/build/lib/lean").resolve()
    libraries = [(project / path).resolve() for path in result.stdout.strip().split(":")]
    libraries = [path for path in libraries if path != old]
    env["LEAN_PATH"] = ":".join([str(evidence / "freshlib"), *(str(path) for path in libraries)])
    sources, dependencies, order = graph(project)
    graph_path = evidence / "module-graph.json"
    graph_data = {"order": order, "dependencies": dependencies, "oldBuildExcluded": str(old),
                  "leanPath": env["LEAN_PATH"]}
    if graph_path.exists():
        assert json.loads(graph_path.read_text()) == graph_data
    else:
        graph_path.write_text(json.dumps(graph_data, indent=2) + "\n")
    if args.phase == "compile":
        return compile_sources(project, toolchain, evidence, env, sources, dependencies, order)
    if args.phase == "lake":
        return guarded("lake-build", ["unshare", "-rn", str(toolchain / "bin/lake"), "--no-cache", "build"], env, project, evidence)
    compilation = json.loads((evidence / "compile-summary.json").read_text())
    assert len(compilation) == len(order) and {row["module"] for row in compilation} == set(order)
    assert all(row["exitCode"] == 0 for row in compilation)
    if args.phase == "witnesses":
        driver = Path(__file__).resolve().parent / "ContractWitnesses.lean"
        return guarded("contract-witnesses", [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)], env, evidence, evidence)
    if args.phase == "kernel":
        adapter = Path(__file__).resolve().parents[1] / "AUD-012-harnesses/SequentialReplay.lean"
        driver = evidence / "exact-kernel-replay.lean"
        driver.write_text(adapter.read_text() + "\n#eval MhfeAudit.replay [" + ", ".join("`" + name for name in order) + "]\n")
        code = guarded("kernel-exact", [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)], env, evidence, evidence)
        observed = re.findall(r"^REPLAY_OK\|(.+)$", (evidence / "kernel-exact.log").read_text(), re.M)
        (evidence / "kernel-summary.json").write_text(json.dumps(
            {"requested": order, "observed": observed, "exitCode": code}, indent=2) + "\n")
        return code or int(observed != order)
    if args.phase == "controls":
        template = (Path(__file__).resolve().parent / "Inventory.lean").read_text()
        results = []
        for label, declaration, marker in [
            ("UnusedAxiom", "axiom AuditUnused : True", "AuditUnused"),
            ("Sorry", "theorem AuditSorry : False := by sorry", "sorryAx"),
            ("Native", "theorem AuditNative : (2 : Nat) + 2 = 4 := by native_decide", "_native"),
        ]:
            driver = evidence / ("Control" + label + ".lean")
            source = template.replace("namespace MhfeCodeAudit", "namespace MhfeProofs\n" +
                                      declaration + "\nend MhfeProofs\n\nnamespace MhfeCodeAudit", 1)
            driver.write_text(source)
            name = "control-" + label
            code = guarded(name, [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)], env, evidence, evidence)
            log = (evidence / (name + ".log")).read_text()
            rejected = "Local axioms are forbidden" in log or "Unexpected proof axioms" in log
            results.append({"name": label, "exitCode": code, "gateRejected": rejected, "markerFound": marker in log})
        (evidence / "control-summary.json").write_text(json.dumps(results, indent=2) + "\n")
        return int(not all(row["exitCode"] == 1 and row["gateRejected"] and row["markerFound"] for row in results))
    driver = evidence / "Inventory.lean"
    driver.write_text((Path(__file__).resolve().parent / "Inventory.lean").read_text())
    return guarded("axiom-inventory", [str(toolchain / "bin/lean"), "-j{JOBS}", str(driver)], env, evidence, evidence)


if __name__ == "__main__":
    sys.exit(main())
