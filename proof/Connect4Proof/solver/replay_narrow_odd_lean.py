"""Replay each new module with Lean's checker, then reject concrete bad premises.

This uses Lean's own kernel in a fresh process per module. Imported modules
are retained, while the selected module's declarations are checked again.
It is not a separate implementation of the Lean kernel.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--available", action="store_true",
        help="Replay a snapshot of successful modules during building; never marks the full review complete")
    parser.add_argument("--stock-checker", action="store_true",
        help="Use stock leanchecker prefix discovery instead of the identical direct replay entry point")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 2:
        parser.error("Use one or two checker workers")
    audit_path = ROOT / "reports/narrow_odd/lean/audit.json"
    audit = json.loads(audit_path.read_text())
    if not args.available and (audit["status"] != "complete" or not audit.get("all_odd_heights_lean_verified")):
        raise RuntimeError("The full build and final theorem audit must pass first")
    if args.available and audit["status"] not in {"building", "certificates_complete", "complete"}:
        raise RuntimeError("Available-module replay requires a successful or active build")
    selected = {name: entry for name, entry in audit["modules"].items() if entry["exit_code"] == 0}
    toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    bin_dir = ROOT.parent / "elan/toolchains" / toolchain / "bin"
    checker = bin_dir / "leanchecker.exe"
    runner = ROOT / "solver/ReplayOddModule.lean"
    engine_hash = digest(checker) if args.stock_checker else hashlib.sha256(
        (digest(bin_dir / "lean.exe") + digest(runner)).encode()).hexdigest()
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(ROOT / ".lake/build/lib/lean")] +
        [str(p / ".lake/build/lib/lean") for p in (ROOT / ".lake/packages").iterdir() if p.is_dir()])
    folder = ROOT / "reports/narrow_odd/replay"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / "audit.json"
    old = json.loads(path.read_text()) if path.exists() else {}
    report = dict(status="running", build_audit_sha256=digest(audit_path),
                  checker_sha256=engine_hash, modules={}, negative_tests=[],
                  engine="leanchecker" if args.stock_checker else "Lean.Replay via exact-module entry point",
                  runner_sha256=None if args.stock_checker else digest(runner),
                  available_only=args.available, full_review_verified=False,
                  scope="Replay all new odd-proof modules individually using Lean's own kernel.")
    lock = threading.Lock()

    def save():
        temp = path.with_suffix(".part")
        temp.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
        temp.replace(path)

    def replay(item):
        name, entry = item
        if digest(ROOT / entry["source"]) != entry["source_sha256"]:
            raise RuntimeError(f"Source changed since build: {name}")
        for artifact, expected in entry["artifacts"].items():
            if digest(ROOT / artifact) != expected:
                raise RuntimeError(f"Artifact changed since build: {artifact}")
        fingerprint = hashlib.sha256(json.dumps(
            [entry["artifacts"], report["checker_sha256"]], sort_keys=True).encode()).hexdigest()
        prior = old.get("modules", {}).get(name)
        if prior and prior["input_sha256"] == fingerprint and prior["exit_code"] == 0 and (
            ROOT / prior["log"]).exists() and digest(ROOT / prior["log"]) == prior["log_sha256"]:
            result = dict(prior, resumed=True)
        else:
            print(f"Replaying {name}", flush=True)
            log = folder / (name.replace("/", "_") + ".txt")
            started = time.monotonic()
            module = "experiments." + name.replace("/", ".")
            command = [str(checker), "-v", module] if args.stock_checker else [
                str(bin_dir / "lean.exe"), "-j", "2", "--run", str(runner), module]
            with log.open("wb") as stream:
                run = subprocess.run(command,
                    cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
            result = dict(input_sha256=fingerprint, exit_code=run.returncode,
                          seconds=round(time.monotonic()-started, 3), resumed=False,
                          log=log.relative_to(ROOT).as_posix(), log_sha256=digest(log))
            if run.returncode:
                raise RuntimeError(f"Kernel replay failed: {name}; {log}")
            if not args.stock_checker and f"kernel replay passed: {module}; declarations=" not in log.read_text(encoding="utf-8"):
                raise RuntimeError(f"Missing kernel replay receipt: {name}")
        with lock:
            report["modules"][name] = result
            save()
        print(f"REPLAY PASS {name} ({result['seconds']:.1f}s)", flush=True)

    try:
        save()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            list(pool.map(replay, selected.items()))
        if args.available:
            current = json.loads(audit_path.read_text())
            for name, entry in selected.items():
                latest = current.get("modules", {}).get(name)
                if not latest or latest["source_sha256"] != entry["source_sha256"] or latest["artifacts"] != entry["artifacts"]:
                    raise RuntimeError(f"A selected build receipt changed during replay: {name}")
            report["status"] = "available_complete"
            report["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
            save()
            print("Available modules replayed; final theorem review is still pending.", flush=True)
            return
        top_board = ("fourTuple [.black,.black,.black,.white,.black,.white,.black] "
                     "[.black,.white,.black,.black,.white,.black,.white] "
                     "[.white,.white,.white,.black,.black,.black,.white] "
                     "[.white,.white,.white,.black]")
        tests = {
            "illegal_full_column_reply":
                "Legal 1 (play (fourTuple [.black] [] [] []) 1 .white) 0",
            "high_control_win":
                f"HasFour 6 ({top_board}) .black",
            "virtual_full_is_not_real_full":
                "BoardFull 9 (fourTuple (List.replicate 7 .black) (List.replicate 7 .black) "
                "(List.replicate 7 .black) (List.replicate 7 .black))",
        }
        for name, proposition in tests.items():
            source = folder / (name + ".lean")
            source.write_text("import experiments.FourColumnsOddFinite\n"
                "namespace Connect4.FourColumns\n"
                "-- Intentionally false premise: compilation MUST fail.\n"
                f"example : {proposition} := by decide +kernel\n"
                "end Connect4.FourColumns\n", encoding="utf-8", newline="\n")
            log = folder / (name + ".txt")
            with log.open("wb") as stream:
                run = subprocess.run([str(bin_dir / "lean.exe"), "-j", "2", str(source)],
                    cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
            text = log.read_text(encoding="utf-8")
            if run.returncode == 0 or "error:" not in text or "decide" not in text:
                raise RuntimeError(f"Negative control was not rejected as expected: {name}")
            report["negative_tests"].append(dict(name=name, rejected=True, exit_code=run.returncode,
                source_sha256=digest(source), log=log.relative_to(ROOT).as_posix(), log_sha256=digest(log)))
            save()
        if digest(audit_path) != report["build_audit_sha256"]:
            raise RuntimeError("Build report changed during replay")
        report["status"] = "complete"
        report["full_review_verified"] = True
        report["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
        save()
        print("All kernel replays and negative controls passed.", flush=True)
    except Exception as error:
        with lock:
            report["status"] = "failed"
            report["error"] = str(error)
            save()
        raise


if __name__ == "__main__":
    main()
