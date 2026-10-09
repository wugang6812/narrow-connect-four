"""Compile odd-height proof DAGs and audit axioms, with hash-checked resumption."""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ["FourColumnsOddCore", "FourColumnsOddGeometry", "FourColumnsOddFinite",
        "FourColumnsOddLift", "FourColumnsOddSound"]
FINAL = ["FourColumnsOddRoots", "FourColumnsOddAssembly", "FourColumnsOddFinal", "FourColumnsOddReview"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--certificates-only", action="store_true")
    parser.add_argument("--fresh", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error("Use 1..4 independent policy workers")
    generation = json.loads((ROOT / "reports/narrow_odd/lean_generation.json").read_text())
    if {p["policy"] for p in generation} != set(range(14)) or not all(p["complete"] for p in generation):
        raise ValueError("Generate ALL 14 complete policy DAGs before building")
    toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    lean = ROOT.parent / "elan/toolchains" / toolchain / "bin/lean.exe"
    cache = ROOT / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(cache)] +
        [str(p / ".lake/build/lib/lean") for p in (ROOT / ".lake/packages").iterdir() if p.is_dir()])
    folder = ROOT / "reports/narrow_odd/lean"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / "audit.json"
    previous = json.loads(path.read_text()) if path.exists() and not args.fresh else {}
    receipts = previous.get("modules", {})
    report = dict(status="building", started_at=time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                  certificates_only=args.certificates_only, modules={}, axioms={},
                  toolchain=toolchain, builder_sha256=digest(Path(__file__)),
                  generation_sha256=digest(ROOT / "reports/narrow_odd/lean_generation.json"),
                  strategy_sha256=digest(ROOT / "reports/narrow_odd/strategies.json"),
                  policy_nodes=sum(p["nodes_generated"] for p in generation),
                  policy_modules=sum(len(p["modules"]) for p in generation))
    lock = threading.Lock()
    stopped = threading.Event()

    def save():
        temporary = path.with_suffix(".part")
        temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
        temporary.replace(path)

    def compile_module(name, parent_hash):
        source = ROOT / f"experiments/{name}.lean"
        source_text = source.read_text(encoding="utf-8")
        if re.search(r"\b(sorry|admit|native_decide)\b|decide\s+\+native|skipKernelTC|^\s*axiom\s",
                     source_text, flags=re.MULTILINE):
            raise RuntimeError(f"Forbidden proof bypass in {name}")
        source_hash = digest(source)
        input_hash = hashlib.sha256((parent_hash + source_hash).encode()).hexdigest()
        output = cache / f"experiments/{name}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        old = receipts.get(name)
        if old and old.get("input_sha256") == input_hash and old.get("exit_code") == 0 and all(
            (ROOT / p).exists() and digest(ROOT / p) == h for p, h in old["artifacts"].items()
        ) and old.get("artifacts") and (ROOT / old["log"]).exists() and digest(ROOT / old["log"]) == old["log_sha256"]:
            entry = dict(old, resumed=True)
        else:
            print(f"Checking {name}", flush=True)
            log = folder / (name.replace("/", "_") + ".txt")
            started = time.monotonic()
            with log.open("wb") as stream:
                result = subprocess.run([str(lean), "-j", "2", "-o", str(output), str(source)],
                    cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
            text = log.read_text(encoding="utf-8")
            entry = dict(source=source.relative_to(ROOT).as_posix(), source_sha256=source_hash,
                         input_sha256=input_hash, exit_code=result.returncode,
                         seconds=round(time.monotonic()-started, 3), resumed=False,
                         log=log.relative_to(ROOT).as_posix(), log_sha256=digest(log), axioms={})
            if result.returncode or re.search(r"declaration uses .sorry.|sorryAx", text):
                with lock:
                    report["modules"][name] = entry
                    save()
                raise RuntimeError(f"{name} failed; see {log}")
            for theorem, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
                axioms = sorted({n.strip() for n in names.split(",") if n.strip()})
                if set(axioms)-ALLOWED:
                    raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
                entry["axioms"][theorem] = axioms
            for theorem in re.findall(r"'([^']+)' does not depend on any axioms", text):
                entry["axioms"][theorem] = []
            stem = output.with_suffix("")
            artifacts = list(output.parent.glob(stem.name + ".olean*")) + list(output.parent.glob(stem.name + ".ir*"))
            entry["artifacts"] = {p.relative_to(ROOT).as_posix(): digest(p) for p in artifacts}
            if not output.exists() or digest(source) != source_hash:
                raise RuntimeError(f"Missing artifact or source changed while compiling {name}")
        with lock:
            report["modules"][name] = entry
            report["axioms"].update(entry["axioms"])
            save()
        print(f"PASS {name} ({entry['seconds']:.1f}s{'; reused' if entry['resumed'] else ''})", flush=True)
        return input_hash

    try:
        with lock:
            save()
        # Include the imported, previously audited finite model in cache provenance.
        base_hash = digest(ROOT / "experiments/FourColumns.lean")
        for name in BASE:
            base_hash = compile_module(name, base_hash)
        mirror_hash = compile_module("FourColumnsOddMirror", base_hash)
        def policy_build(policy):
            chain = base_hash
            if "mirror_of" in policy:
                parent = futures[policy["mirror_of"]].result()
                chain = hashlib.sha256((base_hash + mirror_hash + parent).encode()).hexdigest()
            for name in policy["modules"]:
                if stopped.is_set():
                    raise RuntimeError("A policy failed; stopping remaining work at a module boundary")
                try:
                    chain = compile_module("OddCertificates/" + name, chain)
                except Exception:
                    stopped.set()
                    raise
            return chain
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {}
            # Queue independent DAGs first, so a waiting mirror never occupies
            # a worker that could be checking its unbuilt sibling policy.
            scheduling = [p for p in generation if "mirror_of" not in p] + [
                p for p in generation if "mirror_of" in p]
            for policy in scheduling:
                futures[policy["policy"]] = pool.submit(policy_build, policy)
            policy_hashes = [futures[p["policy"]].result() for p in generation]
        roots = {f"Connect4.FourColumns.OddCertificate.P{i}.root" for i in range(14)}
        if not roots <= report["axioms"].keys():
            raise RuntimeError("Not all 14 certificate root axiom closures were audited")
        if not args.certificates_only:
            chain = hashlib.sha256("".join(policy_hashes).encode()).hexdigest()
            for name in FINAL:
                chain = compile_module(name, chain)
            required = {"Connect4.FourColumns.four_columns_odd_draw",
                        "Connect4.FourColumns.four_columns_finite_draw",
                        "Connect4.FourColumns.four_columns_odd_no_forced_win"}
            if not required <= report["axioms"].keys():
                raise RuntimeError("Final theorem axiom audit is incomplete")
        for entry in report["modules"].values():
            if digest(ROOT / entry["source"]) != entry["source_sha256"]:
                raise RuntimeError("Source changed before audit completed")
        report["status"] = "certificates_complete" if args.certificates_only else "complete"
        report["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
        report["all_odd_heights_lean_verified"] = not args.certificates_only
        with lock:
            save()
        print(report["status"], flush=True)
    except Exception as error:
        with lock:
            report["status"] = "failed"
            report["error"] = str(error)
            save()
        raise


if __name__ == "__main__":
    main()
