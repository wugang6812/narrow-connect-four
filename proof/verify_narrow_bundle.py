"""Portable archive verifier. Defaults to receipt hashes plus relocated Lean checks.

--replay-all replays the 69 accepted modules.
--rebuild recompiles the 70 local sources into a separate cache, then replays them.
Neither option overwrites the historical acceptance reports or original cache.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay-all", action="store_true")
    parser.add_argument("--rebuild", action="store_true")
    args = parser.parse_args()
    home = Path(__file__).resolve().parent
    project = home / "Connect4Proof"
    require(project.is_dir(), "Place this script in the archive's 02_Lean folder.")
    output = home.parent / "03_验收与引用" / "归档复核"
    output.mkdir(parents=True, exist_ok=True)
    report = {"status": "checking", "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "archive": str(home.parent), "proof_baseline": "5a1c02e",
              "mode": "rebuild" if args.rebuild else ("replay-all" if args.replay_all else "quick"),
              "hashes_checked": 0, "lean_checks": []}
    report_path = output / "archive_audit.json"

    def save():
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    def check(relative, expected):
        path = project / relative
        require(path.is_file(), f"Missing: {relative}")
        require(digest(path) == expected, f"SHA256 mismatch: {relative}")
        report["hashes_checked"] += 1

    def run(label, command, env, expected=0):
        log = output / (label + ".txt")
        begin = time.monotonic()
        with log.open("wb") as stream:
            result = subprocess.run(command, cwd=project, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=7200)
        entry = {"name": label, "exit_code": result.returncode,
                 "seconds": round(time.monotonic() - begin, 3),
                 "log": str(log.relative_to(home.parent)), "log_sha256": digest(log)}
        report["lean_checks"].append(entry)
        save()
        if expected == 0:
            require(result.returncode == 0, f"Lean failed: {label}; see {log}")
            require("sorryAx" not in log.read_text(encoding="utf-8"), f"Unfinished proof in {label}")
        else:
            require(result.returncode != 0, f"Negative test was unexpectedly accepted: {label}")
        print(f"{label}: exit {result.returncode}", flush=True)
        return log

    try:
        old = read(project / "reports/narrow_review/audit.json")
        build = read(project / "reports/narrow_odd/lean/audit.json")
        replay = read(project / "reports/narrow_odd/replay/audit.json")
        review = read(project / "reports/narrow_odd/lean_source_review.json")
        require(old["status"] == build["status"] == replay["status"] == "complete", "Incomplete reports")
        require(old["finite_four_columns_all_even_heights_complete"] and
                old["infinite_widths_1_to_4_complete"], "Old theorem acceptance missing")
        require(build["all_odd_heights_lean_verified"] and replay["full_review_verified"] and
                replay["available_only"] is False, "Partial odd-height review")
        require(len(old["modules"]) == 9 and len(build["modules"]) == len(replay["modules"]) == 60,
                "Unexpected module counts")
        require(set(build["modules"]) == set(replay["modules"]), "Replay scope differs from build")
        require(review["status"] == "accepted" and review["root_count"] == 14, "Root review incomplete")
        sources = []
        for item in old["modules"]:
            require(item["exit_code"] == 0, "Old compilation failed")
            check(item["source"], item["sha256"])
            check(item["log"], item["log_sha256"])
            sources.append(item["source"])
        for item in build["modules"].values():
            require(item["exit_code"] == 0, "Odd compilation failed")
            check(item["source"], item["source_sha256"])
            check(item["log"], item["log_sha256"])
            require(bool(item["artifacts"]), "Missing compilation artifact hashes")
            for path, sha in item["artifacts"].items():
                check(path, sha)
            sources.append(item["source"])
        for item in replay["modules"].values():
            require(item["exit_code"] == 0, "Replay failed")
            check(item["log"], item["log_sha256"])
        for path, sha in review["source_hashes"].items():
            check(path, sha)
        check("reports/narrow_odd/lean/audit.json", replay["build_audit_sha256"])
        check("solver/ReplayOddModule.lean", replay["runner_sha256"])
        check("solver/build_narrow_odd_lean.py", build["builder_sha256"])
        check("reports/narrow_odd/lean_generation.json", build["generation_sha256"])
        check("reports/narrow_odd/strategies.json", build["strategy_sha256"])
        for audit in (old, build):
            for name, axioms in audit["axioms"].items():
                require(set(axioms) <= ALLOWED, f"Unexpected axioms for {name}: {axioms}")
        for item in replay["negative_tests"]:
            require(item["rejected"], "Historical negative test did not fail")
            check(f"reports/narrow_odd/replay/{item['name']}.lean", item["source_sha256"])
            check(item["log"], item["log_sha256"])
        require(len(replay["negative_tests"]) == 3, "Missing negative tests")
        report["accepted_modules"] = len(sources)
        report["all_odd_heights_lean_verified"] = True
        report["source_hashes_match_acceptance"] = True
        version = (project / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        lean = home / "elan/toolchains" / version / "bin/lean.exe"
        require(lean.is_file(), "Bundled Lean executable missing")
        engine_hash = hashlib.sha256(
            (digest(lean) + digest(project / "solver/ReplayOddModule.lean")).encode()).hexdigest()
        require(engine_hash == replay["checker_sha256"], "Replay engine fingerprint mismatch")
        for name, item in replay["modules"].items():
            fingerprint = hashlib.sha256(json.dumps(
                [build["modules"][name]["artifacts"], engine_hash], sort_keys=True).encode()).hexdigest()
            require(fingerprint == item["input_sha256"], f"Replay input mismatch: {name}")
        env = os.environ.copy()
        env.pop("LEAN_SYSROOT", None)
        env.pop("LEAN_PATH", None)
        paths = [project / ".lake/build/lib/lean"] + sorted(
            p / ".lake/build/lib/lean" for p in (project / ".lake/packages").iterdir() if p.is_dir())
        env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
        report["lean_executable"] = str(lean)
        report["lean_search_paths"] = list(map(str, paths))
        run("toolchain", [str(lean), "--version"], env)
        if args.rebuild:
            fresh = output / "rebuild-cache"
            fresh.mkdir(exist_ok=True)
            # Only the fresh local module cache and bundled third-party libraries.
            env["LEAN_PATH"] = os.pathsep.join(map(str, [fresh] + paths[1:]))
            local = {p[:-5].replace("/", "."): p for p in ["Connect4Proof/Basic.lean"] + sources}
            completed = set()

            def compile_module(name):
                if name in completed:
                    return
                src = local[name]
                text = (project / src).read_text(encoding="utf-8")
                for dependency in re.findall(r"^\s*import\s+(\S+)", text, re.MULTILINE):
                    if dependency in local:
                        compile_module(dependency)
                target = fresh / Path(src).with_suffix(".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                run("rebuild_" + name.replace(".", "_"),
                    [str(lean), "-j", "2", "-o", str(target), src], env)
                completed.add(name)

            for name in local:
                compile_module(name)
            report["rebuilt_modules"] = len(completed)
        entry = home / "ArchiveReview.lean"
        log = run("ArchiveReview", [str(lean), "-j", "2", str(entry)], env)
        axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
                            log.read_text(encoding="utf-8"))
        require(len(axioms) == 5, f"Expected 5 final theorem closures, got {len(axioms)}")
        for name, names in axioms:
            require({s.strip() for s in names.split(",") if s.strip()} <= ALLOWED,
                    f"Unexpected relocated axioms: {name}")
        report["relocated_final_theorems_checked"] = True
        modules = [s[:-5].replace("/", ".") for s in sources] if (args.replay_all or args.rebuild) else [
            "experiments.FourColumnsOddFinal", "experiments.InfiniteNarrowBoards"]
        for module in modules:
            run("replay_" + module.replace(".", "_"),
                [str(lean), "-j", "2", "--run", "solver/ReplayOddModule.lean", module], env)
        for item in replay["negative_tests"]:
            run("negative_" + item["name"],
                [str(lean), "-j", "2", f"reports/narrow_odd/replay/{item['name']}.lean"], env, expected=1)
        report["status"] = "complete"
        report["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
        save()
        print(f"Archive verified: {report['hashes_checked']} receipt hashes, {len(sources)} accepted modules.",
              flush=True)
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = str(exc)
        save()
        raise


if __name__ == "__main__":
    main()
