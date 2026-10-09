"""Re-elaborate the narrow proof sources serially and audit their public axioms."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "NarrowBoards", "FourColumns", "FourColumnsContinuation",
    "FourColumnsReserve", "FourColumnsRight", "FourColumnsRightFamilies", "FourColumnsFinal",
    "InfiniteNarrowBoards", "NarrowReviewChecks",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_THEOREMS = {
    "Connect4.NarrowBoards.narrow_empty_isDraw",
    "Connect4.FourColumns.opening0_safe",
    "Connect4.FourColumns.opening3_safe",
    "Connect4.FourColumns.black_nonloss_four_columns",
    "Connect4.FourColumns.four_columns_even_draw",
    "Connect4.FourColumns.four_columns_even_no_forced_win",
    "Connect4.InfiniteNarrowBoards.narrow_infinite_draw",
}


def main() -> int:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    toolchain_dir = toolchain.replace("/", "--").replace(":", "---")
    lake = ROOT.parent / "elan" / "toolchains" / toolchain_dir / "bin" / "lake.exe"
    reports = ROOT / "reports" / "narrow_review"
    output = ROOT / ".lake" / "build" / "lib" / "lean" / "experiments"
    reports.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "running", "toolchain": toolchain,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "modules": [], "axioms": {},
        "scope": "Named source modules and their public theorem dependency closures; excludes drafts.",
    }
    report_path = reports / "audit.json"

    def save() -> None:
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    save()
    try:
        for name in MODULES:
            source = ROOT / "experiments" / f"{name}.lean"
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            log = reports / f"{name}.txt"
            started = time.monotonic()
            print(f"Checking {name}", flush=True)
            with log.open("wb") as stream:
                result = subprocess.run(
                    [str(lake), "env", "lean", "-j", "2", "-o", str(output / f"{name}.olean"), str(source)],
                    cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, timeout=300,
                )
            text = log.read_text(encoding="utf-8")
            entry = {
                "source": source.relative_to(ROOT).as_posix(), "sha256": digest,
                "exit_code": result.returncode, "seconds": round(time.monotonic() - started, 3),
                "log": log.relative_to(ROOT).as_posix(),
                "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
            }
            report["modules"].append(entry)
            save()
            if result.returncode or re.search(r"declaration uses .sorry.", text):
                raise RuntimeError(f"{name} failed; see {log}")
            if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"{name} changed during compilation")
            for theorem, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
                axioms = sorted({v.strip() for v in names.split(",") if v.strip()})
                if set(axioms) - ALLOWED_AXIOMS:
                    raise RuntimeError(f"Unexpected axioms for {theorem}: {axioms}")
                report["axioms"][theorem] = axioms
            for theorem in re.findall(r"'([^']+)' does not depend on any axioms", text):
                report["axioms"][theorem] = []
        missing = REQUIRED_THEOREMS - report["axioms"].keys()
        if missing:
            raise RuntimeError(f"Public axiom audit output is incomplete: {sorted(missing)}")
        for entry in report["modules"]:
            if hashlib.sha256((ROOT / entry["source"]).read_bytes()).hexdigest() != entry["sha256"]:
                raise RuntimeError("A source changed before the audit completed")
        report["status"] = "complete"
        report["finite_four_columns_all_even_heights_complete"] = True
        report["infinite_widths_1_to_4_complete"] = True
        report["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
        save()
        print(f"PASS: {len(MODULES)} source modules; {len(report['axioms'])} public axiom closures", flush=True)
        return 0
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = str(exc)
        save()
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
