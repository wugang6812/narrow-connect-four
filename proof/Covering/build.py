"""Dependency-aware isolated build. Each Lean process uses all logical CPUs.

No shared lock, downloads, repository mutations, or trust in stale build products.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
try:
    import psutil
except ImportError:
    psutil = None

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT/'src'
BUILD = ROOT/'build'
LOGS = ROOT/'logs'
requested_lean = os.environ.get('LEAN_BIN') or shutil.which('lean')
if not requested_lean:
    raise RuntimeError('Install the pinned Lean toolchain and set LEAN_BIN or put lean on PATH.')
LEAN = Path(shutil.which(requested_lean) or requested_lean).resolve()
if not LEAN.is_file():
    raise RuntimeError('LEAN_BIN must identify an installed Lean executable.')
CPUS = os.cpu_count() or 1
RAM = psutil.virtual_memory().available if psutil is not None else 0
JOBS = 3 if RAM >= 16*2**30 else 1
COMPILER_VERSION = subprocess.check_output([str(LEAN),'--version'],text=True,encoding='utf-8').strip()
PINNED_VERSION = (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip().split(':v')[-1]
if f'version {PINNED_VERSION},' not in COMPILER_VERSION:
    raise RuntimeError(f'Expected Lean {PINNED_VERSION}, got {COMPILER_VERSION}')
COMPILER_SHA = hashlib.sha256(LEAN.read_bytes()).hexdigest()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def compile_module(module, path, fingerprint):
    artifact = BUILD.joinpath(*module.split('.')).with_suffix('.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(BUILD)
    command = [str(LEAN), '-j', str(CPUS), '-o', str(artifact), str(path)]
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=SOURCE, env=env, capture_output=True,
                                encoding='utf-8', errors='replace', timeout=180)
        code = result.returncode
        output = result.stdout + result.stderr
    except subprocess.TimeoutExpired as exc:
        code = 'timeout'
        output = str(exc)
    log = LOGS/(module+'.log')
    log.write_text(output, encoding='utf-8')
    status = 'passed' if code == 0 else 'failed'
    entry = dict(status=status, exit_code=code, fingerprint=fingerprint,
                 source_sha256=sha(path.read_bytes()), log=str(log),
                 artifact_sha256=sha(artifact.read_bytes()) if code == 0 and artifact.exists() else None,
                 seconds=round(time.monotonic()-started, 3), command=command,
                 diagnostics=[l for l in output.splitlines() if 'error:' in l])
    print(json.dumps(dict(module=module, **entry), ensure_ascii=False), flush=True)
    return entry

def main():
    LOGS.mkdir(exist_ok=True)
    BUILD.mkdir(exist_ok=True)
    paths = {'.'.join(p.relative_to(SOURCE).with_suffix('').parts):p
             for p in SOURCE.rglob('*.lean')}
    imports = {m:re.findall(r'^import\s+([\w.]+)', p.read_text(encoding='utf-8'), re.M)
               for m,p in paths.items()}
    deps = {m:[d for d in names if d in paths] for m,names in imports.items()}
    targets = sys.argv[1:] or ['Audit']
    needed = set()
    def visit(m):
        if m in needed: return
        if m not in paths: raise ValueError('unknown target '+m)
        needed.add(m)
        for d in deps[m]: visit(d)
    for m in targets: visit(m)
    audit_path = ROOT/'audit.json'
    old = json.loads(audit_path.read_text(encoding='utf-8')).get('modules',{}) if audit_path.exists() else {}
    records = {}
    def save():
        audit = dict(status='complete' if len(records)==len(needed) else 'building',
                     all_requested_passed=len(records)==len(needed) and all(r['status']=='passed' for r in records.values()),
                     targets=targets, threads_per_lean=CPUS, independent_workers=JOBS,
                     available_ram_bytes_at_start=RAM, compiler=str(LEAN),
                     compiler_version=COMPILER_VERSION, compiler_sha256=COMPILER_SHA,
                     modules=records)
        temp = audit_path.with_suffix('.tmp')
        temp.write_text(json.dumps(audit,ensure_ascii=False,indent=2),encoding='utf-8')
        temp.replace(audit_path)
    pending = set(needed)
    running = {}
    save()
    with ThreadPoolExecutor(max_workers=JOBS) as executor:
        while pending or running:
            progress = False
            for m in sorted(pending):
                if not all(d in records for d in deps[m]): continue
                if any(records[d]['status'] != 'passed' for d in deps[m]):
                    records[m] = dict(status='blocked_dependency',dependencies=deps[m])
                    pending.remove(m); progress=True; continue
                fingerprint = sha((COMPILER_SHA+'|'+COMPILER_VERSION+'|'+sha(paths[m].read_bytes())+'|'+'|'.join(records[d]['fingerprint'] for d in deps[m])).encode())
                artifact = BUILD.joinpath(*m.split('.')).with_suffix('.olean')
                if (old.get(m,{}).get('status')=='passed' and old[m].get('fingerprint')==fingerprint
                        and artifact.exists() and old[m].get('artifact_sha256')==sha(artifact.read_bytes())):
                    records[m] = old[m]
                    pending.remove(m); progress=True; continue
                if len(running) >= JOBS: continue
                running[executor.submit(compile_module,m,paths[m],fingerprint)] = m
                pending.remove(m); progress=True
            save()
            if running:
                done,_ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    m = running.pop(future)
                    records[m] = future.result()
                save()
            elif pending and not progress:
                raise RuntimeError('dependency cycle: '+repr(pending))
    print(json.dumps({'passed':sum(r['status']=='passed' for r in records.values()),
                      'failed':sum(r['status']=='failed' for r in records.values()),
                      'blocked':sum(r['status']=='blocked_dependency' for r in records.values())}),flush=True)
    return 0 if all(r['status']=='passed' for r in records.values()) else 1

if __name__ == '__main__':
    raise SystemExit(main())
