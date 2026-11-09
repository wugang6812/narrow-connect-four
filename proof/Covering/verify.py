"""Audit the complete source/artifact closure, root axioms, and trust-zero import.

Run build.py first. This validator does not turn finite tests into proof claims.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext','Classical.choice','Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def lean_code(text):
    """Blank nested comments and string literals before checking proof escapes."""
    out=[]
    i=0
    while i<len(text):
        if text.startswith('/-',i):
            depth=1;i+=2
            while depth:
                if i>=len(text):raise ValueError('unterminated Lean comment')
                if text.startswith('/-',i):depth+=1;i+=2
                elif text.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            out.append(' ')
        elif text.startswith('--',i):
            end=text.find('\n',i)
            i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    return ''.join(out)

def main():
    start=time.monotonic()
    audit=json.loads((ROOT/'audit.json').read_text(encoding='utf-8'))
    assert audit['status']=='complete' and audit['all_requested_passed']
    modules=audit['modules']
    files={'.'.join(p.relative_to(ROOT/'src').with_suffix('').parts):p
           for p in (ROOT/'src').rglob('*.lean')}
    assert set(files)==set(modules), 'some source modules were not built'
    banned=re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|skipKernelTC)\b')
    for m,p in files.items():
        assert not banned.search(lean_code(p.read_text(encoding='utf-8'))), m
    def verify_hashes():
        for m,p in files.items():
            record=modules[m]
            artifact=ROOT/'build'/Path(*m.split('.')).with_suffix('.olean')
            assert record['status']=='passed' and record['exit_code']==0,m
            assert sha(p)==record['source_sha256'],('source changed',m)
            assert sha(artifact)==record['artifact_sha256'],('artifact changed',m)
    verify_hashes()
    compiler=Path(audit['compiler'])
    assert sha(compiler)==audit['compiler_sha256']
    expected=re.findall(r'^#print axioms ([\w.]+)',(ROOT/'src/Audit.lean').read_text(encoding='utf-8'),re.M)
    log=(ROOT/'logs/Audit.log').read_text(encoding='utf-8')
    axioms={name:[a.strip() for a in terms.split(',') if a.strip()]
            for name,terms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
    assert set(axioms)==set(expected),(axioms.keys(),expected)
    for name,used in axioms.items():
        assert set(used)<=ALLOWED,(name,used)
    runtime=(ROOT/'logs/ExecutableProbes.log').read_text(encoding='utf-8')
    assert 'All 70 Lean/reference response probes passed.' in runtime
    print(f'Checked {len(files)} source/artifact pairs and {len(axioms)} axiom closures. Starting trust-zero import replay.',flush=True)
    replay=ROOT/'replay'
    replay.mkdir(exist_ok=True)
    probe=replay/'Replay.lean'
    probe.write_text('import Audit\n#print axioms UniformFour.U1.first_exact_history_budget\n#print axioms UniformFour.U1.second_exact_history_budget\n',encoding='utf-8')
    env=os.environ.copy();env['LEAN_PATH']=str(ROOT/'build')
    command=[str(compiler),'-t','0','-j',str(os.cpu_count() or 1),str(probe)]
    result=subprocess.run(command,cwd=replay,env=env,capture_output=True,text=True,encoding='utf-8',timeout=300)
    (replay/'kernel.log').write_text(result.stdout+result.stderr,encoding='utf-8')
    assert result.returncode==0,(result.returncode,result.stdout,result.stderr)
    verify_hashes()
    report=dict(status='accepted',source_modules=len(files),source_and_artifact_hashes_match=True,
                source_escape_scan='passed',root_axioms=axioms,
                whitelist=sorted(ALLOWED),runtime_response_probes=70,
                kernel_replay=dict(exit_code=result.returncode,command=command,
                                   imported_module='Audit',transitive_local_modules=len(files),
                                   log_sha256=sha(replay/'kernel.log')),
                compiler_version=audit['compiler_version'],compiler_sha256=audit['compiler_sha256'],
                build_audit_sha256=sha(ROOT/'audit.json'),elapsed_seconds=round(time.monotonic()-start,3),
                scope='Finite four-column U1 active-budget optimum and U2 safety in the standalone model; exact history-prefix bridge. No old-repository IsDraw bridge, infinite-height theorem, full U3 compressed engine or Lean complexity theorem.')
    (ROOT/'kernel_audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps(dict(status='accepted',modules=len(files),axiom_closures=len(axioms),seconds=report['elapsed_seconds'])),flush=True)

if __name__=='__main__':
    main()
