"""Check preserved proof receipts, optionally compile and replay with pinned Lean.

Default mode checks files and historical records only. --build requires the
pinned toolchain and Mathlib cache to be installed already. No historical
acceptance record is overwritten by this script.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'proof/Connect4Proof'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def read(p):return json.loads(p.read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(condition,message):
    if not condition:raise RuntimeError(message)

def check_sources():
    package=read(ROOT/'audit/proof-package-manifest.json')
    for item in package['proof_files']:
        p=ROOT/item['path']
        require(p.is_file() and sha(p)==item['sha256'],'Preserved package mismatch: '+item['path'])
    records=[]
    for relative,count in [('reports/narrow_review/audit.json',9),('reports/narrow_odd/lean/audit.json',60)]:
        report=read(PROJECT/relative)
        require(report['status']=='complete' and len(report['modules'])==count,'Incomplete historical build: '+relative)
        entries = report['modules'].items() if isinstance(report['modules'],dict) else ((e['source'],e) for e in report['modules'])
        for name,entry in entries:
            require(entry['exit_code']==0,'Historical build failed: '+name)
            require(sha(PROJECT/entry['source'])==entry.get('source_sha256',entry.get('sha256')),'Source receipt mismatch: '+name)
            records.append(entry['source'])
        for theorem,axioms in report.get('axioms',{}).items():
            require(not(set(axioms)-ALLOWED),'Unexpected historical axioms: '+theorem)
    replay=read(PROJECT/'reports/narrow_odd/replay/audit.json')
    require(replay['status']=='complete' and replay['full_review_verified'] and not replay['available_only'],'Incomplete historical replay')
    require(len(replay['modules'])==60 and all(e['exit_code']==0 for e in replay['modules'].values()),'Historical replay module failure')
    require(len(replay['negative_tests'])==3 and all(t['rejected'] for t in replay['negative_tests']),'Historical negative tests did not pass')
    build=read(PROJECT/'reports/narrow_odd/lean/audit.json')
    require(replay['build_audit_sha256']==sha(PROJECT/'reports/narrow_odd/lean/audit.json'),'Replay/build receipt mismatch')
    require(build['all_odd_heights_lean_verified'],'Historical odd-height conclusion not accepted')
    require(len(set(records))==69,'Expected 69 distinct accepted experiment sources')
    return records,len(package['proof_files'])

def import_order(paths):
    order=[];seen=set();active=set()
    def visit(module):
        if module in seen:return
        if module in active:raise RuntimeError('Local import cycle: '+module)
        p=PROJECT/(module.replace('.','/')+'.lean')
        if not p.is_file():return  # external library module, obtained from pinned dependencies
        active.add(module)
        for line in p.read_text(encoding='utf-8').splitlines():
            if line.startswith('import '):
                for dependency in line[7:].split('--',1)[0].split():visit(dependency)
        active.remove(module);seen.add(module);order.append(module)
    for path in paths:visit(path[:-5].replace('/','.'))
    require(len(order)==70,'Expected the shared Basic module plus 69 accepted modules')
    return order

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--replay',action='store_true',help='Kernel-replay the 69 modules; requires built .olean files')
    parser.add_argument('--print-order',action='store_true')
    parser.add_argument('--lake',help='Path to the lake executable, if not on PATH')
    args=parser.parse_args()
    paths,package_files=check_sources();order=import_order(paths)
    if args.print_order:
        print('\n'.join(order));return
    result={'status':'passed','accepted_baseline':'5a1c02e',
            'preserved_package_files_verified':package_files,'accepted_source_hashes_verified':len(paths),
            'local_dependency_order_modules':len(order),
            'new_lean_compilation':False,'new_kernel_replay':False,
            'scope':'Source bytes and historical acceptance receipts only.'}
    if args.build or args.replay:
        lake=args.lake or shutil.which('lake')
        require(bool(lake),'Install the exact Lean toolchain and expose lake on PATH, or pass --lake.')
        version=subprocess.run([lake,'env','lean','--version'],cwd=PROJECT,capture_output=True,text=True,check=True).stdout
        require('4.34.0-rc2' in version,'The archive requires Lean 4.34.0-rc2, not a replacement version')
        log_root=ROOT/'audit/local-proof-check';log_root.mkdir(exist_ok=True)
        compiled=[];replayed=[]
        def run(label,command):
            start=time.monotonic();log=log_root/(label+'.txt')
            with log.open('wb') as out:
                proc=subprocess.run([lake,'env',*command],cwd=PROJECT,stdout=out,stderr=subprocess.STDOUT,timeout=3600)
            text=log.read_text(encoding='utf-8',errors='replace')
            require(proc.returncode==0 and 'sorryAx' not in text,'Lean check failed: '+str(log))
            return {'module':label,'seconds':round(time.monotonic()-start,2),'exit_code':proc.returncode,'log_sha256':sha(log)},text
        if args.build:
            for module in order:
                relative=Path(module.replace('.','/'))
                source=PROJECT/relative.with_suffix('.lean')
                output=PROJECT/'.lake/build/lib/lean'/relative.with_suffix('.olean')
                output.parent.mkdir(parents=True,exist_ok=True)
                before=sha(source)
                print('Compile',module,flush=True)
                entry,_=run(module.replace('.','_'),['lean','-j','2','-o',str(output),str(source)])
                require(sha(source)==before and output.is_file(),'Source changed or output missing: '+module)
                compiled.append(entry)
            entry,text=run('final_theorems',['lean',str(ROOT/'proof/ArchiveReview.lean')])
            closures=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
            require(len(closures)>=4,'Missing final theorem axiom output')
            for theorem,names in closures:
                require(not({n.strip() for n in names.split(',') if n.strip()}-ALLOWED),'Unexpected final axiom: '+theorem)
            compiled.append(entry)
            result['new_lean_compilation']=True
        if args.replay:
            for path in paths:
                module=path[:-5].replace('/','.')
                print('Kernel replay',module,flush=True)
                entry,text=run('replay_'+module.replace('.','_'),['lean','-j','2','--run','solver/ReplayOddModule.lean',module])
                require('kernel replay passed: '+module in text,'Missing exact-module replay receipt: '+module)
                replayed.append(entry)
            result['new_kernel_replay']=True
        result.update(scope='Requested fresh Lean checks plus source/receipt verification.',compilations=compiled,replays=replayed)
        (log_root/'result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
