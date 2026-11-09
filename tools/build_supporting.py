"""Build/replay the narrow-width and infinite-height supporting model.

Normal use requires the pinned dependencies installed with Lake in proof/Narrow.
--dependencies-from reuses an already installed project with the identical lock
file, but compiles all five local modules into this project's own build directory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'proof/Narrow'
MODULES=['Connect4Proof.Basic','experiments.NarrowBoards','experiments.FourColumns',
         'experiments.InfiniteNarrowBoards','NarrowAudit']
ALLOWED={'propext','Classical.choice','Quot.sound'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--dependencies-from',type=Path)
    parser.add_argument('--lake',default=shutil.which('lake'))
    args=parser.parse_args()
    if not (args.build or args.replay):
        parser.error('select --build and/or --replay')
    started=time.monotonic()
    env=os.environ.copy()
    output=PROJECT/'build'
    logs=PROJECT/'logs'
    output.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    external_paths=[]
    dep=args.dependencies_from.resolve() if args.dependencies_from else PROJECT
    expected=json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf-8'))
    actual=json.loads((dep/'lake-manifest.json').read_text(encoding='utf-8'))
    assert expected['packages']==actual['packages'],'Dependency pins differ'
    for package in expected['packages']:
        folder=dep/'.lake/packages'/package['name']
        rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=folder,text=True).strip()
        assert rev==package['rev'],('Installed dependency revision differs',package['name'])
        lib=folder/'.lake/build/lib/lean'
        if lib.is_dir():
            external_paths.append(str(lib))
    if args.dependencies_from:
        requested=os.environ.get('LEAN_BIN') or shutil.which('lean')
        if not requested:
            raise RuntimeError('Set LEAN_BIN for the installed pinned toolchain.')
        lean=Path(shutil.which(requested) or requested).resolve()
        command_prefix=[str(lean)]
    else:
        if not args.lake:
            raise RuntimeError('Install the pinned toolchain and dependencies; expose lake on PATH.')
        # Discover the pinned executable without allowing an old local Lake
        # artifact to shadow the freshly compiled output below.
        probe='import json,os,shutil; print(json.dumps({"lean":shutil.which("lean"),"PATH":os.environ["PATH"]}))'
        found=json.loads(subprocess.check_output([args.lake,'env',sys.executable,'-c',probe],
                                                cwd=PROJECT,env=env,text=True,encoding='utf-8'))
        assert found['lean'],'Lake did not provide a Lean executable'
        command_prefix=[found['lean']]
        env['PATH']=found['PATH']
    env['LEAN_PATH']=os.pathsep.join([str(output),*external_paths])
    version=subprocess.check_output(command_prefix+['--version'],cwd=PROJECT,env=env,text=True,encoding='utf-8').strip()
    required=(PROJECT/'lean-toolchain').read_text(encoding='utf-8').strip().split(':v')[-1]
    assert f'version {required},' in version,version
    cpus=os.cpu_count() or 1
    previous={}
    if not args.build:
        accepted=json.loads((PROJECT/'local-audit.json').read_text(encoding='utf-8'))
        assert accepted['compiler_version']==version,'Compiler changed; rebuild first'
        assert accepted['dependency_manifest_sha256']==sha(PROJECT/'lake-manifest.json')
        previous={row['module']:row for row in accepted['modules']}
    entries=[]
    for module in MODULES:
        source=PROJECT/Path(*module.split('.')).with_suffix('.lean')
        target=output/Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        before=sha(source)
        if args.build:
            command=command_prefix+['-j',str(cpus),'-o',str(target),str(source)]
            run=subprocess.run(command,cwd=PROJECT,env=env,capture_output=True,text=True,encoding='utf-8',timeout=600)
            (logs/(module+'.txt')).write_text(run.stdout+run.stderr,encoding='utf-8')
            assert run.returncode==0,(module,run.stdout[-3000:],run.stderr[-1000:])
            assert sha(source)==before
            print('Compiled '+module,flush=True)
        assert target.is_file(),('Build first',module)
        if not args.build:
            assert before==previous[module]['source_sha256'],('Source changed; rebuild first',module)
            assert sha(target)==previous[module]['artifact_sha256'],('Artifact changed; rebuild first',module)
        entries.append({'module':module,'source':source.relative_to(PROJECT).as_posix(),
                        'source_sha256':before,'artifact_sha256':sha(target)})
    audit_log=(logs/'NarrowAudit.txt').read_text(encoding='utf-8')
    roots={name:[x.strip() for x in terms.split(',') if x.strip()]
           for name,terms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit_log)}
    assert len(roots)==6 and all(set(x)<=ALLOWED for x in roots.values()),roots
    replay_record=None
    if args.replay:
        probe=output/'Replay.lean'
        probe.write_text('import NarrowAudit\n',encoding='utf-8')
        run=subprocess.run(command_prefix+['-t','0','-j',str(cpus),str(probe)],
                           cwd=PROJECT,env=env,capture_output=True,text=True,encoding='utf-8',timeout=600)
        replay_log=logs/'kernel-replay.txt'
        replay_log.write_text(run.stdout+run.stderr,encoding='utf-8')
        assert run.returncode==0,(run.stdout[-3000:],run.stderr[-1000:])
        replay_record={'exit_code':0,'trust_level':0,'import':'NarrowAudit',
                       'local_modules':len(MODULES),'log_sha256':sha(replay_log)}
    for row in entries:
        assert sha(PROJECT/row['source'])==row['source_sha256']
        target=output/Path(*row['module'].split('.')).with_suffix('.olean')
        assert sha(target)==row['artifact_sha256']
    report={'status':'accepted','compiler_version':version,'threads_per_lean':cpus,
            'dependency_manifest_sha256':sha(PROJECT/'lake-manifest.json'),
            'modules':entries,'root_axioms':roots,'kernel_replay':replay_record,
            'fresh_build':args.build,'seconds':round(time.monotonic()-started,3),
            'scope':'Finite widths one to three and genuinely infinite heights at widths one to four; supporting model, not an equivalence to the finite four-column model.'}
    (PROJECT/'local-audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({'status':'accepted','modules':len(entries),'axiom_closures':len(roots),
                      'replayed':args.replay,'seconds':report['seconds']}),flush=True)


if __name__=='__main__':
    main()
