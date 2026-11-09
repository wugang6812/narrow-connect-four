"""Check public proof sources and receipts; optionally rebuild and kernel-replay.

Default mode is a byte/receipt check, not a new Lean run.
--supporting selects the narrow-width/infinite-height model instead of Covering.
No command installs dependencies or changes published acceptance receipts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check_sources():
    manifest_path=ROOT/'audit/proof-manifest.json'
    manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
    receipt=json.loads((ROOT/'audit/proof-verification.json').read_text(encoding='utf-8'))
    assert receipt['source_manifest_sha256']==sha(manifest_path),'Receipt is for a different source manifest'
    expected={row['path'] for row in manifest['sources']}
    actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'proof/Covering/src').rglob('*.lean')}
    actual|={p.relative_to(ROOT).as_posix() for p in (ROOT/'proof/Narrow').rglob('*.lean')
             if 'build' not in p.relative_to(ROOT/'proof/Narrow').parts
             and '.lake' not in p.relative_to(ROOT/'proof/Narrow').parts}
    assert expected==actual,('Unexpected or missing proof source',sorted(expected^actual))
    for row in manifest['sources']:
        assert sha(ROOT/row['path'])==row['sha256'],('Source differs from accepted snapshot',row['path'])
    for group,count,roots in [('covering',55,14),('supporting',5,6)]:
        r=receipt[group]
        assert r['status']=='accepted' and r['source_modules']==count
        assert r['kernel_replay']['exit_code']==0 and r['kernel_replay']['trust_level']==0
        assert len(r['root_axioms'])==roots
        assert all(set(used)<=ALLOWED for used in r['root_axioms'].values())
        assert len(r['modules'])==count
        accepted_sources={}
        for row in r['modules']:
            if group=='covering':
                path='proof/Covering/src/'+row['module'].replace('.','/')+'.lean'
                assert row['exit_code']==0
            else:
                path='proof/Narrow/'+row['source']
            assert path not in accepted_sources,('Duplicate receipt source',path)
            accepted_sources[path]=row['source_sha256']
        prefix='proof/Covering/' if group=='covering' else 'proof/Narrow/'
        assert accepted_sources=={row['path']:row['sha256'] for row in manifest['sources']
                                  if row['path'].startswith(prefix)},'Receipt/source mismatch'
    return {'status':'passed','source_files':len(expected),'covering_modules':55,'supporting_modules':5,
            'selected_axiom_closures':20,'fresh_compilation':False,'fresh_kernel_replay':False,
            'scope':'Published source hashes and acceptance receipts only.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--supporting',action='store_true')
    parser.add_argument('--dependencies-from',type=Path)
    parser.add_argument('--lake')
    args=parser.parse_args()
    result=check_sources()
    if args.build or args.replay:
        if args.supporting:
            command=[sys.executable,str(ROOT/'tools/build_supporting.py')]
            if args.build:command.append('--build')
            if args.replay:command.append('--replay')
            if args.dependencies_from:command+=['--dependencies-from',str(args.dependencies_from)]
            if args.lake:command+=['--lake',args.lake]
            subprocess.run(command,cwd=ROOT,check=True)
        else:
            project=ROOT/'proof/Covering'
            if args.build:
                subprocess.run([sys.executable,'build.py','Audit'],cwd=project,check=True)
            if args.replay:
                subprocess.run([sys.executable,'verify.py'],cwd=project,check=True)
        result.update(fresh_compilation=args.build,fresh_kernel_replay=args.replay,
                      checked_project='supporting' if args.supporting else 'covering',
                      scope='Requested fresh Lean checks plus published source/receipt checks.')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
