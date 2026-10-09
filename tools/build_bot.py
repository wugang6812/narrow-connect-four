"""Compile the original C bot to a small freestanding WebAssembly module."""
from pathlib import Path
import argparse
import base64
import hashlib
import json
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--clang',default=shutil.which('clang'))
parser.add_argument('--lld',default=shutil.which('ld.lld'))
args=parser.parse_args()
if not args.clang or not args.lld:parser.error('Provide clang and ld.lld; no Emscripten or libc is required.')
work=ROOT/'audit/bot-build';work.mkdir(exist_ok=True)
obj=work/'bot.o';wasm=ROOT/'game/bot.wasm'
subprocess.run([args.clang,'--target=wasm32','-O3','-ffreestanding','-fno-builtin','-c',str(ROOT/'game/bot.c'),'-o',str(obj)],check=True)
exports=['bot_history_pointer','bot_policy_pointer','bot_choose','bot_depth','bot_source','bot_score','bot_nodes']
subprocess.run([args.lld,'-flavor','wasm','--no-entry','--allow-undefined','--export-memory',
                '--initial-memory=100663296','--max-memory=268435456',
                *['--export='+e for e in exports],str(obj),'-o',str(wasm)],check=True)
data=wasm.read_bytes()
(ROOT/'game/bot-module.js').write_text('/* Generated from bot.c; MIT licensed. */\nwindow.CONNECT4_BOT_WASM="'+base64.b64encode(data).decode()+'";\n',encoding='utf-8')
report={'status':'built','source_sha256':hashlib.sha256((ROOT/'game/bot.c').read_bytes()).hexdigest(),
        'wasm_sha256':hashlib.sha256(data).hexdigest(),'wasm_bytes':len(data),'exports':exports,
        'compiler':subprocess.run([args.clang,'--version'],capture_output=True,text=True).stdout.splitlines()[0]}
(ROOT/'audit/bot-build.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
