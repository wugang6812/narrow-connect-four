"""Decode the shipped policy asset for the native C console bot."""
from pathlib import Path
import argparse
import base64
import gzip
import hashlib
import re
root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('output',nargs='?',type=Path,default=root/'audit/standard-policy.bin')
args=parser.parse_args()
text=(root/'game/standard-policy.js').read_text(encoding='utf-8')
expected=re.search(r'sha256:"([0-9a-f]{64})"',text).group(1)
encoded=re.search(r'gzipBase64:"([A-Za-z0-9+/=]+)"',text).group(1)
data=gzip.decompress(base64.b64decode(encoded))
assert hashlib.sha256(data).hexdigest()==expected
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_bytes(data)
print('Decoded and SHA256-verified:',args.output,len(data),'bytes')
