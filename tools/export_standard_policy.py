"""Strip board coordinates from the accepted standard-board DAG for playing.

Every selected move, reply edge and reflection flag is preserved and checked
against the original board coordinates. This does not generate a new Lean proof.
"""
from pathlib import Path
import argparse
import base64
import gzip
import hashlib
import json
import mmap
import struct

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('archive',type=Path)
args=parser.parse_args()
folder=args.archive/'project/d1l_canonical_four'
metadata=json.loads((folder/'metadata.json').read_text(encoding='utf-8'))
accepted=json.loads((args.archive/'project/d1o_final_acceptance/audit_report.json').read_text(encoding='utf-8'))
assert accepted['status']=='complete'
build=json.loads((args.archive/'project/d1o_fast_full/build_manifest.json').read_text(encoding='utf-8'))
assert build['cache']['data_sha256']==metadata['data_sha256']
source=folder/'nodes.bin'
with source.open('rb') as f:source_sha=hashlib.file_digest(f,'sha256').hexdigest()
assert source_sha==metadata['data_sha256']
count=metadata['node_count'];row=struct.Struct('<QQBB7i')
assert source.stat().st_size==count*row.size
mask_board=sum(63<<(7*c) for c in range(7))
def four(x):
    for d in [1,7,6,8]:
        p=x&(x>>d)
        if p&(p>>(2*d)):return True
    return False
def mirror(x):return sum(((x>>(7*c))&127)<<(7*(6-c)) for c in range(7))
payload=bytearray();offsets=bytearray(count*4);base=40+count*4
edges=0;reflections=0
with source.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as data:
    for i in range(count):
        b,m,c,flags,*children=row.unpack_from(data,i*row.size)
        assert b&~m==0 and m&~mask_board==0 and b.bit_count()*2==m.bit_count() and c<7
        assert not four(m^b)
        heights=[]
        for d in range(7):
            col=(m>>(7*d))&63;assert col&(col+1)==0;heights.append(col.bit_count())
        assert heights[c]<6
        bit=1<<(7*c+heights[c]);b1=b|bit;m1=m|bit
        struct.pack_into('<I',offsets,i*4,base+len(payload))
        payload.extend(bytes([c,flags]))
        if flags&1:
            assert m1!=mask_board
            for d,j in enumerate(children):
                h=heights[d]+(c==d)
                if h==6:
                    assert j==-1 and not (flags>>(d+1))&1
                else:
                    assert 0<=j<i
                    cb,cm=struct.unpack_from('<QQ',data,j*row.size)
                    if (flags>>(d+1))&1:cb=mirror(cb);cm=mirror(cm);reflections+=1
                    assert cb==b1 and cm==m1|(1<<(7*d+h))
                    edges+=1
            payload.extend(struct.pack('<7i',*children))
        else:
            assert flags==0 and all(j==-1 for j in children) and four(b1)
        if (i+1)%500000==0:print('Checked and exported',i+1,'/',count,flush=True)
roots=[metadata['roots'][str(c)] for c in range(4)]
root_flags=sum(int(metadata['root_reflections'][str(c)])<<c for c in range(4))
header=struct.pack('<8s8I',b'NC4POL1\0',count,base,*roots,root_flags,0)
binary=header+offsets+payload
assert len(binary)<60000000 and edges==metadata['edge_count'] and reflections==metadata['reflected_edges']
compressed=gzip.compress(binary,compresslevel=6,mtime=0)
sha=hashlib.sha256(binary).hexdigest()
(ROOT/'audit/standard-policy.bin').write_bytes(binary)
(ROOT/'game/standard-policy.js').write_text('/* Derived from the accepted 7-column, 6-row first-player policy. MIT licensed. */\nwindow.CONNECT4_POLICY={sha256:"'+sha+'",bytes:'+str(len(binary))+',gzipBase64:"'+base64.b64encode(compressed).decode()+'"};\n',encoding='utf-8')
report={'status':'passed','source_format':metadata['format'],'source_nodes_sha256':source_sha,
        'accepted_audit_sha256':hashlib.sha256((args.archive/'project/d1o_final_acceptance/audit_report.json').read_bytes()).hexdigest(),
        'node_count':count,'edges_checked':edges,'reflections_checked':reflections,
        'exported_bytes':len(binary),'exported_sha256':sha,'gzip_bytes':len(compressed),
        'script_sha256':hashlib.sha256((ROOT/'game/standard-policy.js').read_bytes()).hexdigest(),
        'meaning':'Playing policy exported from accepted standard-board data; all board/reply correspondences checked. Not a new kernel replay or a universal all-position solver.'}
(ROOT/'audit/standard-policy-export.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
