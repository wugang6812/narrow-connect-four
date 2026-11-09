"""Extract and independently replay a real U2 trajectory with nine segments."""
from pathlib import Path
import json
from independent_lower_bounds import add, winner_after
from a2_interval_scan import encode

ROOT = Path(__file__).resolve().parent
source = (ROOT/'reference/check_uniform.py').read_text(encoding='utf-8')
witness = {}

def observe(H, columns, trail):
    count = sum(len(encode(c)) for c in columns)
    if count > witness.get('segments',-1):
        witness.update(height=H,columns=columns,segments=count,moves_one_based=[c+1 for c in trail])

edits = {
    'def check_shape(h,P,Q):': 'trail=[0] if first else []\n def check_shape(h,P,Q):',
    "st['states']+=1": "st['states']+=1\n  observe(H,board(h,P,Q),trail)",
    'else:ca,ct=visit(hp,PP,QQ)': 'else:\n    trail.extend([q,p])\n    ca,ct=visit(hp,PP,QQ)\n    del trail[-2:]',
}
for old,new in edits.items():
    assert source.count(old)==1
    source=source.replace(old,new)
env=dict(__name__='segment_witness_reference',observe=observe)
exec(compile(source,'instrumented_supplied_reference','exec'),env)
env['verify'](6,True)
assert witness['segments']==9

# Independent coordinate replay: no earlier win, no illegal placement, and
# correct active/passive accounting including the free first placement.
board=((),(),(),())
active=passive=0
last=None
for i, one_based in enumerate(witness['moves_one_based']):
    c=one_based-1
    if i and i%2==0 and c!=last:
        if len(board[last])<6: active+=1
        else: passive+=1
    board=add(board,c,1 if i%2==0 else 2,6)
    assert winner_after(board,c)==0
    last=c
columns=tuple(''.join('P' if stone==1 else 'Q' for stone in col) for col in board)
assert columns==tuple(witness['columns'])
assert sum(len(encode(c)) for c in columns)==9
assert active==1 and passive==3
witness.update(status='passed',active=active,passive=passive,
               independent_coordinate_replay=True,earlier_terminal=False,
               scope='One concrete lower witness for sharpness of the uniform nine-segment bound; not an arbitrary-height proof')
(ROOT/'segment_nine_witness.json').write_text(json.dumps(witness,indent=2),encoding='utf-8')
print(json.dumps(witness))
