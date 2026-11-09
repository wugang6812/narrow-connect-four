"""Rerun the supplied reviewed bitboard checker; instrument candidate segment counts.

The rule/checker is supplied evidence, NOT a new independent implementation.
The segment instrumentation is new to this review. No source files are changed.
"""
from pathlib import Path
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'reference/check_uniform.py'

def segment_count(h, P, Q, H):
    result = sum(n > 0 for n in h)
    for c, n in enumerate(h):
        for r in range(1, n):
            low, high = 1 << (c*H+r-1), 1 << (c*H+r)
            result += bool((P & low and P & high) or (Q & low and Q & high))
    return result

if __name__ == '__main__':
    source = SOURCE.read_text(encoding='utf-8')
    before = "st['states']+=1"
    after = before + "\n  st['max_segments_after_response']=max(st.get('max_segments_after_response',0),segment_count(h,P,Q,H))"
    assert source.count(before) == 1
    source = source.replace(before, after)
    before = 'choices[p]=(tuple(hp),PP,w,after)'
    after = before + "\n    segments=segment_count(hp,PP,QQ,H)\n    st['max_candidate_segments']=max(st.get('max_candidate_segments',0),segments)\n    assert segments<=9,('candidate exceeds proposed nine-segment bound',H,board(tuple(hp),PP,QQ),segments)"
    assert source.count(before) == 1
    source = source.replace(before, after)
    namespace = {'__name__': 'instrumented_supplied_checker', 'segment_count': segment_count}
    exec(compile(source, str(SOURCE)+' [instrumented]', 'exec'), namespace)
    results = []
    start = time.monotonic()
    for H in range(13):
        for first in (True, False):
            row = namespace['verify'](H, first)
            results.append(row)
            print(json.dumps(row), flush=True)
    report = dict(checker_source=SOURCE.relative_to(ROOT).as_posix(), checker_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  provenance='supplied checker rerun with new segment instrumentation',
                  scope='heights 0..12, both roles, all opponent continuations; no general-height inference from tests',
                  elapsed_seconds=round(time.monotonic()-start,3), results=results)
    (ROOT / 'upper_and_segments_results.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
