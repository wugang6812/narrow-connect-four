"""Improved A2 fixed-three search on maximal alternating segments.

The target must be at positive even distance above its column, so no vertical
four can have the three other cells already occupied. Each nonvertical slope
is checked by intersecting three ordered interval streams, with a parity test.
This is an A2 subroutine, not a complete compressed implementation of U2/U3.
"""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import random
import time


@dataclass(frozen=True)
class Segment:
    lo: int
    hi: int
    first: str

    def p_parity(self):
        return (self.lo + (self.first != 'P')) % 2


def encode(column):
    if not column:
        return []
    segments, start = [], 1
    for r in range(2, len(column)+1):
        if column[r-1] == column[r-2]:
            segments.append(Segment(start, r-1, column[start-1]))
            start = r
    segments.append(Segment(start, len(column), column[start-1]))
    return segments


def first_common_parity(streams, lo, hi, parity):
    """Minimum feasible point; iterations <= total interval count.

    Each stream consists of sorted disjoint closed intervals. The intervals
    denote points of one shared parity, not all integer points in each range.
    """
    if lo > hi or any(not stream for stream in streams):
        return None, 0
    pointers = [0]*len(streams)
    iterations = 0
    while all(p < len(stream) for p, stream in zip(pointers, streams)):
        intervals = [stream[p] for p, stream in zip(pointers, streams)]
        left = max(lo, *(a for a, _ in intervals))
        right = min(hi, *(b for _, b in intervals))
        candidate = left + ((parity-left) % 2)
        iterations += 1
        if candidate <= right:
            return candidate, iterations
        end = min(b for _, b in intervals)
        if end >= hi:
            return None, iterations
        for i, (_, b) in enumerate(intervals):
            if b == end:
                pointers[i] += 1
    return None, iterations


def winning_target(segments, heights, H, column, upper):
    """Least A2 fixed-three target in one specified column, or None.

    Caller checks outside-capacity parity and sets upper to the minimum row
    at which an unresolved line meets this target column (also capped by H).
    """
    lo, hi, parity = heights[column]+2, min(H, upper), heights[column] % 2
    best, steps, visited_intervals = None, 0, 0
    for slope in (-1, 0, 1):
        streams = []
        for other in range(4):
            if other == column:
                continue
            shift = slope*(other-column)
            stream = [(s.lo-shift, s.hi-shift) for s in segments[other]
                      if s.p_parity() == (parity+shift) % 2]
            streams.append(stream)
        result, iterations = first_common_parity(streams, lo, hi, parity)
        count = sum(map(len, streams))
        assert iterations <= count
        steps += iterations
        visited_intervals += count
        if result is not None:
            best = result if best is None else min(best, result)
    return best, steps, visited_intervals


def brute_target(columns, H, target, upper):
    for row in range(len(columns[target])+2, min(H, upper)+1, 2):
        for slope in (-1, 0, 1):
            if all(1 <= row+slope*(other-target) <= len(columns[other]) and
                   columns[other][row+slope*(other-target)-1] == 'P'
                   for other in range(4) if other != target):
                return row
    return None


def run_validation():
    rng = random.Random(20261108)
    started = time.monotonic()
    comparisons = max_steps = 0
    def check(columns, H, upper):
        nonlocal comparisons, max_steps
        segments = [encode(c) for c in columns]
        heights = list(map(len, columns))
        for j in range(4):
            fast, steps, _ = winning_target(segments, heights, H, j, upper)
            slow = brute_target(columns, H, j, upper)
            assert fast == slow, (columns, H, j, upper, fast, slow)
            comparisons += 1
            max_steps = max(max_steps, steps)

    # Exhaustive arbitrary columns up to height two, including non-game boards.
    words = ['', 'P', 'Q', 'PP', 'PQ', 'QP', 'QQ']
    for columns in product(words, repeat=4):
        for upper in (1, 2, 3, 4, 6):
            check(columns, 6, upper)

    # Taller arbitrary columns exercise multiple disjoint translated intervals.
    for _ in range(8000):
        H = rng.randrange(1, 65)
        columns = [''.join(rng.choice('PQ') for _ in range(rng.randrange(H+1)))
                   for _ in range(4)]
        check(columns, H, rng.randrange(H+1))

    # Huge height: consume segments directly, never expand cells.
    H = 10**12
    compact = [[], [Segment(1,H-1,'P')], [Segment(1,H-1,'Q')], [Segment(1,H-1,'P')]]
    target, steps, intervals = winning_target(compact, [0,H-1,H-1,H-1], H, 0, H)
    assert target == 2
    report = dict(status='passed', comparisons=comparisons,
                  exhaustive_column_tuples=7**4, randomized_boards=8000,
                  seed=20261108, max_pointer_iterations=max_steps,
                  huge_height=dict(height=H, total_segments=3, target=target,
                                   pointer_iterations=steps, filtered_intervals=intervals),
                  seconds=round(time.monotonic()-started,3),
                  scope='Exact fixed-three A2 subroutine against independent cell enumeration; not full U3 or a Lean complexity proof')
    path = Path(__file__).with_name('a2_interval_scan_results.json')
    path.write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(json.dumps(report,ensure_ascii=False))


if __name__ == '__main__':
    run_validation()
