"""Generate finite certificates for the odd-height lifting proof.

Height 5 is the real game; height 7 counts wins only in rows 1..6.
Cap enemy moves above row 2 unless their column is full.
The independent checker uses coordinate strings instead of this solver.
"""
from __future__ import annotations
import argparse
import functools
import hashlib
import json
import time
from pathlib import Path
from narrow4_probe_v3 import Geometry


def board_key(g, black, white):
    columns = []
    for c in range(4):
        s = ""
        for r in range(g.height):
            bit = 1 << (c * g.stride + r)
            if (black | white) & bit:
                s += "B" if black & bit else "W"
        columns.append(s)
    return "|".join(columns)


def solve(height, win_rows, defender, columns):
    g = Geometry(height)
    low = sum(((1 << win_rows) - 1) << (c * g.stride) for c in range(4))
    started = time.monotonic()
    choices = {}

    @functools.lru_cache(maxsize=None)
    def safe(black, white):
        mine, enemy = (black, white) if defender == "B" else (white, black)
        if g.has_four(mine & low):
            return True
        if g.has_four(enemy & low):
            return False
        for c, bit in g.moves(black | white):
            e = enemy | bit
            if g.has_four(e & low):
                return False
            replies = g.moves(mine | e)
            if not replies:
                continue
            row = (bit.bit_length() - 1) % g.stride + 1
            cap = [(d, b) for d, b in replies if d == c]
            allowed = replies if row <= 2 or not cap else cap
            for d, b in allowed:
                child = (mine | b, e) if defender == "B" else (e, mine | b)
                if safe(*child):
                    choices[(black, white, c)] = d
                    break
            else:
                return False
        return True

    root = g.encode(columns)
    if not safe(*root):
        raise RuntimeError(f"No constrained strategy: {height}, {defender}, {columns}")
    nodes = {}

    def collect(black, white):
        key = board_key(g, black, white)
        mine, enemy = (black, white) if defender == "B" else (white, black)
        if key in nodes or g.has_four(mine & low) or (black | white).bit_count() == 4 * height:
            return
        nodes[key] = actions = {}
        for c, bit in g.moves(black | white):
            e = enemy | bit
            replies = dict(g.moves(mine | e))
            if not replies:
                actions[str(c + 1)] = None
                continue
            d = choices[(black, white, c)]
            actions[str(c + 1)] = d + 1
            child = (mine | replies[d], e) if defender == "B" else (e, mine | replies[d])
            collect(*child)

    collect(*root)
    result = dict(height=height, win_rows=win_rows, defender=defender,
                  root="|".join(columns), nodes=nodes)
    print(json.dumps(dict(height=height, defender=defender, root=result["root"],
                         searched=safe.cache_info().currsize, certificate_nodes=len(nodes),
                         seconds=time.monotonic()-started)), flush=True)
    safe.cache_clear()
    return result


def reflect(policy):
    def flip(key):
        return "|".join(reversed(key.split("|")))
    return dict(height=policy["height"], win_rows=policy["win_rows"],
                defender=policy["defender"], root=flip(policy["root"]),
                nodes={flip(key): {str(5-int(c)): None if d is None else 5-d
                                   for c, d in actions.items()}
                       for key, actions in policy["nodes"].items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("reports/narrow_odd/strategies.json"))
    args = parser.parse_args()
    policies = []
    for height, win_rows in ((5, 5), (7, 6)):
        policies.append(solve(height, win_rows, "B", ("B", "", "", "")))
        for root in (("BW", "", "", ""), ("W", "B", "", "")):
            policy = solve(height, win_rows, "W", root)
            policies.extend((policy, reflect(policy)))
    certificate = dict(format="narrow4-odd-lift-v1", numbering="columns and rows start at 1",
                       max_uncapped_enemy_row=2, policies=policies)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(certificate, sort_keys=True, separators=(",", ":")) + "\n",
                        encoding="utf-8", newline="\n")
    print(json.dumps(dict(path=str(args.out), bytes=args.out.stat().st_size,
                         sha256=hashlib.sha256(args.out.read_bytes()).hexdigest())), flush=True)


if __name__ == "__main__":
    main()
