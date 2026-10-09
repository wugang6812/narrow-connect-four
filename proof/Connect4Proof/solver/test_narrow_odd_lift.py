"""Exhaustive finite regression of the mathematical lift against all enemy moves.

These runs exercise real wins in ALL rows. They supplement, rather than
replace, the universal lifting lemma and the independent certificate check.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from narrow4_probe_v3 import Geometry
from check_narrow_odd import require, verify, check_policy, play


def negative_controls(certificate):
    tests = []
    p = certificate["policies"][0]
    bad = copy.deepcopy(p)
    del bad["nodes"][bad["root"]]["1"]
    tests.append(("missing_enemy_branch", lambda: check_policy(bad)))
    bad_reply = copy.deepcopy(p)
    bad_reply["nodes"][bad_reply["root"]]["1"] = 5
    tests.append(("illegal_reply", lambda: check_policy(bad_reply)))
    bad_opening = dict(certificate, policies=certificate["policies"][:-1])
    tests.append(("missing_opening", lambda: verify(bad_opening)))
    bad_cap = copy.deepcopy(p)
    for key, actions in bad_cap["nodes"].items():
        cols = key.split("|")
        candidates = [c for c in range(4) if 2 < len(cols[c])+1 < p["height"]
                      and any(d != c and len(cols[d]) < p["height"] for d in range(4))]
        if candidates:
            c = candidates[0]
            d = next(d for d in range(4) if d != c and len(cols[d]) < p["height"])
            actions[str(c+1)] = d+1
            break
    tests.append(("uncapped_high_move", lambda: check_policy(bad_cap)))
    results = []
    for name, test in tests:
        try:
            test()
        except ValueError as error:
            results.append(dict(test=name, rejected=True, reason=str(error)))
        else:
            raise ValueError(f"Corrupted certificate accepted: {name}")
    return results


def exhaustive(height, policy):
    defender = policy["defender"]
    enemy = "W" if defender == "B" else "B"
    g = Geometry(height)
    seen = set()
    branches = buffers = tails = draws = wins = 0
    started = time.monotonic()

    def visit(board, black, white):
        nonlocal branches, buffers, tails, draws, wins
        mine, theirs = (black, white) if defender == "B" else (white, black)
        require(not g.has_four(theirs), "Enemy won in real board")
        if g.has_four(mine):
            wins += 1
            return
        if all(len(c) == height for c in board):
            draws += 1
            return
        if board in seen:
            return
        seen.add(board)
        virtual = []
        for column in board:
            require(all(column[r] != enemy or column[r-1] == defender
                        for r in range(3, len(column))), "Real support invariant failed")
            require(len(column) < 3 or len(column) == height or column[-1] == defender,
                    "Real high top invariant failed")
            if len(column) <= 6:
                virtual.append(column)
            else:
                virtual.append(column[:6] + (column[-1] if len(column) % 2 else ""))
        key = "|".join(virtual)
        for c in range(4):
            if len(board[c]) == height:
                continue
            branches += 1
            cell = 1 << (c * g.stride + len(board[c]))
            updated_enemy = theirs | cell
            require(not g.has_four(updated_enemy), f"Real enemy win at H={height}, {board}, {c+1}")
            child = play(board, c, enemy)
            if all(len(s) == height for s in child):
                draws += 1
                continue
            buffer = len(virtual[c]) == 7 or (len(virtual[c]) == 6 and len(child[c]) < height)
            if all(len(s) >= 6 for s in child):
                # The first six rows are now immutable. Finish in the high tail,
                # including when a virtual draw precedes the real full board.
                d = c if len(child[c]) < height else next(i for i in range(4) if len(child[i]) < height)
                tails += 1
            elif buffer:
                d = c
                buffers += 1
            else:
                require(key in policy["nodes"], f"No lifted control state: {key}")
                reply = policy["nodes"][key][str(c+1)]
                require(reply is not None, "Virtual draw while real reply required")
                d = reply - 1
            require(len(child[d]) < height, "Illegal lifted reply")
            own_cell = 1 << (d * g.stride + len(child[d]))
            updated_mine = mine | own_cell
            pieces = (updated_mine, updated_enemy) if defender == "B" else (updated_enemy, updated_mine)
            visit(play(child, d, defender), *pieces)

    root = tuple(policy["root"].split("|"))
    visit(root, *g.encode(root))
    result = dict(height=height, defender=defender, root=policy["root"],
                  states=len(seen), enemy_branches=branches, buffer_rounds=buffers, tail_replies=tails,
                  own_win_edges=wins, draw_edges=draws, seconds=time.monotonic()-started,
                  all_enemy_choices_checked=True)
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--heights", nargs="+", type=int, default=[7, 9])
    parser.add_argument("--out", type=Path, default=Path("reports/narrow_odd/lift_regression.json"))
    args = parser.parse_args()
    require(all(h >= 7 and h % 2 == 1 for h in args.heights), "Odd heights >= 7 required")
    path = Path("reports/narrow_odd/strategies.json")
    data = path.read_bytes()
    certificate = json.loads(data)
    report = dict(status="running", certificate_sha256=hashlib.sha256(data).hexdigest(),
                  negative_controls=negative_controls(certificate), finite_checks=[])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    for height in args.heights:
        for policy in certificate["policies"]:
            if policy["height"] == 7:
                report["finite_checks"].append(exhaustive(height, policy))
                args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    report["status"] = "complete"
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
