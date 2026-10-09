"""Independently check EVERY adversary branch in the odd-height certificates.

Standard library only. No solver, bitboards, pruning, or success claims are
trusted. The unbounded-height step is the separate written lifting lemma.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def four(board, player, win_rows):
    def at(c, r):
        return board[c][r] if 0 <= c < 4 and 0 <= r < min(len(board[c]), win_rows) else None
    return any(all(at(c + k*dc, r + k*dr) == player for k in range(4))
               for c in range(4) for r in range(win_rows)
               for dc, dr in ((0, 1), (1, 0), (1, 1), (1, -1)))


def play(board, c, player):
    child = list(board)
    child[c] += player
    return tuple(child)


def check_policy(policy):
    height, win_rows, defender = (policy[k] for k in ("height", "win_rows", "defender"))
    require((height, win_rows) in ((5, 5), (7, 6)), "Unexpected control game")
    require(defender in ("B", "W"), "Unknown defender")
    enemy = "W" if defender == "B" else "B"
    nodes = policy["nodes"]
    seen = set()
    branches = terminals = 0

    def check(board):
        nonlocal branches, terminals
        key = "|".join(board)
        if key in seen:
            return
        require(len(board) == 4 and all(len(c) <= height and set(c) <= {"B", "W"} for c in board),
                "Malformed board")
        nb = sum(c.count("B") for c in board)
        nw = sum(c.count("W") for c in board)
        require(nb == nw + (enemy == "W"), "Wrong turn/piece counts")
        require(not four(board, enemy, win_rows), f"Enemy already won: {key}")
        if four(board, defender, win_rows) or nb+nw == 4*height:
            terminals += 1
            return
        for column in board:
            require(all(column[r] != enemy or column[r-1] == defender
                        for r in range(3, len(column))), "Unsupported enemy above row 3")
            require(len(column) < 3 or len(column) == height or column[-1] == defender,
                    "Uncapped high enemy at a nonfull column")
        require(key in nodes, f"Missing nonterminal state: {key}")
        seen.add(key)
        actions = nodes[key]
        legal = [c for c in range(4) if len(board[c]) < height]
        require(set(actions) == {str(c+1) for c in legal}, "Enemy choices missing")
        for c in legal:
            branches += 1
            child = play(board, c, enemy)
            require(not four(child, enemy, win_rows), f"Enemy wins: {key}, column {c+1}")
            reply = actions[str(c+1)]
            if all(len(column) == height for column in child):
                require(reply is None, "Move after full-board draw")
                terminals += 1
                continue
            require(type(reply) is int and 1 <= reply <= 4, "Invalid reply")
            d = reply - 1
            require(len(child[d]) < height, "Illegal defender move")
            if 2 < len(child[c]) < height:
                require(d == c, "High move must be capped")
            check(play(child, d, defender))

    check(tuple(policy["root"].split("|")))
    require(seen == set(nodes), "Unverified/unreachable states in certificate")
    return dict(height=height, win_rows=win_rows, defender=defender, root=policy["root"],
                verified_states=len(seen), enemy_branches=branches, terminal_edges=terminals)


def verify(certificate):
    require(certificate["format"] == "narrow4-odd-lift-v1", "Wrong certificate format")
    require(certificate["max_uncapped_enemy_row"] == 2, "Wrong capping threshold")
    expected = {(h, "B", "B|||") for h in (5, 7)}
    for h in (5, 7):
        expected.update((h, "W", root) for root in ("BW|||", "|||BW", "W|B||", "||B|W"))
    keys = [(p["height"], p["defender"], p["root"]) for p in certificate["policies"]]
    require(len(keys) == len(set(keys)) and set(keys) == expected, "Incomplete openings")
    return [check_policy(p) for p in certificate["policies"]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path("reports/narrow_odd/strategies.json"))
    parser.add_argument("--out", type=Path, default=Path("reports/narrow_odd/check.json"))
    args = parser.parse_args()
    data = args.certificate.read_bytes()
    results = verify(json.loads(data))
    report = dict(status="complete", certificate_sha256=hashlib.sha256(data).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  finite_certificates_verified=True, lean_verified=False,
                  unbounded_step="Mathematical lifting lemma in notes/fourcolumns_odd_proof.md",
                  policies=results)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
