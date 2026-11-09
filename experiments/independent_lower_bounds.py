"""Independent coordinate replay of U1's zero-active lower-bound constructions.

Four physical openings, all legal zero-cost replies at every branch, exact first
win stopping. Written for this review; no imports from supplied verification code.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def winner_after(board, column):
    row = len(board[column])-1
    color = board[column][row]
    def at(c, r):
        return 0 <= c < 4 and 0 <= r < len(board[c]) and board[c][r] == color
    for dc, dr in ((1,0),(0,1),(1,1),(1,-1)):
        count = 1
        for sign in (-1,1):
            k = 1
            while at(column+sign*k*dc, row+sign*k*dr):
                count += 1
                k += 1
        if count >= 4:
            return color
    return 0

def add(board, column, color, H):
    assert len(board[column]) < H
    b = list(board)
    b[column] += (color,)
    return tuple(b)

def first_lower(H, opening):
    m = H//2
    outer = opening in (0,3)
    mirror = opening in (2,3)
    physical = lambda c: 3-c if mirror else c
    board = add(((),(),(),()), opening, 1, H)
    moves = [1]*m+[3]*(m-1)+[0]*m if outer else [0]*2+[2]*m+[3]+[1]*m
    preparation_plies = 1
    for i, canonical in enumerate(moves):
        c = physical(canonical)
        board = add(board, c, 2, H)
        preparation_plies += 1
        assert winner_after(board,c) == 0
        if i != len(moves)-1:
            assert len(board[c]) < H  # zero cost forces this unique cover
            board = add(board,c,1,H)
            preparation_plies += 1
            assert winner_after(board,c) == 0
        else:
            assert len(board[c]) == H
    expected = (((1,)+(2,1)*(m-1)+(2,)), (2,1)*m, (), (2,1)*(m-1)) if outer else (
        (2,1)*2, ((1,)+(2,1)*(m-1)+(2,)), (2,1)*m, (2,1))
    assert board == (tuple(reversed(expected)) if mirror else expected)
    # Iterative tree walk avoids assuming a passive reply chosen by a script.
    legal = lambda b: [c for c in range(4) if len(b[c]) < H]
    pending = [(board, legal(board), 0)]
    leaves = []
    checked_replies = 0
    while pending:
        b, choices, depth = pending.pop()
        assert choices
        for c in choices:
            p = add(b,c,1,H)
            checked_replies += 1
            assert winner_after(p,c) == 0, ('premature first win',H,opening,p,c)
            assert len(p[c]) < H
            q = add(p,c,2,H)
            outcome = winner_after(q,c)
            if outcome:
                assert outcome == 2
                assert (c,len(q[c])) == (physical(2),2) if outer else (c,len(q[c])) == (physical(3),4)
                leaves.append(depth+1)
            else:
                assert legal(q)
                next_choices = legal(q) if len(q[c]) == H else [c]
                pending.append((q,next_choices,depth+1))
    assert leaves
    return dict(H=H, opening=opening+1, preparation_plies=preparation_plies,
                checked_replies=checked_replies, terminal_paths=len(leaves),
                max_response_rounds=max(leaves), all_paths_second_first_win=True)

def second_lower(H):
    b = ((),(),(),())
    for c in range(4):
        b = add(b,c,1,H)
        assert winner_after(b,c) == (1 if c == 3 else 0)
        if c == 3:
            return
        assert len(b[c]) < H
        b = add(b,c,2,H)
        assert winner_after(b,c) == 0

if __name__ == '__main__':
    rows = [first_lower(H,c) for H in range(4,201,2) for c in range(4)]
    for H in range(2,201):
        second_lower(H)
    report = dict(provenance='new coordinate checker written in this review',
                  first_heights='all even heights 4..200', first_openings='all four',
                  first_cases=len(rows), second_heights='all heights 2..200', second_cases=199,
                  all_passed=True, results=rows)
    (ROOT/'independent_lower_results.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'}))
