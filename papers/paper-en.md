# Lean-Verified Draw Strategies for Narrow Connect Four

GPT

Journal revision, 28 September 2026. Not submitted.

## Abstract

We prove that gravity Connect Four from the empty board is a draw at every finite height when the width is at most four, and formalize the result in Lean. The even-height proof combines the classical second-player defence with an explicit first-player strategy covering every initial reply. For odd heights, the main construction reduces an unbounded family of boards to a finite control game. A supporting-stone invariant confines any first loss to the lowest six rows; a seventh control row records capacity without scoring. Verified control strategies lift to every odd height at least seven, with separate certificates for heights one, three and five. The lift handles full columns, immediate wins and continued real play after control fullness. The finite certificates contain 39,616 explicit nodes and fourteen roots. We also formalize the known infinite-height draws using fixed strategies. The contribution is a parameterized, reproducible proof development rather than a table of solved board sizes.

**Keywords:** Connect Four; drawing strategies; narrow boards; computer-assisted proof; Lean

## 1. Rules, prior work, and main results

### 1.1 Boards and strategies

A finite board has width \(w\ge1\) and height \(H\ge0\). A cell \((c,r)\) has column coordinate increasing from left to right and row coordinate increasing from the bottom. Black moves first. The players alternate, placing a stone in the lowest empty cell of a nonfull column. Four consecutive stones of one colour in a horizontal, vertical, or either diagonal direction win immediately. A full board without a winner is a draw. Passing, playing in a full column, and replying after the opponent has already won are not legal continuations.

We write \(B,W\) for the two colours and describe a position by its column strings, read from bottom to top. For example, \([BW,BWBW,\varnothing,\varnothing]\) has two nonempty columns. String powers denote concatenation. All position families below are subject to the stated capacity and turn conditions. If the defender has already won or the board is full, the prescribed continuation stops.

A nonlosing strategy assigns a fixed legal move to each reachable nonterminal history at which its player moves, and prevents the opponent from being the first to make four, against every legal opponent continuation. An empty board is a draw if both players have nonlosing strategies. On a finite board, play lasts at most \(wH\) moves; hence using both strategies produces a draw. Arbitrary play need not draw.

An infinite-height board has a bottom edge, positive-integer row coordinates, and no top edge. It starts empty, so each column is finite after every finite history. Endless play with no four is declared a draw. Here a strategy must protect every finite prefix simultaneously; a separate strategy for each chosen horizon would not suffice.

Our colour convention is the reverse of Allis's: his White is the first player and his Black the second. We therefore attribute his results by move order, not by copying colour names.

### 1.2 Prior results and attribution

Allis (1988, Section 2.2) proves that the second player can avoid defeat on boards of width at most six and positive even height. His construction uses replies in the same column, pairing, and a change of column at an appropriate point. The initial development of the present even-height argument used this known result and these defensive ideas. Section 4 restates and verifies the required four-column construction. Second-player nonloss alone does not establish a draw: a first-player strategy is also needed. Allis explicitly states the bound “at most six”, so no unproved monotonicity under deleting columns is needed here.

Yamaguchi et al. (2011, Sections 5.1–5.2) explicitly prove draws on infinite-height boards of widths one to three and four, respectively; related work appeared in the ACG proceedings (Yamaguchi et al., 2012). Thus the infinite-height conclusion in Section 7 is an existing mathematical result. Its role here is a common presentation and Lean formalization alongside the finite-height results. The technical report supplies the directly checked theorem statements; no internal theorem numbering is inferred from the proceedings abstract.

Tromp (2008, Table 2) reports computed draws for four columns and heights four through eleven. These are relevant prior small-board results, but a finite table does not prove a theorem for all heights. Connect Four has also been studied using formal models and model checking (Kant & van de Pol, 2014; Escobar & Insuasti, 2025). Kant and van de Pol check winning-strategy properties for fixed board sizes, whereas Escobar and Insuasti study the behaviour of a parallel minimax model. Our result is instead quantified over arbitrary heights and checked in a proof assistant.

Among the sources actually examined, we did not locate the specific all-odd-height proof via the seven-row control game given in Section 6. This is a statement about the search performed, not evidence of historical priority. We also do not claim that supporting stones, pairing, or downward threat analysis are new general ideas. For example, downward blocking arguments occur in related cylinder-board work (Yamaguchi & Neller, 2015), whose different rules prevent direct substitution for our lemmas.

Hamkins (2019) studies Connect-$\omega$, whose winning target is an infinite connected sequence. That winning condition differs from the finite four-stone condition here, even on an infinite board; his Connect-$\omega$ draw results are not used in our proofs.

### 1.3 Classification

**Theorem 1.1 (finite heights).** For every \(1\le w\le4\) and integer \(H\ge0\), both players have nonlosing strategies from the empty width-\(w\), height-\(H\) board.

**Theorem 1.2 (infinite height).** For every \(1\le w\le4\), both players have fixed nonlosing strategies on the infinite-height empty board. Its value is therefore a draw under the convention above.

Section 2 gives defensive lemmas. Section 3 handles widths at most three; Sections 4–5 handle the two players on four-column even-height boards. Section 6 handles odd heights by finite certificates and a height-independent lifting argument. Section 7 proves the infinite-height result separately. Section 8 relates these arguments to the verified definitions and records the evidence and trust boundary. The odd-height argument is computer-assisted: its finite certificates are part of the proof, not merely numerical tests.


### 1.4 Proof contributions and reading guide

The central construction is the odd-height reduction in Section 6: a finite strategy certificate controls an arbitrary real height through a support invariant and a capacity relation. This separates the finite computation from the unbounded mathematical argument. A solved seven-row ordinary game alone would not give the lifting theorem, because the extra control row is deliberately excluded from scoring.

The even-height first-player construction supplies the other half of the finite classification, complementing the attributed second-player defence. The formal development checks full-column legality and first-win semantics throughout. For readers primarily interested in the computer-assisted method, Sections 6 and 8 and Appendix A give the reduction, trust boundary and exact proof entry points; Sections 2-5 contain the explicit even-height strategy.

## 2. Defensive lemmas

### 2.1 Descent through supporting stones

A nonbottom White stone is a support exception if the stone immediately below it is also White. Gravity ensures that every nonbottom occupied cell has an occupied cell below; thus any other nonbottom White stone is supported by Black.

**Lemma 2.1 (support descent).** White cannot be the first winner by completing a horizontal or diagonal four all of whose stones have Black stones immediately below them.

**Proof.** Lower the entire line by one row. The resulting line consists of four Black stones in the same direction. All four were present before White's last move, including the support of the newly placed stone. Black had therefore already won, a contradiction. The colours may be exchanged. \(\square\)

This reduces defence to vertical lines, lines through the bottom row, and lines through support exceptions.

### 2.2 Permanent blocking

The same-column reply rule for Black is to cover White's last stone if its column remains nonfull; if White filled that column, Black plays in any other nonfull column. If the entire board is full, no reply is required.

**Lemma 2.2 (permanent defence).** Consider a nonterminal position with White to move. Suppose that:

1. every horizontal or diagonal winning line meeting the bottom row contains a Black stone;
2. White has no vertical four, and the top White run of every nonfull column has length at most two;
3. a set \(E\) contains every existing support exception and the cell immediately above every nonfull White-topped column, and every in-board horizontal or diagonal winning line through a cell of \(E\) contains a Black stone.

Then the same-column reply rule is nonlosing for Black.

**Proof.** Before an initially White-topped column is first processed, at most one further White stone can be added. Black then covers it, or the column is full and cannot grow. Once covered or proactively extended by Black, every nonfull column is Black-topped at the start of subsequent White turns. Every possible new support exception in an initially White-topped column has already been included in \(E\).

An initial White run can grow from at most two to at most three, after which a Black stone or the top boundary closes it; hence no White vertical four is possible. A first nonvertical White four through the bottom or through an exception is blocked by assumptions 1 or 3. Every other candidate is excluded by Lemma 2.1. If White fills a column and space remains elsewhere, a legal Black move exists. Finite capacity eventually ends play in a Black win or a draw. \(\square\)

We call this switching to permanent defence. If it is Black's turn when the conditions hold, Black can first add a stone in any nonfull column: this creates no White exception and removes none of the blockers. Terminal positions are handled immediately.

### 2.3 Reserving an odd-height column

**Lemma 2.3 (legal progress in a reserved column).** On a four-column board of even height \(H\), suppose White is to move and a reserved column \(j\) has odd height \(q\). When White enters \(j\), Black replies there; when White moves elsewhere, Black makes a legal move elsewhere and does not proactively enter \(j\). For any odd target row \(g\) with \(q<g<H\), this rule can be followed until Black occupies \((j,g)\), unless the game terminates earlier. Safety before reaching the target is a separate hypothesis at each application.

**Proof.** At the start of every White turn the total number of stones is odd. Removing the odd number in column \(j\) leaves an even number outside it. The outside capacity \(3H\) is even, so the number of outside empty cells is even. If White can move outside, at least two such cells exist before that move, leaving a legal outside reply for Black.

Each entry into the reserved column lets Black occupy the next row in the sequence \(q+2,q+4,\ldots,g\), all below the top boundary. White occupies rows of the opposite parity there, so the target is empty until Black takes it. Outside capacity is finite, and White cannot avoid the reserved column forever. \(\square\)

This lemma proves legality and progress, not safety by itself. At each use below we identify a cell that stays empty throughout any not-yet-permanently-blocked threat. The reserved column may initially be White-topped; possible new support exceptions must also be checked.

## 3. Widths one to three

**Theorem 3.1.** For every \(1\le w\le3\) and finite height \(H\ge0\), the empty board is a draw.

**Proof.** Horizontal and diagonal fours require four distinct columns and cannot occur. Fix defender \(P\) and opponent \(Q\). At the start of every \(Q\) turn, maintain that no column contains adjacent \(Q\) stones and every nonfull column is empty or \(P\)-topped. A new \(Q\) stone is then either on the bottom or supported by \(P\), and cannot create adjacent \(Q\)'s. If the column remains nonfull, \(P\) covers it; otherwise \(P\) uses any other nonfull column. A filled column never grows again, and adding \(P\) creates no adjacent \(Q\)'s.

The invariant holds initially for the second player. The first player starts with any legal stone and then uses the same strategy. Height zero is already a full, drawn board. At positive finite height, finite capacity gives termination without defeat. \(\square\)

**Corollary 3.2.** Infinite-height boards of widths one to three are draws.

**Proof.** The same fixed covering strategy applies without a full-column case. Its invariant excludes an opponent four at every finite prefix, and any first win would occur at a finite move. If both players use their strategies, play is endless without a winner. \(\square\)

## 4. The classical second-player defence at even height

This section supplies the four-column instance of the second-player result of Allis (1988, Section 2.2). The use of same-column replies, paired columns, and switching is attributed to that prior work; the following invariant proof is the version needed here.

**Theorem 4.1.** White has a nonlosing strategy on every four-column board of positive even height \(H\).

**Proof.** Pair adjacent columns as \(\{1,2\}\) and \(\{3,4\}\). If Black starts in \(q\), White starts in its partner \(p\). Let \(P=\{q,p\}\) and let \(R\) be the other pair. Thus White's first replies to columns 1, 2, 3, 4 are 2, 1, 4, 3.

Thereafter White covers each Black stone until Black first fills a column \(f\). White then adds a stone in the other column of \(P\), and resumes covering forever.

For legality, after White's first move the columns in \(P\) have odd heights and those in \(R\) even heights. Each round before the switch adds two stones to one column. A Black move in \(R\) leaves an odd height, strictly less than even \(H\), so White can cover it. Thus the first Black-filled column lies in \(P\). Its partner still has odd height below \(H\), making the switching move legal. All nonfull columns then have even heights, so every subsequent Black move can be covered. There is at most one switch.

Black vertical stones are separated except possibly for the two bottom Black stones in \(q\). These are covered or stopped by the top boundary when \(H=2\); the switching move adds no Black stone. There is therefore no Black vertical four. In \(R\), Black occupies only odd rows. Every diagonal uses the two adjacent columns of \(R\) at consecutive row numbers, ruling out a Black diagonal; \(R\) also rules out even-row horizontal fours. Before the switch, \(P\) contains Black stones only at even rows apart from the initial bottom stone, ruling out odd-row horizontal fours above the bottom. The bottom is blocked by White's first move. After the switch, the filled column \(f\) has permanent White stones at rows \(3,5,7,\ldots\), ruling out those same odd-row horizontal lines. These arguments apply immediately after each Black move, before White replies. \(\square\)

## 5. A first-player construction at even height

Black starts in column 1. A separate construction is needed because Theorem 4.1 alone does not determine the value. For a four-column board, the nonvertical lines through the bottom are the bottom horizontal and the diagonals

\[
((1,1),(2,2),(3,3),(4,4)),\qquad
D=((1,4),(2,3),(3,2),(4,1)).
\tag{5.1}
\]

An out-of-board line is ignored. The first two are blocked by \((1,1)=B\); \(D\) often needs an additional blocker.

### 5.1 White's first reply in column 2 or 3

**Proposition 5.1.** For even \(H\ge2\), Black is nonlosing after the opening \(B1,W2,B1\).

**Proof.** The position is

\[
[BB,W,\varnothing,\varnothing].
\tag{5.2}
\]

At \(H=2\), the full first column blocks both horizontal lines; vertical and diagonal fours do not exist. For \(H\ge4\), Black covers White in columns 1, 3, 4 until White first enters column 2. The outside columns have even heights before White moves, so replies are legal and the wait is finite. The bottom horizontal is blocked, \(D\) has an empty cell in column 2, and all other potentially dangerous lines have Black supports. The wait is safe.

After \(W(2,2)\), the new exception is horizontally and diagonally blocked by \((1,2)=B\) and \((1,1)=B\), with its descending diagonal out of bounds. Black plays \((2,3)\), reaching

\[
[BB(WB)^a,WWB,(WB)^c,(WB)^d].
\]

Now \(D\) is blocked by \((2,3)=B\); the sole exception \((2,2)\) has all its nonvertical lines blocked, and every other nonfull column is Black-topped. Apply Lemma 2.2. \(\square\)

**Proposition 5.2.** For \(H\ge2\), Black is nonlosing after \(B1,W3,B3\).

**Proof.** The position

\[
[B,\varnothing,WB,\varnothing]
\tag{5.3}
\]

has Black-topped nonempty nonfull columns and no support exception. The bottom lines are blocked by \((1,1)=B\) and \((3,2)=B\). Lemma 2.2 applies. This branch does not require even height. \(\square\)

### 5.2 White's first reply in column 1

**Proposition 5.3.** For even \(H\ge2\), Black is nonlosing after \(B1,W1,B4\).

**Proof.** The initial position is

\[
[BW,\varnothing,\varnothing,B].
\tag{5.4}
\]

At \(H=2\), the first column is full, the other nonempty column is Black-topped, and no exception or diagonal is possible; the bottom line is blocked. Apply Lemma 2.2.

For \(H\ge4\), Black covers White until White fills column 4. Before each White move the position has the form

\[
[BW(WB)^a,(WB)^b,(WB)^c,B(WB)^d].
\tag{5.5}
\]

The first three heights are even and the fourth odd, so column 4 is the only one White can fill. The two bottom corners block every bottom line. The only existing or potential exception is \(x=(1,3)\); its nonvertical lines are the row-3 horizontal and

\[
U_1=((1,3),(2,4),(3,5),(4,6)).
\tag{5.6}
\]

During the wait, \((4,3)\) on the horizontal and \((2,4)\) on \(U_1\) are empty or Black. White's first-column run has length at most two, and White stones elsewhere are separated. The wait is safe, legal, and finite.

Once column 4 is full, \((4,1)\) and \((4,3)\) are permanent Black stones. At \(H=4\), \(U_1\) is out of bounds, so use permanent defence. For \(H\ge6\), classify the current parameters:

1. If \(a=0\), Black takes \((1,3)\), removing the potential exception, and switches to permanent defence.
2. If \(a\ge1\) and \(b\ge2\), \((2,4)=B\) blocks \(U_1\); the row-3 line is already blocked.
3. If \(a\ge1\), \(b\le1\), and \(c\le2\), Black extends column 3 to odd height \(2c+1\le5\). If necessary, reserve it using Lemma 2.3 until Black occupies \((3,5)\). This target is empty before occupation and lies below \(H\), so \(U_1\) cannot be completed during the wait. All other dangerous lines are already blocked.
4. If \(a\ge1\), \(b\le1\), and \(c\ge3\), Black has \((1,4),(3,2),(4,1)\). For \(b=1\), playing \((2,3)\) wins along \(D\). For \(b=0\), play \((2,1)\), reserve column 2, and reply to \(W(2,2)\) with the winning \((2,3)\). Before that win, \((2,4)\) remains empty, blocking \(U_1\); the horizontal and bottom lines remain blocked. Lemma 2.3 gives safe legal progress.

These cases exhaust all parameters. \(\square\)

### 5.3 Three families for White's first reply in column 4

Throughout this subsection \(H\ge4\) is even. Write

\[
F_H=W(WB)^{H/2-1}W,\qquad
U=((1,5),(2,4),(3,3),(4,2)).
\tag{5.7}
\]

The full string \(F_H\) has White at rows 1 and 2, then Black at odd rows and White at even rows. Every family below has \((1,1)=(1,2)=B\). Thus the horizontal through \(x=(4,2)\) is blocked, leaving only \(U\) as its possible diagonal; \(U\) is out of bounds at height four. For the other potential exception \(y=(2,2)\), its horizontal and rising diagonal are blocked by \((1,2)\) and \((1,1)\); its falling diagonal is out of bounds.

**Lemma 5.4.** With White to move, Black is nonlosing in

\[
X(a,b,c,d)=[BB(WB)^a,(WB)^b,(WB)^c,W(WB)^d],
\tag{5.8}
\]

whenever the heights are legal, the parameters are nonnegative, and \(a\ge1\) or \(c\ge1\).

**Proof.** The diagonal \(D\) is blocked by \((1,4)=B\) if \(a\ge1\), or by \((3,2)=B\) if \(c\ge1\). The only existing or potential exception is \(x=(4,2)\), leaving \(U\) to defend. At height four apply Lemma 2.2.

For \(H\ge6\), cover White until column 4 is full. The other columns have even height and column 4 odd height, so the wait is legal and finite. Throughout it, \((2,4)\) is empty or Black, blocking \(U\); other blockers persist and every White top run has length at most two.

After column 4 becomes \(F_H\), if \(b\ge2\) then \((2,4)=B\), allowing permanent defence. If \(b\le1,c\le1\), extend column 3 to height 1 or 3 and, if necessary, reserve it until Black occupies \((3,3)\). That cell is empty until occupation, blocking \(U\), and the blocker of \(D\) persists.

In the remaining case \(b\le1,c\ge2\), the Black stones \((1,2),(3,4),(4,5)\) are fixed. If \(b=1\), playing \((2,3)\) wins along

\[
((1,2),(2,3),(3,4),(4,5)).
\tag{5.9}
\]

If \(b=0\), play \((2,1)\), reserve the column, and win at \((2,3)\) after \(W(2,2)\). Until then the empty \((2,4)\) prevents a White \(U\), and other threats are blocked. Lemma 2.3 supplies legality and termination. \(\square\)

**Lemma 5.5.** If \(d\ge0\) and \(2d+1<H\), Black is nonlosing with White to move in

\[
Y(d)=[BB,W,B,W(WB)^d].
\tag{5.10}
\]

**Proof.** The only existing or potential exceptions are \(y=(2,2)\) and \(x=(4,2)\). The fixed blockers described after (5.7) cover all lines through \(y\) and the horizontal through \(x\); only \(D\) and \(U\) remain.

Cover White in columns 1 and 4 until White first enters column 2 or 3, or fills column 4. Column 1 remains \(BB(WB)^a\) of even height, column 4 has odd height, and columns 2 and 3 remain \(W,B\). The empty \((2,3)\) blocks \(D\), the empty \((3,3)\) blocks \(U\), and White top runs have length at most two. The wait is safe and finite.

If White enters at \((2,2)\), cover at \((2,3)\), permanently blocking \(D\); then reserve column 3 to obtain \((3,3)\), blocking \(U\). If White enters at \((3,2)\), cover at \((3,3)\), then reserve the White-topped column 2 to obtain \((2,3)\). In either order the unfinished target remains empty until Black takes it. The possible exception at \((2,2)\) has its other lines blocked, so Lemmas 2.3 and 2.2 apply.

It remains that White fills column 4. If \(a\ge1\), \(D\) is already blocked by \((1,4)\). Play \((2,2)\), turning column 2 into \(WB\), then reserve column 3 until Black obtains \((3,3)\), and use permanent defence.

If \(a=0\), column 1 is \(BB\). Play \((1,3)\), threatening a vertical four. White cannot win immediately elsewhere: row 2 is blocked by \((1,2)\), \(D\) still lacks \((2,3)\), \(U\) lacks \((3,3)\), and column 4 is full. Thus White must play \((1,4)\) or lose on Black's next move.

After that forced reply, at \(H=4\) play \((3,2)\), blocking \(D\); \(U\) is out of bounds and Lemma 2.2 applies. At \(H\ge6\), play \((1,5)\), permanently blocking \(U\). The resulting White-to-move position is \([BBBWB,W,B,F_H]\). Reserve column 2 until Black occupies \((2,3)\), blocking \(D\). Before occupation this target is empty, and all lines through the possible exception \(y\), as well as the horizontal through \(x\), are already blocked. Apply permanent defence afterwards. \(\square\)

**Lemma 5.6.** With Black to move in

\[
[BB,\varnothing,\varnothing,F_H],
\tag{5.11}
\]

Black is nonlosing.

**Proof.** Play \((1,3)\). Both middle columns are empty, ruling out an immediate White nonvertical four elsewhere; column 4 is full. White must block the vertical threat at \((1,4)\).

At \(H=4\), play \((2,1)\) and reserve column 2 until Black takes \((2,3)\), blocking \(D\). The line \(U\) is out of bounds, the horizontal through \(x\) is blocked by \((1,2)\), and other White stones are supported. The wait is safe, after which Lemma 2.2 applies.

At \(H\ge6\), play \((1,5)\), permanently blocking \(U\). Cover White in column 1 until White first enters a middle column or fills column 1. During the wait the position is

\[
[BBBWB(WB)^a,\varnothing,\varnothing,F_H],
\qquad 5+2a<H,
\tag{5.12}
\]

with White to move. Empty middle columns rule out nonvertical wins, and White stones in column 1 remain separated. The wait is safe and finite.

If White first enters column 2, play at the bottom of column 3, then reserve the White-topped column 2 until Black takes \((2,3)\), blocking \(D\). The exception \(y\) has its lines blocked and \(U\) is already blocked by \((1,5)\). If White first enters column 3, cover at \((3,2)\), directly blocking \(D\), and apply Lemma 2.2. If White instead fills column 1, play at the bottom of column 2 and reserve it until \((2,3)\) is Black. The unfinished target is empty, so the wait is safe. Each reserved column starts at height 1 with target \(3<H\); Lemma 2.3 applies. \(\square\)

### 5.4 Assembling the column-4 reply

**Proposition 5.7.** For even \(H\ge2\), Black is nonlosing after \(B1,W4,B1\).

**Proof.** The position is

\[
[BB,\varnothing,\varnothing,W].
\tag{5.13}
\]

At \(H=2\), the full first column blocks every horizontal, and there is no vertical or diagonal four. For \(H\ge4\), cover White in column 4 until White first changes column or fills column 4. The middle columns remain empty, column 1 remains \(BB\), and the White run in column 4 has length at most two. The wait is safe, legal, and finite.

**Table 1. Responses after the opening Black 1, White 4, Black 1.**

| First event | Black's reply | Continuation |
|---|---|---|
| White enters column 1 at row 3 | Cover at row 4 | Lemma 5.4, \(a=1,b=c=0\) |
| White enters column 2 | Play at the bottom of column 3, rather than cover column 2 | Lemma 5.5 |
| White enters column 3 | Cover at row 2 | Lemma 5.4, \(c=1,a=b=0\) |
| White fills column 4 | Use (5.11) | Lemma 5.6 |

Table 1 covers every first event. Each continuation covers all subsequent White moves, so the branch is complete. \(\square\)

### 5.5 Assembling the empty-board strategy

**Theorem 5.8.** Black has a nonlosing strategy from the four-column empty board of every positive even height.

**Proof.** Black starts in column 1. In response to White's first move in columns 1, 2, 3, 4, Black plays in columns 4, 1, 3, 1, respectively. Propositions 5.3, 5.1, 5.2, and 5.7 provide the corresponding continuations. These four legal branches exhaust White's choices. \(\square\)

**Corollary 5.9.** For every integer \(n\ge1\), the empty four-column board of height \(2n\) is a draw.

**Proof.** Combine Theorems 4.1 and 5.8. Each strategy stops if a player has already won; using both prevents either player from being the first winner, and finite capacity forces a drawn full board. \(\square\)



## 6. Odd heights: a control game and a uniform lift

Fix defender \(P\) and opponent \(Q\); either colour may be the defender. Removing one row from an even-height board removes only four cells, but changes which player fills a column and whether a covering reply is legal. A difference in the total number of moves does not transfer a strategy. Lemma 2.1, however, is independent of height parity.

### 6.1 Localizing a first loss

At the beginning of every \(Q\) turn, maintain:

1. every \(Q\) stone at row 4 or above has a \(P\) stone immediately below;
2. every nonfull column of height at least 3 is \(P\)-topped.

Require \(P\) to cover a \(Q\) move at row 3 or higher whenever the column remains nonfull. If \(Q\) plays at row 1 or 2, or fills its column, \(P\) may choose another legal column.

These conditions are preserved from roots satisfying them. An uncovered \(Q\)-topped column that can still grow has height at most two, so its next \(Q\) stone is at most at row three and is then covered or stopped by the boundary. Every other new high \(Q\) stone lands on \(P\). Proactive \(P\) moves preserve the conditions.

**Lemma 6.1 (high-region safety).** Under these invariants, any first four-in-a-row by \(Q\) lies entirely within the lowest six rows.

**Proof.** A horizontal or diagonal four meeting row seven or above has its lowest row at least four, because its vertical span is at most three. All four stones are supported by \(P\); lowering the line gives an earlier \(P\) four, contradicting first victory. A high vertical four contains adjacent \(Q\) stones whose upper stone is at row four or above, contradicting its \(P\) support. This argument applies immediately after the \(Q\) move, before any covering reply. \(\square\)

### 6.2 The finite control game

Define \(C_7\) to have four columns of capacity seven, ordinary gravity and alternating moves, but to score four-in-a-row for **either player only when all four stones lie within rows one through six**. Row seven records capacity and colour without scoring. A full control board without a scoring four is a control draw. The defender is subject to the covering requirement of Section 6.1.

The seventh control row is a capacity marker, not a stone permanently fixed at real row seven. In particular, a defender four involving that control row cannot be counted as a real victory. Both players must use the same six-row scoring window.

A certificate is a finite directed acyclic strategy graph. Each ordinary node records a \(Q\)-to-move position and a defender. It is checked by one of three rules:

1. \(Q\) has no scoring four and \(P\) does: terminate;
2. \(Q\) has no scoring four and the control board is full: terminate;
3. for every legal \(Q\) move, check that it does not score a four; if a reply is required, supply a legal \(P\) move satisfying the covering condition and a checked child node.

Edges increase the number of stones, so reverse induction on that number verifies the graph. It represents all opponent choices together with a fixed defender reply, rather than assuming correctness of an external solver.

**Lemma 6.2 (control roots).** The \(Q\)-to-move positions in Table 2 have nonlosing control strategies satisfying the covering requirement.

**Table 2. Capacity-seven control roots in Lemma 6.2.**

| Defender | Root position | Opening | Distinct states before reflection reuse |
|---|---|---|---:|
| Black | \([B,\varnothing,\varnothing,\varnothing]\) | Black 1 | 14,488 |
| White | \([BW,\varnothing,\varnothing,\varnothing]\) | Black 1, White 1 | 9,700 |
| White | \([W,B,\varnothing,\varnothing]\) | Black 2, White 1 | 7,720 |
| White | \([\varnothing,\varnothing,B,W]\) | Black 3, White 4 | 7,720 |
| White | \([\varnothing,\varnothing,\varnothing,BW]\) | Black 4, White 4 | 9,700 |

**Computer-assisted proof.** Check each node against the three rules and induct in reverse stone-count order. The complete node data and corresponding Lean definitions accompany the paper; all root theorems have passed kernel verification. The last two roots also follow by reflection from the first two White roots. The state counts are not themselves evidence of validity: the supplied nodes and their checked derivations are the finite proof. \(\square\)

Black chooses column 1. White replies to Black's first column 1, 2, 3, or 4 in column 1, 1, 4, or 4, respectively. This reaches the listed roots and covers every first move. All roots satisfy the high-region invariants.

### 6.3 Lifting to every larger odd height

**Lemma 6.3 (odd-height lift).** Let \(H\ge7\) be odd. Every certified \(C_7\) strategy from a root in Lemma 6.2 induces a fixed nonlosing strategy from the corresponding real height-\(H\) position.

**Proof.** Maintain both a control position and a real position with equal colours in the lowest six rows. At synchronized \(Q\) turns, relate each pair of columns as in Table 3, for a nonnegative integer \(t\):

**Table 3. Column relation used by the odd-height lift.**

| Control column | Corresponding real column |
|---|---|
| Length below six | The entire column strings agree |
| Length six | Height \(6+2t\le H-1\), topped by \(P\) |
| Length seven, top marker \(P\) | Height \(7+2t\le H\); if nonfull, topped by \(P\) |
| Length seven, top marker \(Q\) | The real column is full |

Also maintain the support and top-colour invariants of Section 6.1. The final row of this relation requires real fullness, not an additional real top-colour condition. All root columns have height at most two, making the initial relation immediate.

**Buffer rounds.** Suppose \(Q\) enters a real nonfull column whose control column has length seven and marker \(P\). The real height and \(H\) are both odd, so at least two empty cells remain. Black or White as defender \(P\) can legally cover, increasing real height by two and leaving the control position unchanged. The same happens if the control length is six and \(Q\)'s move does not fill the real column: cover, increase the even real height by two, and leave the control position unchanged. The bottom six rows do not change; the new high \(Q\) stone is supported, so no first loss occurs.

**Synchronized rounds.** If the control length is below six, record the same \(Q\) stone in the control position. If the control length is six and \(Q\) has just filled the real column, record a seventh control \(Q\). In either case the control move is legal. Its certificate excludes a scoring \(Q\) four in the lowest six rows; Lemma 6.1 excludes a first high \(Q\) four.

If a reply is required, read the prescribed \(P\) column from the certificate. At control length below six, the real column agrees and the reply is legal. At control length six, its real height is even and strictly below odd \(H\); adding \(P\) is legal and establishes a length-seven control column with marker \(P\). The certificate never requests a move in a control-full column. The covering requirement preserves the support invariant in low synchronized rounds.

If \(P\) wins high on the real board, play stops successfully. If the control strategy ends with a scoring \(P\) four, equality of the lowest six rows gives an actual \(P\) four. A control move into an already full marker-\(Q\) column is never simulated, because its real column is already full.

**The tail after control fullness.** A full control board need not give a full real board. At that point, the real lowest six rows are fixed and full, with no \(Q\) four. Every subsequent move is at row seven or above. Continue covering; when \(Q\) fills its column and other real space remains, add \(P\) in any nonfull column. The support and top-colour conditions persist. The low region never changes, and Lemma 6.1 rules out a first \(Q\) win above it. If entry to this tail occurs on \(P\)'s turn, first make any legal \(P\) move; if the real board is already full, stop. This handles either player's move filling the control board.

Every buffer or tail round consumes real space, and there are only \(4H\) real cells, so no infinite wait occurs. Certificate replies are fixed in advance; arbitrary legal filler moves may be fixed as the leftmost available column. Maintaining the control state from the real history therefore defines one history-dependent strategy, not a family chosen afresh for each search depth. All legal \(Q\) moves are covered, and the first-win guard is checked before replies. \(\square\)

### 6.4 Heights one, three, and five

The seven-row root cannot directly be used at heights one or three. For each of those heights, we provide a complete first-player and second-player certificate: nine states in total for height one, and 406 for height three. They are checked at their actual capacities without lifting. At height one the elementary defence prevents the opponent from occupying the sole horizontal line. At height three only horizontal fours are possible. The certificates specify full legal strategies for both cases.

For height five, use actual-game certificates with both capacity and scoring height five. The roots have the same shapes as in Lemma 6.2: one Black root with 2,201 states, and four White roots with 1,353, 1,193, 1,193, and 1,353 states when ordered by Black's initial column 1, 2, 3, and 4. These total 7,293 states. All five height-five certificates are generated explicitly and checked node by node.

These small-height cases do not rely on a solver's reported game value. Their roots are concrete components of the certificate structure used by the final Lean theorem and are checked by the kernel. Together with Lemma 6.3 they cover every positive odd height.

### 6.5 Odd and arbitrary finite heights

**Theorem 6.4.** For every integer \(n\ge1\), the empty four-column board of height \(2n-1\) is a draw.

**Proof.** Use Section 6.4 at heights one, three, and five. Every other positive odd height is at least seven. Choose the openings of Lemma 6.2 and lift each player's control strategy by Lemma 6.3. Both players have nonlosing strategies. \(\square\)

Every positive integer is odd or even. Combining Theorem 6.4 with Corollary 5.9 proves the four-column result at all positive finite heights; height zero is already full and drawn. Theorem 3.1 supplies the other widths, completing Theorem 1.1. This is a parity classification, not a monotonicity assertion about adding or deleting a top row.

## 7. Infinite-height boards

Draws at widths one through four are prior results (Yamaguchi et al., 2011, Sections 5.1–5.2; 2012). We give fixed strategies suitable for the present rules and formalization, independently of finite top boundaries.

**Theorem 7.1.** The four-column infinite-height empty board is a draw.

**Proof.** Black starts in any column \(q\) and subsequently covers every White move. There is no top boundary, so replies are always legal. White stones in \(q\) occupy only even rows; White stones in the other three columns only odd rows. They are vertically separated. A horizontal line uses all four columns, but at each row at least one column has the wrong White parity. Among the three columns other than \(q\), two are adjacent; their White rows have equal parity, whereas consecutive cells of a diagonal have opposite parity. Hence White cannot complete a diagonal either.

For White, use the first paired-column response of Theorem 4.1 and thereafter always cover Black. No column fills, so there is no switch. In the first pair \(P\), Black stones apart from the initial one lie at even rows; in the other adjacent pair \(R\), they lie at odd rows. The pair \(R\) rules out diagonals and even-row horizontals. The pair \(P\) rules out odd-row horizontals above the bottom, and the first White stone blocks the bottom. Black's only possible adjacent vertical stones are its two bottom stones in the initial column, so there is no vertical four.

These invariants hold at every finite prefix. A first win would have to occur at some finite move; neither strategy permits one by its opponent. Using both strategies gives endless play without a winner. \(\square\)

Corollary 3.2 and Theorem 7.1 prove Theorem 1.2.


## 8. Formalization and verification evidence

### 8.1 Definitions and strategy quantifiers

The development uses Lean 4 (de Moura & Ullrich, 2021) and Mathlib (The mathlib Community, 2020). Boards map a finite type of columns to lists of stones, read bottom to top. A legal move appends to a nonfull column. The four-in-a-row predicate checks the four directions with every cell in bounds, without horizontal wrapping.

Finite safety is recursive in a remaining-move horizon. It first excludes an opponent four, then permits a defender win, a full board, or continued play. A defender turn existentially chooses a legal reply; an opponent turn universally quantifies over legal moves. Nonloss requires safety at every finite horizon. On a finite board, the \(wH\)-move bound means a strategy tree covering the entire remaining capacity fixes responses on every reachable history, matching Section 1.1. This finite-bound argument cannot simply be transferred to an infinite board.

For infinite boards, the strategy is an explicit function, existentially quantified outside the universal horizon quantifier. Thus the theorem supplies a single strategy protecting all finite prefixes, rather than separately selecting strategies at each horizon.

Widths at most three, finite four-column boards, and infinite-height boards use separate namespaces and safety definitions. They are interpreted using the same gravity, legal-move, and first-win conventions of Section 1. The paper unifies their mathematical statements; the implementation does not use a single IsDraw definition for every width and both height models. A formal statement must be read with its own definitions.

### 8.2 Formal entry points

Table 4 lists the principal entry points. Appendix A gives the correspondence with paper theorem numbers, auxiliary entry points and all fourteen certificate roots. Files are in the experiments directory; all namespace paths have the prefix Connect4.

**Table 4. Principal Lean entry points.**

| Result | Namespace and theorem | File |
|---|---|---|
| Widths at most three, any finite height | NarrowBoards.narrow_empty_isDraw | NarrowBoards.lean |
| Four columns, positive even height | FourColumns.four_columns_even_draw | FourColumnsFinal.lean |
| Uniform odd-height lift | FourColumns.odd_control_lift | FourColumnsOddSound.lean |
| Four columns, positive odd height | FourColumns.four_columns_odd_draw | FourColumnsOddFinal.lean |
| Four columns, every finite height | FourColumns.four_columns_finite_draw | FourColumnsOddFinal.lean |
| Widths one to four, infinite height | InfiniteNarrowBoards.narrow_infinite_draw | InfiniteNarrowBoards.lean |

The odd-height final theorem takes an arbitrary natural number \(n\) with \(1\le n\), and concludes that the empty board of height \(2n-1\) is a draw. The finite-height theorem takes an arbitrary natural number \(h\), including zero. Neither final theorem asks its caller to supply a control certificate: all fourteen roots have already been constructed and assembled. Corollaries excluding forced wins for either player also compile with the audited axiom closure.

The efficient finite four-in-a-row checker used in certificate verification is proved equivalent to the geometric predicate. External programs search for strategies and generate candidate material; acceptance depends on ordinary Lean proof terms and kernel checking, not on assuming those programs are correct.

### 8.3 Certificate size

The five capacity-seven roots contain 49,328 states before reflection reuse; the five capacity-five roots contain 7,293. The four roots for heights one and three contain 415, giving 57,036 states in total. Reusing the two reflected right-side White roots at capacity seven saves 9,700 plus 7,720 nodes, or 17,420 in total. Capacity-five certificates remain explicit. The Lean development therefore contains 39,616 explicit nodes and fourteen final roots.

Fifty modules contain certificate nodes; ten more contain definitions, bridges, lifting, assembly, and review, giving sixty new modules. The original nine-module chain already includes widths at most three, the four-column even-height result, and infinite height. Together these make 69 specially audited modules, excluding the shared Basic file and third-party libraries. These counts describe the finite proof material, not an enumeration of real positions at all heights.

### 8.4 Acceptance and trust boundary

The proof baseline is accepted revision 5a1c02e. The full compilation report for the sixty new modules completed on 13 September 2026 at 00:58:20 China Standard Time, with every exit code zero. Full module-by-module kernel replay completed at 01:06:20, with all sixty modules checked; it was not a partial available-files run. Root and final theorem closures contain only propext, Classical.choice, and Quot.sound. No new domain axiom, unfinished proof placeholder, or native-evaluation proof bypass occurs in the accepted proof chain. A clean axiom audit means this stated whitelist, not an axiom-free foundation.

The original reports are reports/narrow_odd/lean/audit.json, reports/narrow_odd/replay/audit.json, and reports/narrow_review/audit.json. Archiving additionally checks source, artifact, and log hashes and records checks performed after relocation. Replay uses Lean's own kernel interface; it is not an independently implemented second kernel.

Three deliberately invalid Lean tests are rejected: replying in a full column, counting a high control-board four as a scoring win, and inferring real fullness from control fullness. These address concrete lifting boundaries but do not replace the general proof. Earlier Python checks of certificates and lifted play at real heights seven and nine provide regression evidence, not the universal-height argument.

The toolchain is pinned to Lean 4.34.0-rc2 and Mathlib revision cecebc3014fd27da46b2899d7639ea643a444a51; the dependency manifest pins the other packages. The local archive contains sources, compiled dependencies, the toolchain, and verification entry points. The Lean kernel proves statements under their definitions. Faithfulness of those definitions to the intended game, accuracy of the prose exposition, and historical originality remain matters for human and bibliographic review.

## 9. Scope and further work

The paper organizes a complete drawing classification for widths one through four at all finite heights, together with the genuinely infinite-height result. Classical even-height second-player defence and the known infinite-height draws are attributed to prior work. The even-height first-player proof explicitly covers every opening reply; the odd-height proof combines finite control certificates with a lift having no bound on real height. Legality at full columns, checks for an opponent's immediate win, and the real-board tail after control fullness all occur in the final proof.

The concrete deliverables are the constructions and their organization, the control-game implementation and lift, parameterized Lean theorems, and replayable proof material. Our literature search does not settle priority for the full mathematical classification. The paper does not classify width five or greater and does not infer narrow-board values from the standard six-row, seven-column game. Nor does it turn Allis's second-player nonloss result into a claim that every board in his width range is drawn.

The odd-height proof remains computer-assisted. Replacing the tens of thousands of finite certificate nodes with a small collection of readable position families would simplify it while retaining the verified lifting theorem. Another improvement would be to unify the strategy interfaces of the three namespaces and mechanize their correspondence. These are opportunities for simplification and interface improvement, not missing hypotheses of the present four-column final theorem.

## Appendix A. Paper statements and Lean entry points

All qualified names below have the prefix `Connect4.`, and files are under `experiments/`. Theorem 1.1 combines the first and eleventh entries: there is no single implementation theorem spanning all namespaces. These are result-level entry points, not a claim that every prose lemma is implemented verbatim.

- Theorems 1.1 and 3.1: widths at most three: `NarrowBoards.narrow_empty_isDraw` in `NarrowBoards.lean`.
- Theorem 4.1: even-height second player: `FourColumns.white_nonloss_four_columns` in `FourColumns.lean`.
- Theorem 5.8: even-height first player: `FourColumns.black_nonloss_four_columns` in `FourColumnsFinal.lean`.
- Corollary 5.9: even-height draw: `FourColumns.four_columns_even_draw` in `FourColumnsFinal.lean`.
- Lemma 6.1: first-loss localization: `FourColumns.high_supported_no_four` in `FourColumnsOddCore.lean`.
- Lemma 6.3: uniform odd-height lift: `FourColumns.odd_control_lift` in `FourColumnsOddSound.lean`.
- Section 6.4: height one: `FourColumns.four_columns_height_one_draw` in `FourColumnsOddFinal.lean`.
- Section 6.4: height three: `FourColumns.four_columns_height_three_draw` in `FourColumnsOddFinal.lean`.
- Section 6.4: height five: `FourColumns.four_columns_height_five_draw` in `FourColumnsOddFinal.lean`.
- Theorem 6.4: all positive odd heights: `FourColumns.four_columns_odd_draw` in `FourColumnsOddFinal.lean`.
- Theorem 1.1: four columns, all finite heights: `FourColumns.four_columns_finite_draw` in `FourColumnsOddFinal.lean`.
- Theorem 7.1: four columns, infinite height: `InfiniteNarrowBoards.four_columns_infinite_draw` in `InfiniteNarrowBoards.lean`.
- Theorem 1.2 and Corollary 3.2: infinite height: `InfiniteNarrowBoards.narrow_infinite_draw` in `InfiniteNarrowBoards.lean`.

For Lemma 6.1, the listed theorem is applied after the opponent move and explicitly assumes the absence of a defender four; the preceding first-win guard supplies this condition. See the source for all invariant hypotheses.

**Table 5. The fourteen certificate roots supporting Lemma 6.2 and Section 6.4.**

| Root | Capacity / scoring height | Defender | Position | Root module |
|---|---|---|---|---|
| P0 | 5 / 5 | B | `[B,0,0,0]` | `P0_0002` |
| P1 | 5 / 5 | W | `[BW,0,0,0]` | `P1_0001` |
| P2 | 5 / 5 | W | `[0,0,0,BW]` | `P2_0001` |
| P3 | 5 / 5 | W | `[W,B,0,0]` | `P3_0001` |
| P4 | 5 / 5 | W | `[0,0,B,W]` | `P4_0001` |
| P5 | 7 / 6 | B | `[B,0,0,0]` | `P5_0014` |
| P6 | 7 / 6 | W | `[BW,0,0,0]` | `P6_0009` |
| P7 | 7 / 6 | W | `[0,0,0,BW]` | `P7_0000` |
| P8 | 7 / 6 | W | `[W,B,0,0]` | `P8_0007` |
| P9 | 7 / 6 | W | `[0,0,B,W]` | `P9_0000` |
| P10 | 1 / 1 | B | `[B,0,0,0]` | `P10_0000` |
| P11 | 1 / 1 | W | `[0,0,0,0]` | `P11_0000` |
| P12 | 3 / 3 | B | `[B,0,0,0]` | `P12_0000` |
| P13 | 3 / 3 | W | `[0,0,0,0]` | `P13_0000` |

Here 0 denotes an empty column. The full name of root Pj is `Connect4.FourColumns.OddCertificate.Pj.root`; root modules are in `experiments/OddCertificates/`. P7 and P9 reuse P6 and P8 by reflection. `odd_root_bundle` in `FourColumnsOddFinal.lean` supplies all roots. The earlier `OddAssembly` theorems still have a `roots` parameter and must not be mistaken for the final discharged statements.

## Materials and verification

The source package contains the accepted Lean sources, finite certificates, original verification records, dependency pins, third-party notices and a reviewer guide. It omits the compiled toolchain and dependency cache. Appendix A identifies the exact statements to inspect.

The formal acceptance evidence consists of the stated Lean kernel checks. Kernel checking does not certify historical priority, bibliographic attribution or the natural-language interpretation of the encoded definitions. The manuscript has not undergone journal peer review.

GPT: manuscript preparation and proof-artifact organization.

## References

Allis, V. (1988). *A knowledge-based approach of Connect-Four: The game is solved: White wins* [Master's thesis, Vrije Universiteit Amsterdam]. Report IR-163. https://tromp.github.io/c4/connect4_thesis.pdf

de Moura, L., & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. In A. Platzer & G. Sutcliffe (Eds.), *Automated Deduction—CADE 28* (LNCS Vol. 12699, pp. 625–635). Springer. https://doi.org/10.1007/978-3-030-79876-5_37

Escobar, D., & Insuasti, J. (2025). Formal verification of multi-thread minimax behavior using mCRL2 in the Connect 4. *Mathematics, 13*(1), Article 96. https://doi.org/10.3390/math13010096

Hamkins, J. D. (2019, April 30). *The connect-infinity game!* [Blog post]. https://jdh.hamkins.org/the-connect-infinity-game/

Kant, G., & van de Pol, J. (2014). Generating and solving symbolic parity games. *Electronic Proceedings in Theoretical Computer Science, 159*, 2–14. https://doi.org/10.4204/EPTCS.159.2

The mathlib Community. (2020). The Lean mathematical library. In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs* (pp. 367–381). ACM. https://doi.org/10.1145/3372885.3373824

Tromp, J. (2008). Solving Connect-4 on medium board sizes. *ICGA Journal, 31*(2), 110–112. https://doi.org/10.3233/ICG-2008-31205

Yamaguchi, Y., & Neller, T. W. (2015). First player's cannot-lose strategies for cylinder-infinite-connect-four with widths 2 and 6. In *Advances in Computer Games: ACG 2015* (LNCS Vol. 9525, pp. 113–121). Springer. https://doi.org/10.1007/978-3-319-27992-3_11

Yamaguchi, Y., Yamaguchi, K., Tanaka, T., & Kaneko, T. (2011). [A proof that infinite Connect Four is a draw] [Technical report in Japanese]. *IPSJ SIG Technical Report, 2011-GI-25*(1), 1–8. Original Japanese title and author names are preserved in the accompanying reference data. https://ipsj.ixsq.nii.ac.jp/records/73005

Yamaguchi, Y., Yamaguchi, K., Tanaka, T., & Kaneko, T. (2012). Infinite Connect-Four is solved: Draw. In H. J. van den Herik & A. Plaat (Eds.), *Advances in Computer Games: ACG 2011* (LNCS Vol. 7168, pp. 208–219). Springer. https://doi.org/10.1007/978-3-642-31866-5_18
