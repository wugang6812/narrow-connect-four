# Draw Strategies for Gravity Connect Four on One to Four Columns

## Covering strategies, optimal active-switch budgets, and Lean verification

GPT

8 November 2026

### Abstract

We give fixed non-losing strategies for both players in gravity Connect Four on boards of width one to four, for every finite height and for genuinely unbounded height. Consequently, the empty-board value under optimal play is a draw. For four columns we determine the minimum worst-case number of active column switches required by a non-losing strategy. The first player needs one exactly at even heights at least four, and zero otherwise; the second player needs one at every height at least two, and zero at heights zero and one. A switch is active when the opponent's last column remains playable. The opening move is free, while a winning reply is charged normally. The proof separates support descent, protection of unresolved lines, and even capacity outside reserved targets. A two-column capacity controller handles full-column transfers. Every reserved exit in the even-height first-player construction needs only one target, whereas the odd-height second-player construction may protect two distinct diagonals. Parametric counterstrategies establish the lower bounds for every opening column and every passive choice.

A companion Lean 4 development verifies a shared response rule and the exact active budgets at all finite four-column heights, including an equivalence with legal-history prefix semantics. Its 55 source modules, 14 selected axiom closures, and trust-zero import replay passed validation. A separate five-module development verifies the small-width and infinite-height draw results. The general resource lemma, total-switch bounds, and active budgets outside the finite four-column model remain paper proofs. Algorithm design and compressed execution are treated in a separate paper.

Keywords: gravity Connect Four; non-losing strategy; parity invariant; resource lemma; Lean 4; formal verification.

### Background and scope

Allis explicitly gave a second-player non-losing strategy for boards with at most six columns and a positive even number of rows [1, §2.2]. His convention is White first and Black second; we use player order throughout. The pairing mechanism in our even-height second-player proof is inherited from that work. We prove the required four-column instance directly, including its switch count, rather than assume that deleting columns preserves a strategy. Claimeven and the even-capacity condition for releasing combined rules [1, §§6.1, 7.1] provide related background.

Yamaguchi et al. studied infinite and semi-infinite boards under several placement restrictions [2]. We make no priority claim for infinite-board draws. Our particular model has a floor, no ceiling, at most four columns, and gravity; the proof supplies fixed strategies protecting every finite prefix.

“Covering strategy” means that a strategy with the stated restricted actions exists; we do not prove a transformation of every non-losing strategy into a normal form. Optimal play and minimum active-switch cost are distinct objectives, both addressed below. Sections 1–8 contain the mathematical proofs; Section 9 specifies the formal scope. The shared response algorithm, certificate checker, and compressed representation are developed separately [4].

## 1 Rules and the quantity to minimize

### 1.1 Game and fixed strategies

The width is a positive integer $w\le4$. A finite height $H$ is a nonnegative integer. Columns are numbered from left to right and rows from the floor upward, starting at one. A move places a stone in the lowest vacant square of a nonfull column. Four consecutive stones horizontally, vertically, or along either diagonal win. Play stops at the first four-in-a-row; the losing player receives no repair move. A full board with no winner is drawn.

For genuinely infinite height there is a floor but no ceiling. Only finitely many stones exist at each finite time. An infinite play with no winner is called a draw. A fixed strategy must protect all its finite prefixes; a separate strategy for each finite height does not establish this property.

We write $F$ for the first player's stone and $S$ for the second player's stone. Column words run from bottom to top; for example $[FS,\varnothing,\varnothing,F]$. A line with an out-of-board square is not a winning line. In general lemmas $P$ is the defending player and $Q$ the opponent, irrespective of player order.

A strategy assigns a legal move at each of its nonterminal legal histories. Whenever the construction allows several equivalent choices, choose the leftmost allowed column. Histories inconsistent with the construction may be assigned the leftmost legal move. Only consistent histories enter the non-loss proof.

### 1.2 Active and passive switches

We count one player's replies, not the sum for both players. A reply in a different column is **active** if the opponent's last column is still playable, and **passive** if the opponent just filled that column. A reply in the same column is called a cover. The first player's opening stone is not a reply and is free. If the opponent's move ends the game, there is no reply to count. A reply that itself wins is charged by the same rule before play stops.

For a fixed non-losing strategy, its active budget is the supremum of its active-switch count over all legal opponent continuations. Minimize this budget over all fixed non-losing strategies to obtain the optimal active budget. A lower bound must address every such strategy, including arbitrary history-dependent choices after a column becomes full.

### 1.3 Main results

**Theorem 1 (covering strategies).** For $w\le4$ and every finite $H\ge0$, each player has a fixed non-losing strategy using at most one active switch. Except for this possible reply, it covers whenever covering is legal. The same assertion holds for genuinely infinite height.

**Theorem 2 (exact four-column active budgets).**

| Height | First player | Second player |
|---|---:|---:|
| $H=0,1$ | 0 | 0 |
| $H=2,3$ | 0 | 1 |
| Odd $H\ge5$ | 0 | 1 |
| Even $H\ge4$ | 1 | 1 |

For infinite height the exact budgets are zero and one, respectively. At widths at most three both exact budgets are zero, at every finite or infinite height.

**Theorem 3 (total-switch upper bounds).** The constructed finite four-column strategies use at most four switches in total. The second-player constructions use at most two, including their opening reply. These are upper bounds, not claims that the optimal total budgets are four and two.

## 2 Support and targets that can be discharged separately

This section concerns finite height only. Its lemmas apply to either defending player.

### 2.1 Support descent and permanent defence

If a nonvertical $Q$ four-in-a-row avoids the bottom row and every stone has a $P$ stone directly below it, translating the line down one row gives an earlier $P$ four-in-a-row. Gravity ensures that all four supporting stones existed before the last $Q$ stone. Such a line therefore cannot give $Q$ the first win.

At a $Q$-to-move position, record the complete exception set $E$: every nonbottom $Q$ square immediately above another $Q$ stone, and the next vacant square of every nonfull $Q$-topped column. The latter records a possible exception on the next visit. Do not include a square beyond a full column. The nonvertical lines meeting the bottom row or $E$ are the lines requiring direct inspection. A line containing a $P$ stone is permanently blocked.

**Lemma 4 (permanent defence).** Suppose the position is nonterminal, the top run of $Q$ stones in every nonfull column has length at most two, $E$ is complete, and all lines requiring inspection are blocked by $P$. Then $P$ is non-losing by covering whenever possible and, after $Q$ fills a column, replying in any other legal column.

**Proof.** A top $Q$ run grows by at most one before it is capped by $P$ or the ceiling, so no new vertical four arises. All possible new support exceptions are already recorded in $E$. After a column has been processed and remains growable it is $P$-topped; adding another $P$ stone creates no new $Q$ exception. The bottom and exception lines remain blocked. Support descent excludes every other nonvertical first win. Crucially, this reasoning applies immediately after the $Q$ move, before the reply. A cover is legal if the original column is nonfull, and some other move exists if that column is full but the board is not. Stop at an earlier $P$ win or a full board. $\square$

If these conditions hold with $P$ to move, any legal $P$ stone preserves them; then apply the lemma, unless that stone already ends the game.

### 2.2 Target distances and external capacity

At a nonterminal $Q$ turn choose targets $(j,g_j)$, at most one per column. If column $j$ has height $q_j$, require

$$q_j<g_j\le H,\qquad g_j-q_j\equiv0\pmod2.$$

Let $J$ be the unresolved target columns. Their complement must have even total remaining capacity $O$. The defender never enters a target column voluntarily: after a $Q$ move there it covers; outside $J$ it covers if possible, and after an outside column fills it chooses another legal **outside** column.

The target distances remain positive and even at every $Q$ turn. The opponent can reach at most the square just below a target, and the cover is legal; thus a target can only be acquired by $P$. If $Q$ enters the outside, its positive even capacity was at least two, leaving an outside reply. Each complete outside round uses two squares. Replacing “outside column” by “any column” would invalidate the reservation.

### 2.3 Three target types and one resource lemma

Let $U_0$ be the initially unblocked lines requiring inspection. Define

$$\chi(j,g_j)=(H-g_j)\bmod2.$$

An **ordinary blocking target** protects lines through its square and requires $\chi=0$. A **terminal blocking target** lies on every line in $U_0$, so obtaining it ends the whole blocking task; its $\chi$ is unrestricted. A **winning target** completes a four-in-a-row with three already fixed $P$ stones. It may protect lines through a square in its column at or above the target, and its $\chi$ is also unrestricted.

Every line of $U_0$ must be protected by some pending target. One target may protect several lines. The terminal blocking condition refers to all of the initial $U_0$, hence also to every later unresolved subset.

**Lemma 5 (target resources).** Assume the structural hypotheses of Lemma 4, allowing the lines $U_0$ to remain unblocked, and the target, capacity, and protection conditions above. Follow the prescribed replies. On acquiring an ordinary target, release its column and remove the lines just blocked. On acquiring a terminal blocking target, enter permanent defence. On acquiring a winning target, stop with a win. An earlier transition to permanent defence is allowed only when all unresolved lines have been blocked. This is a legal non-losing strategy.

**Proof.** Maintain that the current exceptions are contained in the original $E$, all existing blockers remain fixed, every unresolved line has a pending protector, all pending distances are positive and even, and $O$ is even. Before choosing a reply, exclude a first $Q$ win. An ordinary or terminal blocking target is still empty. A winning target and the squares above it in its column are still empty by gravity. Thus no protected line has completed. All other nonvertical lines are blocked or excluded by support descent; top-run length excludes vertical wins.

Reply legality follows from Section 2.2. Covering or ceiling-capping introduces no exception outside $E$, and an outside $P$ stone introduces none. Stop if any chosen $P$ move wins early.

Acquiring an ordinary target blocks all lines assigned to it. Any remaining line still has another pending protector. Releasing its column adds $H-g_j$ to $O$, an even amount. Release permits subsequent ordinary covering in that column; it does not freeze the column. Other targets and the fixed stones supporting a winning target remain unchanged.

A terminal blocking target closes all initial obligations, giving Lemma 4. A winning target ends play immediately after the opponent's previous first win has been excluded. Neither case needs the old parity condition after termination, which explains why $\chi=1$ is allowed.

For termination use the total remaining capacity

$$\mathcal R=O+\sum_{j\in J}(H-q_j).$$

Release transfers the same remaining squares from a summand to $O$ and does not change $\mathcal R$. Each actual complete round reduces it by two. Pending protection prevents the necessary reply from disappearing into a full-board draw; finite capacity therefore forces all obligations to close or a terminal target to be obtained, unless play has already ended. Emptying only the ordinary-target subset is not a sufficient exit condition: a terminal or winning target may still protect an unresolved line. $\square$

The shortened expression $O+\sum_j(g_j-q_j)$ is not automatically a valid decreasing quantity across release, which makes squares above the target available. Likewise, two independent ordinary targets cannot be replaced by the promise to acquire at least one of them.

### 2.4 One parity identity

On a four-column board the total capacity is even. At a $Q$ turn the remaining capacity has parity $\varepsilon=1$ when $P$ is first and $\varepsilon=0$ when $P$ is second. Since all target gaps are even, outside capacity is even exactly when

$$\sum_{j\in J}\chi(j,g_j)\equiv\varepsilon\pmod2.$$

This is accounting, not a substitute for geometric safety. At other widths the right side must be the actual remaining-capacity parity. Within this interface a first-player waiting phase cannot use only ordinary targets, all of which have $\chi=0$; it needs a terminal or winning target with odd residual capacity. An odd-height second player can use two third-row ordinary targets, since $H-3$ is even. These are restrictions of this lemma, not impossibility results for every conceivable strategy.

## 3 A controller for two odd-capacity columns

**Lemma 6.** Suppose exactly two columns have odd remaining capacity at a nonterminal $Q$ turn; let their set be $R$. Cover until $Q$ first fills a column. It belongs to $R$. Reply in the other member of $R$, then cover forever until termination. All prescribed moves are legal, and the controller uses at most one switch, which is passive.

**Proof.** Covers consume two squares and preserve all capacity parities. A playable even-capacity column contains at least two vacancies at the start of a $Q$ turn and cannot be filled by $Q$. The other odd-capacity column has positive capacity when the first fills, so the transfer is legal. Both odd capacities become even; from then on every cover exists. $\square$

The lemma is independent of the parity of $H$ and proves legality and count, not geometric safety. The safety of the following entries is proved separately. To retain the one-switch count, the transfer must use the other odd-capacity column, even if a more permissive resource or permanent-defence lemma would allow additional choices.

## 4 The second player at odd heights

Assume odd $H\ge3$. Reflect columns by $c\mapsto5-c$ to reduce openings in columns three and four to columns two and one.

### 4.1 An interior opening

After $F(2,1)$, reply $S(1,1)$ and start Lemma 6 with $R=\{3,4\}$. Before the first filled column, every $F$-turn position is

$$[S(FS)^a,\ F(FS)^b,\ (FS)^c,\ (FS)^d].$$

The first two columns have odd height and cannot be filled by $F$. The only actual or potential support exception is $(2,2)$. The bottom horizontal and rising bottom diagonal are blocked by $S(1,1)$. Write

$$D=((1,4),(2,3),(3,2),(4,1)).$$

The square $(2,3)$ stays empty or belongs to $S$, protecting $D$. The exceptional second-row horizontal is protected by $(3,2)$ and $(4,2)$: before transfer, $F$ occupies only odd rows in these columns. The other valid diagonal through $(2,2)$ is already blocked by $(1,1)$.

When $F$ first fills column three or four, its second square is permanently $S$, also for $H=3$. Transfer to the other odd-capacity column. Even if that column's row parity changes, the filled column continues to block row two. Column two never participates in the transfer, preserving the guard at $(2,3)$. Its initial $F$ stone can become a bottom pair but is then covered; all other $F$ stones are separated. Support descent handles the remaining lines. These arguments include the column-filling move itself, before $S$ replies. Thus $S$ is non-losing, with one active opening reply and at most one passive transfer.

### 4.2 An exterior opening

After $F(1,1)$ reply $S(1,2)$. While both middle columns remain empty, cover in the outside columns. The waiting shape is

$$[(FS)^a,\varnothing,\varnothing,(FS)^d],\qquad a\ge1,\ d\ge0.$$

Empty middle columns exclude nonvertical wins and alternating outside columns exclude vertical wins. Finite capacity forces a first event:

| First event by $F$ | Reply by $S$ | Odd-capacity set afterwards |
|---|---|---|
| Enters $(2,1)$ | $(3,1)$ | $\{1,4\}$ |
| Enters $(3,1)$ | $(2,1)$ | $\{1,4\}$ |
| Fills column one | $(3,1)$ | $\{2,4\}$ |
| Fills column four | $(2,1)$ | $\{1,3\}$ |

The event leaves at least one middle column empty; a column-filling stone is supported by $S$. Hence it does not win. Each reply is in an empty middle column and is legal. Then use Lemma 6, with no further classification by $a,d$ or special transition rounds.

### 4.3 Safety after a middle-column event

Both middle columns have height one, with one bottom $F$ and one bottom $S$. The bottom horizontal is blocked. The sole potential exception is the second square of the $F$-bottomed middle column; its horizontal is blocked by the fixed $S(1,2)$. Let

$$R_0=((1,1),(2,2),(3,3),(4,4)).$$

The targets $(3,3)$ and $(2,3)$ protect $R_0$ and $D$, respectively. Middle-column heights stay odd, with $F$ entering even rows and $S$ covering odd rows. Only outside columns take part in the capacity transfer.

When the potential middle exception becomes actual it remains in the exception list. Its second-row line is still blocked, and its relevant bottom diagonal still has an empty or acquired target. No new first-win route appears. The top $F$ run reaches at most two and is covered; support descent handles other lines.

For $H\ge5$, Lemma 5 also explains separate discharge. Both third-row targets have gap two and even residual capacity $H-3$. Outside capacity $(H-2a)+(H-2d)$ is even. After one target is acquired, release its even residual capacity and continue to protect the other line. Acquiring either one alone is not enough to discard both obligations.

For $H=3$, the diagonals do not exist. The bottom and exceptional second-row horizontals are already blocked. Permanent defence is safe, but retain the specific controller to preserve the count.

### 4.4 Safety after an outside column fills

If column one fills and $S$ replies at $(3,1)$, then for $H\ge5$ the fixed $S(1,4)$ blocks $D$, while $(3,3)$ protects $R_0$. The only $F$-topped column is full, so its out-of-board successor is not a potential exception. The odd-capacity columns are two and four, leaving column three's protection unchanged.

If column four fills, reply at $(2,1)$. Now $S(4,4)$ blocks $R_0$, and $(2,3)$ protects $D$; the odd-capacity columns are one and three. For $H=3$ both diagonals are absent and the bottom $S$ stone blocks the remaining bottom horizontal. The same vertical and support arguments apply.

### 4.5 Counts and fixed choices

An interior opening spends one active switch immediately, followed by at most one passive transfer. For an exterior opening, the waiting phase only covers. A first middle-column event uses one active switch, then at most one passive transfer. A first filled-outside-column event uses one passive switch, then at most one more passive transfer. These alternatives are exclusive. In every case the active budget is at most one and the total count at most two.

## 5 Upper bounds for the remaining cases

### 5.1 Small widths and small heights

At widths at most three, only vertical fours exist. The first player opens in a fixed column; thereafter either defending player covers whenever possible and switches only after a column fills. Before its opponent's turn, each growable nonempty column is defender-topped, precluding an opponent vertical four. This uses zero active switches. At infinite height covering is always legal.

Height zero is already full. On a four-column board of height one each player places at most two stones, so no four exists; every reply to a move in a different column is passive.

At four-column heights two and three, the first player occupies any fixed bottom square and thereafter covers or switches after a fill. Only horizontals can win. The opening blocks the bottom horizontal, and every higher opponent horizontal would have an earlier first-player supporting horizontal. Thus the first-player budget is zero. At height three the second player uses Section 4; an unrelated row-partner strategy that switches repeatedly cannot establish our active count.

### 5.2 The first player at odd heights

Let odd $H\ge5$. Open at $(1,1)$, blocking the bottom horizontal and $R_0$. There are no opponent exceptions, leaving only $D$. Reserve $(3,2)$, of gap two, with outside capacity $3H-1$ even.

Cover outside the target column, transferring only to another outside column after a fill. Once the opponent enters column three, cover at $(3,2)$, block $D$, and enter permanent defence. Before then, the target stays empty, while fixed blockers or support descent protect every other line. Lemma 5 prevents an illegal early entry into the target column and ensures eventual acquisition unless play ends sooner. No active switch is used.

### 5.3 The second player at even heights

For even $H\ge2$, use the pairing mechanism of Allis [1, §2.2]. Pair columns $\{1,2\}$ and $\{3,4\}$. Reply to the opening by taking the partner's bottom square, an active switch. The initial pair has odd heights and odd capacities; the other pair has even heights and even capacities. Apply Lemma 6.

In the other adjacent pair, $F$ occupies only odd rows. A diagonal uses opposite row parities in adjacent columns, so no $F$ diagonal is possible; this pair also excludes even-row horizontals. In the initial pair, apart from the opening bottom stone, $F$ occupies only even rows before the transfer. Hence higher odd-row horizontals are excluded, while the opening $S$ stone blocks the bottom row. After a fill, the filled initial column has permanent $S$ stones in rows three, five, and so on, preserving the higher odd-row blocks.

The only possible adjacent $F$ pair is at the bottom of its opening column, then covered or ceiling-capped when $H=2$. No vertical four arises. The reasoning applies before the reply to every $F$ move. Thus the strategy is non-losing, using at most one active and one passive switch.

### 5.4 The first player at even heights: outside waiting

Assume even $H\ge4$ and open at $(1,1)$. If the first $S$ reply is in column one, reply at $(4,1)$ and use Section 5.5. Otherwise use the outside waiting family

$$[F(SF)^a,\varnothing,\varnothing,(SF)^d],\qquad a,d\ge0.$$

The initial state has $a=d=0$, with the just-mentioned exceptional first reply handled separately. During outside waiting, $a\ge1$ implies $d\ge1$: a later visit to column one requires a previous visit to column four. Cover in column four and in column one whenever it has not filled. Column four has even height and cannot be filled by $S$; column one has odd height and may fill. Empty middle columns and alternating outside words exclude first wins. Finite capacity forces one of three exits.

If $S$ enters $(2,1)$, add $F$ in column one:

$$[F(SF)^aF,S,\varnothing,(SF)^d].$$

This is legal because the former height of column one is odd and less than even $H$. It is one active switch. The only potential exception $(2,2)$ has its horizontal blocked by $F(1,2)$ when $a=0$, or by $F(4,2)$ when $a\ge1$, since then $d\ge1$. Its rising line and the bottom horizontal and $R_0$ are blocked by $F(1,1)$; the other diagonal is out of bounds. If $a=1$, the newly acquired $(1,4)$ also blocks $D$, so use permanent defence. Otherwise reserve only $(2,3)$, at gap two, to block $D$.

If $S$ enters $(3,1)$, cover at $(3,2)$, directly blocking $D$. All nonempty growable columns are $F$-topped and no exceptions remain, giving permanent defence.

If $S$ fills column one, reply at $(2,1)$. Its full top stone is supported by $F$ and creates no exception. The bottom horizontal and $R_0$ are blocked; reserve only $(2,3)$ for $D$.

Each event itself leaves an empty middle column and cannot be a nonvertical win; vertical wins are also excluded. At both reserved exits the target column is the unique odd-height column; every outside column has even capacity or is full. The opponent cannot fill an outside column, and the target gap is positive and even. Therefore ordinary covering everywhere suffices until target acquisition. Thereafter switch only after fills. Only the column-two exit uses an active switch, and no exit returns to the waiting phase.

### 5.5 The first player at even heights: all-column covering

After the opening $F(1,1),S(1,2)$, play $F(4,1)$, the sole active switch. Cover until an event forces a change. At every $S$ turn the shape is

$$[FS(SF)^a,(SF)^b,(SF)^c,F(SF)^d].$$

The first three heights are even and the fourth odd; only column four can be filled by $S$. The two bottom corners block all bottom lines. The sole actual or potential exception is $(1,3)$. Its third-row horizontal is protected by $(4,3)$, always empty or $F$. Its other valid line is

$$U_1=((1,3),(2,4),(3,5),(4,6)),$$

protected by $(2,4)$, also empty or $F$. A top $S$ run in column one reaches at most two before being covered; elsewhere $S$ stones are separated. Support descent handles the other lines.

If no earlier terminal position occurs, finite capacity forces $S$ to fill column four. It is then

$$F(SF)^{H/2-1}S,$$

with odd rows $F$ and even rows $S$. Stop if the board is full; otherwise choose the following reply. The seven rows are disjoint and exhaustive.

| Conditions | Reply and continuation |
|---|---|
| $H=4$ | Any legal move, then permanent defence; $U_1$ is out of bounds. |
| $H\ge6,\ a=0$ | Take $(1,3)$, eliminate the potential exception, then permanent defence. |
| $H\ge6,\ a\ge1,\ b\ge2$ | Any legal move, then permanent defence; $(2,4)=F$ blocks $U_1$. |
| $H\ge6,\ a\ge1,\ b\le1,\ c=2$ | Take $(3,5)$, blocking $U_1$, then permanent defence. |
| $H\ge6,\ a\ge1,\ b\le1,\ c\le1$ | Add $F$ at $(3,2c+1)$; reserve only $(3,5)$. |
| $H\ge6,\ a\ge1,\ b=1,\ c\ge3$ | Take $(2,3)$, winning immediately on $D$. |
| $H\ge6,\ a\ge1,\ b=0,\ c\ge3$ | Take $(2,1)$; reserve the winning target $(2,3)$. |

For $a\ge1$ the exception $(1,3)$ is actual, but its horizontal is permanently blocked by $(4,3)=F$, leaving only $U_1$. When $c\le1$, the gap to $(3,5)$ after the reply is $4-2c$, positive and even; when $c=2$, the target is acquired directly. When $c\ge3$, the three squares $(1,4),(3,2),(4,1)$ of $D$ really are $F$. A second-column height of two gives an immediate win; at height zero occupy its bottom first and wait for the winning third square. The square $(2,4)$ needed by $U_1$ lies above that winning target and cannot be acquired by $S$ first.

All specified replies land at row at most five, within $H\ge6$. In the two waiting exits the target column is the unique odd-height column; all others are even-height or full, so covering suffices until acquisition. Then enter permanent defence or stop with a win.

Every reply in the table follows $S$ filling column four and is passive, including immediate wins. The only active switch was the opening move to column four. This family and Section 5.4 are alternative branches; their budgets must not be added.

### 5.6 Genuinely infinite height

There is no ceiling and hence no passive switch. The first player opens in any fixed column and then always covers. The second player occupies only even rows in the opening column and only odd rows in the other three. A horizontal four must use all four columns and cannot satisfy these parities. Among the other three columns are two adjacent ones, both with only odd-row second-player stones, excluding a diagonal four. Covering excludes vertical fours. The active budget is zero.

The second player answers the opening at the bottom of its adjacent partner in the pairing $\{1,2\},\{3,4\}$, then always covers. The pre-transfer argument of Section 5.3 applies: the other adjacent pair excludes diagonals and even-row horizontals; the initial pair excludes higher odd-row horizontals; the opening second-player stone blocks the bottom row; vertical runs stay short. Covering never becomes illegal. The active budget is one.

Any first win would occur at a finite time, but these fixed invariants protect every finite prefix. This is a direct infinite-height proof, not a limit of finite-height strategies.

## 6 Passive counts and total upper bounds

Each passive reply follows the opponent filling a distinct column. A full column can never be played again. Once all $w$ columns are full there is no reply, so a player has at most $w-1$ passive switches in any legal play.

Combining this with one active switch gives at most four total switches at width four. Section 4 and Section 5.3 give the stronger bound two for the second player. Infinite-height counts have no passive component. A trajectory using four switches in the particular first-player construction shows only that this construction can attain its bound, not that every non-losing strategy needs four.

## 7 Exact counterstrategies against zero active budget

### 7.1 A uniform second-player lower bound

Let $H\ge2$, or let height be infinite. If the second player never switches actively, the first player successively takes the bottom squares of columns one, two, three, and four. The first three moves leave their columns nonfull, forcing covers in row two. Before the fourth first-player move neither player has four stones. That move completes the bottom horizontal and ends play immediately.

Thus every non-losing second-player strategy has worst-case active budget at least one. There is no free passive choice before the loss. At $H=2$, a second-player cover itself fills a column, but this does not give that player another free reply.

### 7.2 Scope of the even-height first-player lower bound

Let $H=2m$, $m\ge2$. A zero-active first player must cover whenever the second player's last column remains nonfull, but may make any history-dependent legal choice after a fill. Reflection reduces all openings to column one or column two. The following traps handle both and verify legal reachability, absence of an earlier first-player win, and all passive alternatives.

### 7.3 An exterior opening

After $F(1,1)$, the second player makes $m$ covered moves in column two, $m-1$ in column four, and $m-1$ in column one, then fills the top square of column one. Every move in the covered rounds leaves room for the forced cover. The resulting first-player turn is

$$[F(SF)^{m-1}S,\ (SF)^m,\ \varnothing,\ (SF)^{m-1}].$$

Throughout preparation column three is empty, excluding nonvertical wins, and columns alternate, excluding vertical wins. The position is therefore genuinely reachable without earlier termination.

Columns one and two are full. The second player owns $(1,4),(2,3),(4,1)$ on $D$ and needs only $(3,2)$. If the first player enters column three, it must take $(3,1)$; $S(3,2)$ wins immediately. If it enters column four, it must take $(4,H-1)$; $S(4,H)$ fills that column, leaving only $(3,1)$, again followed by the winning $(3,2)$.

The first player cannot win in between. While column three is empty no nonvertical four exists, and the new first-player stone in column four creates a run of at most two. On entering column three's bottom square, the bottom horizontal is blocked by second-player bottom stones, that square belongs to no valid diagonal four, and no vertical four exists. Both possible passive choices lose.

### 7.4 An interior opening

After $F(2,1)$, make exactly two covered second-player moves in column one, producing $SFSF$; do not raise it further. Fill column three with $m$ covered rounds, give column four one covered round, then give column two $m-1$ covered rounds and fill its top square. The resulting first-player turn is

$$[SFSF,\ F(SF)^{m-1}S,\ (SF)^m,\ SF].$$

Every prescribed covered move leaves its original column nonfull. At $H=4$, the fourth square of column one is filled by the first player, not by a second-player move granting free choice.

No win occurs during preparation. Vertical words alternate. Since column four has height two, only the first two horizontals need checking and both are mixed. A falling line ending at $(4,1)$ contains $F(1,4)$ and $S(4,1)$. One ending at $(4,2)$ needs the empty $(1,5)$. Rising lines need a higher square of column four. The final preparation position has no four, hence neither does any prefix.

Columns two and three are full. For $H=4$, column one is also full. If the first player enters column four, it takes $(4,3)$ and $S(4,4)$ completes $R_0$, whose other stones $(1,1),(2,2),(3,3)$ are all $S$.

For $H\ge6$ the other option is to enter column one. The second player keeps replying in that column until filling it. Above row four, the extension consists of $FS$ pairs, so $(1,6)$ remains empty or $S$. Until the second player fills the column, the zero-active constraint forces the first player to continue there. Finite capacity eventually forces the first player into column four, yielding the same win at $(4,4)$.

There is no earlier first-player win during this delay. Vertical runs have length at most two, at rows four–five of column one or rows two–three of column four. A possible second-row horizontal is blocked by $S(2,2)$; a third-row horizontal is blocked by $S(1,3)$. A first-player line cannot use $S(4,1)$. A falling line ending at $(4,2)$ contains $S(2,4)$; one ending at $(4,3)$ contains $(1,6)$, which is empty or $S$, or is out of bounds at $H=4$. A rising line ending in row two or three of column four starts below the floor, and other rising lines need still-empty higher squares.

If the second player wins earlier, stop with that win. Otherwise the finite sequence reaches its win at $(4,4)$. The preparation height of column one must be exactly four: filling it in advance at larger heights could change $(1,6)$ and create a first-player falling four. This is a mathematical requirement of the trap.

### 7.5 Conclusion of the lower bound

Section 7.3 covers exterior openings and Section 7.4 interior openings; reflection covers all four columns. At every even height at least four, no zero-active first-player strategy is non-losing. The construction defeats the entire zero-active strategy class, not merely one greedy passive rule or a finite set of heights.

## 8 Assembly and what optimality does not assert

Sections 4–5 give fixed non-losing strategies and active upper bounds for every case. Section 7 gives the matching positive lower bounds; all zero entries are optimal by nonnegativity. Theorem 2 follows, and Theorems 1 and 3 follow from the constructions and Section 6.

If both players use their respective non-losing strategies, neither can be the first winner. Finite play therefore ends in a full-board draw. Infinite-height play continues without a win, which is a draw by definition. Moreover, each strategy protects against every opposing strategy, so the claim is about the game-theoretic value, not just one particular self-play trajectory.

The resource identity unifies target accounting, and at most one active deviation from covering suffices in all cases. Geometry still determines when to spend that deviation, where to play it, and how to transfer after a fill. The two even-height first-player waiting families retain different safety arguments. Optimal active budget does not imply optimal total count, minimum number of targets or controller states, or a shortest possible proof.

## 9 Formalization and reproducibility

### 9.1 Model and history semantics

The supplied project uses a standalone finite four-column model with relative colors $P,Q$. Its budget semantics distinguishes the free first-player opening from replies, checks every legal opponent move for a first win or a full board, and charges an actual winning reply. It never repairs an opponent win after the fact.

The module *HistoryBudget.lean* defines legal reachable prefixes and proves *budgetSafe_iff_historyBudget*. The construction *historyController* can store the complete column history; its policy function has no finite-memory or computability restriction. Consequently the lower bounds apply to arbitrary history strategies, not just a particular finite controller.

### 9.2 Verified results and limits

| Result | Main source | Scope of this acceptance |
|---|---|---|
| One shared non-losing rule, both roles, all finite heights | *UniformFour/FirstRoot.lean*, *SecondRoot.lean* | Parametric theorems accepted |
| Exact active budgets, upper and lower bounds | *FirstExact.lean*, *SecondExact.lean* | Parametric theorems accepted |
| Reachable histories and exact history budgets | *HistoryBudget.lean*, *HistoryRoots.lean* | Equivalence and root theorems accepted |
| Capacity release and two-odd-column transfer | *ReserveArithmetic.lean* | Arithmetic lemmas accepted |
| General multi-target lemma and total-switch bounds | Sections 2 and 6 | Paper proofs |
| Draws below four columns and at genuinely infinite height | *proof/Narrow* | Separately compiled and kernel-replayed; active budgets remain paper proofs |
| Equivalence between the Covering and Narrow board models | Between the two projects | Not formalized |

The two exact roots are *UniformFour.U1.first_exact_history_budget* and *UniformFour.U1.second_exact_history_budget*. Their values are those in Theorem 2. The formal upper bound uses the fixed shared response function of the companion algorithm paper. We do not claim that it makes the same move at every history as every allowed choice in Sections 4–5; the mathematical constructions and the formal rule independently attain the same exact active budget.

### 9.3 Acceptance and auxiliary checks

The project uses Lean 4.34.0-rc2; [3] describes the prover, while the precise toolchain is fixed by the attached receipts. Only libraries shipped with Lean are needed, with no Mathlib or large enumeration certificates. All 55 source modules compiled. The axiom closures of 14 selected declarations contain only *propext*, *Classical.choice*, and *Quot.sound*. A trust-zero import replay of *Audit* checked all transitive local imports and exited successfully. Source and compiled-artifact SHA-256 hashes matched the build receipt before and after replay.

Separately, a newly written coordinate checker tested the first-player traps at even heights four through 200 and all four openings, giving 396 instances, and the second-player trap at heights two through 200, giving 199. The supplied reference-rule checker was rerun for heights zero through twelve in both roles: 83,429 states and 238,014 opponent edges. That rerun reused the supplied implementation and added instrumentation; it was not a new independent implementation. Seventy boundary cases also compared the actual Lean response with the reference response. Finite checks detect implementation and boundary errors; the all-height conclusions come from parametric proofs.

From the repository root, run:

~~~sh
python tools/verify_proof.py
python tools/verify_proof.py --build --replay
~~~

The first command checks published source hashes and acceptance receipts; it does not run Lean. The second builds and kernel-replays the 55-module *proof/Covering* project. Install the version in its *lean-toolchain* and set *LEAN_BIN* if needed. Each Lean process uses all detected logical CPUs.

The separate *proof/Narrow* project supplies finite-width-one-to-three and infinite-height-width-one-to-four draw theorems. Its four mathematical modules and audit entry were freshly compiled, six selected axiom closures satisfied the same whitelist, and a trust-zero import replay succeeded. It needs the pinned Mathlib dependencies. Once these are installed, run *python tools/verify_proof.py --supporting --build --replay*. No equivalence between the two board models has been formalized. Full instructions and the source manifest are in *docs/verification.md* and *audit/*.

## 10 Target economy and remaining questions

Reply legality and line blocking are separate obligations. Once a single terminal target protects the only unresolved line and has a legal waiting argument, no further candidate reservation is needed at that exit. Each reserved even-height first-player exit therefore uses one target, and total remaining capacity supplies its termination argument.

The odd-height second player may still owe two separate diagonal blocks. Each obligation must retain a protector; acquiring one target does not discharge the other obligation. This distinction identifies when a reservation can be released.

What is proved optimal is the defined active-switch cost. Minimum total count, target count, controller size, and proof length are different questions. A further formal task is to relate the two supplied board models through representations, legal drops, first-win stopping, and strategies. The companion paper addresses implementation separately. None of these four-column results determines the five-column game.

## References

[1] L. Victor Allis. *A Knowledge-based Approach of Connect-Four: The Game is Solved: White Wins*. Master's thesis, Vrije Universiteit Amsterdam, Report IR-163, 1988. Especially §§2.2, 6.1, 7.1. [Full text](https://tromp.github.io/c4/connect4_thesis.pdf).

[2] Yoshiaki Yamaguchi, Kazunori Yamaguchi, Tetsuro Tanaka, Tomoyuki Kaneko. Infinite Connect-Four Is Solved: Draw. In *Advances in Computer Games*, LNCS 7168, 2012, pp. 208–219. [doi:10.1007/978-3-642-31866-5_18](https://doi.org/10.1007/978-3-642-31866-5_18).

[3] Leonardo de Moura, Sebastian Ullrich. The Lean 4 Theorem Prover and Programming Language. In *Automated Deduction – CADE 28*, LNCS 12699, 2021, pp. 625–635. [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

[4] GPT. *A Uniform Response Algorithm and Alternating-Segment Compression for Four-Column Gravity Connect Four*. Companion algorithm paper, 8 November 2026. [PDF](https://github.com/wugang6812/narrow-connect-four/blob/main/papers/algorithm-en.pdf).
