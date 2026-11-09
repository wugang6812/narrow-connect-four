
#set document(title: "A Uniform Response Algorithm and Alternating-Segment Compression for Four-Column Gravity Connect Four", author: "GPT",
    date: datetime(year: 2026, month: 11, day: 8))
#set page(paper: "a4", margin: (x: 22mm, top: 21mm, bottom: 21mm),
    numbering: "1", number-align: center,
    header: context {
      if counter(page).get().first() > 1 {
        text(size: 7.5pt, fill: rgb("#666666"))[Four-column gravity Connect Four | Uniform algorithm and compression]
        v(2pt)
        line(length: 100%, stroke: 0.35pt + rgb("#b0b0b0"))
      }
    })
#set text(font: ("Times New Roman", "Liberation Serif", "SimSun", "Noto Serif CJK SC"), size: 10.5pt, lang: "en")
#set par(justify: true, leading: 0.56em, spacing: 0.65em)
#set heading(outlined: true)
#show heading.where(level: 1): it => block(above: 0pt, below: 12pt)[
  #align(center, text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 20pt, weight: "bold", hyphenate: false, it.body))
]
#show heading.where(level: 2): it => block(above: 15pt, below: 8pt, sticky: true)[
  #text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 13.5pt, weight: "bold", it.body)
]
#show heading.where(level: 3): it => block(above: 10pt, below: 5pt, sticky: true)[
  #text(font: ("Times New Roman", "Liberation Serif", "Microsoft YaHei", "Noto Sans CJK SC"), size: 11.5pt, weight: "bold", it.body)
]
#show link: set text(fill: rgb("#244f6b"))
#set table(inset: 5pt, stroke: 0.35pt + rgb("#aab3bc"))
#show table: set text(size: 8.5pt)
#show raw: set text(font: ("Consolas", "DejaVu Sans Mono", "SimSun", "Noto Serif CJK SC"), size: 8.6pt)

= A Uniform Response Algorithm and Alternating-Segment Compression for Four-Column Gravity Connect Four
<a-uniform-response-algorithm-and-alternating-segment-compression-for-four-column-gravity-connect-four>
#align(center)[GPT #linebreak() 8 November 2026]

=== Abstract
<abstract>
We organize covering strategies for four-column gravity Connect Four
into one deterministic response rule for both players and every finite
height. The rule reads the complete current board, the controlled color,
and the opponent's last column. It stores no phase, reserved target, or
active-switch counter, and does not search a future game tree. Its proof
separates geometric position certificates, covering closure, full-column
exits, and the initial uncertified states. The precise selection order
matters. A shared executable Lean 4 function has been proved non-losing
in both roles, with an optimal active-switch budget and an explicit
bridge to legal-history prefix semantics. A further paper proof bounds
the total number of maximal alternating segments in every legal
candidate board by nine. A three-stream interval intersection replaces
segment-combination enumeration for the winning-target subproblem with a
linear scan. The complete compressed engine, its refinement to the
accepted response function, and its cost theorem have not been
formalized; finite comparison tests do not establish these claims.

Keywords: strategy certificate; position invariant; alternating segment;
interval intersection; Lean 4.

=== Relationship to the mathematical paper
<relationship-to-the-mathematical-paper>
The companion mathematical paper \[4\] proves empty-board draws at
widths one to four and exact active-switch budgets. The present paper
concerns uniform execution on finite four-column boards and compressed
representations. Pairing, Claimeven, and even-capacity release have
precedents in Allis \[1\]. The present implementation chooses a move
through current-position checks rather than future-tree search or a
height-indexed strategy table.

Infinite and semi-infinite games have their own literature \[2\]. This
finite algorithm does not accept an infinite capacity or assign a parity
to it. The executable definition and proofs are supplied in the
repository \[5\], together with the interval-scan implementation and
finite checks \[6\].

== 1 Game, cost, and algorithm input
<game-cost-and-algorithm-input>
=== 1.1 Legal play and first-win stopping
<legal-play-and-first-win-stopping>
The board has four columns and a finite height $H gt.eq 0$. Rows start
at one at the floor. A move drops a stone into the lowest vacant square
of a nonfull column. Horizontal, vertical, and either diagonal fours
win. Play stops at the first win or a full board; the losing player has
no corrective reply. Height zero is an immediate draw.

We use $F \, S$ for the first and second players and write column words
bottom to top. For local certificates, $P$ is the responding player and
$Q$ the opponent. Out-of-board lines and targets are excluded. A fixed
non-losing policy must handle every legal opponent continuation, not
merely a self-play run.

=== 1.2 Switch cost
<switch-cost>
A reply in a different column is active when the opponent's last column
remains nonfull, and passive when the opponent just filled it. Covers
have zero cost; the first player's opening is free. A reply that wins is
still charged before termination. A non-losing policy's budget is its
worst-case active count over all opponent continuations, minimized over
all such policies when discussing optimality.

=== 1.3 Inputs and lack of phase memory
<inputs-and-lack-of-phase-memory>
For $H > 0$ the first player opens at $\( 1 \, 1 \)$. Thereafter the
same response function serves both roles. It reads the board after the
opponent's move, the controlled color, and the previous move's column
$c$. Its row $r$ is the current height of $c$.

All targets, exceptions, and certificates are recomputed from the
current board. No extra phase label, old target, old certificate, or
used-budget counter is stored. “Local” here means a current-board and
one-candidate-move check, not a fixed-radius neighborhood. Certificates
below apply after a hypothetical or actual $P$ reply, with $Q$ to move.

== 2 Support exceptions and common safety conditions
<support-exceptions-and-common-safety-conditions>
=== 2.1 Support descent
<support-descent>
#strong[Lemma 1.] If a nonbottom nonvertical $Q$ four has a $P$ stone
immediately below every stone, it cannot be a first $Q$ win.

#strong[Proof.] Translating the line down one row gives a $P$ four. All
its stones existed before the last $Q$ move, by gravity.
$square.stroked.tiny$

=== 2.2 Complete exceptions and unresolved lines
<complete-exceptions-and-unresolved-lines>
In a nonterminal candidate position, let $E$ contain every nonbottom $Q$
stone directly above $Q$, and the next empty square of every nonfull
$Q$-topped column. The second type is a potential support exception. Do
not add a square above a full column. Require that each nonfull top run
of $Q$ has length at most two.

Let $U$ be the valid nonvertical four-cell lines meeting the bottom row
or $E$ and containing no $P$ stone. Other nonvertical lines are already
blocked or excluded by support descent. At heights at most three the two
bottom diagonals do not exist. An already won or full board is handled
as terminal, not passed off as a nonterminal certificate.

=== 2.3 What covering preserves
<what-covering-preserves>
A $Q$ move followed by a cover creates no exception outside the old $E$:
a potential exception may become actual and must remain recorded. A $Q$
move filling a column, followed by a $P$ stone elsewhere, also creates
no new exception outside $E$. A top $Q$ run grows from at most two to at
most three before being capped by $P$ or the ceiling. Existing blockers
persist. Consequently the newly relevant unresolved lines form a subset
of the old ones.

What still needs proof is that every old unresolved line remains
protected against the opponent's move itself, before the reply. The next
certificates provide this protection.

== 3 Three decidable certificate classes
<three-decidable-certificate-classes>
Write $h_j$ for the current height of column $j$. Every certificate
includes the common nonterminal, boundedness, and top-run conditions of
Section 2.

=== 3.1 Class A: permanent safety or one target
<class-a-permanent-safety-or-one-target>
Accept class A if one of the following holds:

- #strong[A0:] $U$ is empty.
- #strong[A1:] There is an in-board empty target $\( j \, g \)$ with
  positive even gap $g - h_j$, even total capacity outside column $j$,
  and every line of $U$ passes through $\( j \, g \)$.
- #strong[A2:] The target has the same capacity and gap conditions, and
  three fixed current $P$ stones would form a four with a $P$ stone at
  the target. Every line of $U$ passes through some square in column $j$
  at or above row $g$.

A2 is a geometric test, not permission to drop a stone over empty
squares. Its other three stones must already exist. All unresolved lines
must be protected by the same target.

#strong[Lemma 2 (A safety and closure).] From an A-certified position
the opponent cannot win first on the next move. If another reply is
needed, a legal cover yields another A certificate or a safe terminal
result. If the opponent fills its column, some legal reply has the same
property.

#strong[Proof.] For A0, bottom and exception lines are permanently
blocked; support descent and the top-run condition handle the rest. A
cover or any legal post-fill move preserves these facts.

For A1 and A2, a positive even target gap prevents $Q$ from reaching the
target: a visit reaches at most the square below it, with room for a
cover. The target and the higher squares in its column remain empty
until $P$ acquires it. Thus the protected lines cannot complete first.
Covers preserve the gap parity or acquire the target.

An opponent fill cannot occur in the still-pending target column. It
occurs outside, whose positive even capacity before the move was at
least two. There is therefore a legal outside reply. Such a reply
preserves the target and all fixed stones. Before acquisition retain the
certificate; on A1 acquisition all unresolved lines become blocked,
giving A0; on A2 acquisition $P$ wins. Any earlier $P$ win or a
full-board draw also ends the process safely. $square.stroked.tiny$

The implementation need not remember the old target. The old certificate
ensures safety of the next opponent move and existence of a good
successor; the selected successor's certificate takes over.

=== 3.2 Class B: zero or two odd-capacity columns
<class-b-zero-or-two-odd-capacity-columns>
Let

$ R = { j : H - h_j upright(" is odd") } . $

Let $G$ contain all current $P$ squares and every empty in-board square
$\( j \, g \)$ at a positive even gap from $h_j$. Such an empty square
remains empty or becomes $P$ under repeated covering.

A B certificate requires:

+ $\| R \|$ is zero or two.
+ Every line in $U$ meets $G$.
+ If $R = { f \, t }$, check #strong[both ordered choices]
  $\( f \, t \)$ and $\( t \, f \)$: every line of $U$ meets the set
  consisting of $G$ outside the prospective receiving column $t$,
  together with $\( t \, H \)$.

The receiving column's top square is currently empty because its
capacity is positive and odd. Condition 3 is not optional: its old
even-gap guards may cease to be guards after an unpaired transfer.

#strong[Lemma 3 (B safety and closure).] A B certificate excludes a
first opponent win. Covering preserves B or reaches a safe terminal
state. If the opponent fills a column, there were two odd-capacity
columns, and replying in the other one is legal and yields a B
certificate with $R = emptyset$, or a safe terminal state.

#strong[Proof.] With no odd capacities, every playable column has at
least two vacancies at a $Q$ turn, so covering is always possible. The
guards remain empty or become $P$. With two odd capacities, complete
covering rounds preserve $R$ and the guard conditions; unresolved lines
can only disappear.

The first column filled by $Q$ is some $f in R$, and that move is still
protected by the old $G$. The other column $t$ has positive odd
capacity. A $P$ move there makes every remaining capacity even. Old
guards outside $t$ persist; old guards in the now-full $f$ have become
fixed $P$ stones. Guards in $t$ may be lost, but $\( t \, H \)$ becomes
either a $P$ stone or an empty square at positive even gap. Condition 3
supplies precisely the surviving protection for every unresolved line.
No new exception appears, so B holds with no odd capacities.
$square.stroked.tiny$

No remembered choice of $R$ or “already transferred” flag is required.

=== 3.3 Class C: empty middle columns
<class-c-empty-middle-columns>
C requires all four capacities to be odd, both middle columns empty, and
both exterior columns to be alternating even-length words
$\( Q P \)^a \, \( Q P \)^d$, with $a \, d gt.eq 0$ and $a + d > 0$.
These conditions imply odd $H gt.eq 3$.

#strong[Lemma 4 (C safety and exits).] Covering a non-filling outside
move preserves C or safely terminates. When the opponent first enters a
middle column or fills an outside column, there is a legal B-certified
or terminal reply. The event move itself is safe.

#strong[Proof.] Before the event both middle columns are empty, and
after it at least one remains empty. No nonvertical four is possible;
exterior words alternate and a newly entered middle column contains one
stone, excluding vertical fours.

On entry into column two, reply at the bottom of column three, and
conversely. The middle heights become one and the odd capacities are the
exterior pair. The bottom horizontal contains $P$. The sole potential
exception is the second square above the opponent's middle bottom stone;
its horizontal is blocked by the second square of a nonempty exterior
word. The falling and rising bottom diagonals are guarded by
$\( 2 \, 3 \)$ and $\( 3 \, 3 \)$. These guards lie outside either
possible receiving exterior column, satisfying both B exits. At $H = 3$
the diagonals are absent.

When column one fills, reply at $\( 3 \, 1 \)$. For $H gt.eq 5$ the
fixed $P \( 1 \, 4 \)$ blocks the falling bottom diagonal and
$\( 3 \, 3 \)$ guards the rising one. The odd capacities are columns two
and four, neither containing that guard. A full $Q$-topped column adds
no out-of-board exception. Reflect for a fill in column four, replying
at $\( 2 \, 1 \)$. At $H = 3$ only the bottom horizontal remains
relevant and is blocked. All replies enter an empty middle column and
are legal. $square.stroked.tiny$

This event table proves existence of qualified replies; the algorithm
does not store it as a phase table.

=== 3.4 Role parity
<role-parity>
After a first-player reply the total number of stones, and hence
vacancies, is odd. Thus the number of odd-capacity columns is odd,
excluding both B and C. A first-player certificate must be A. After a
second-player reply the total vacancy count is even and all three
classes can be checked.

The even outside-capacity condition of A1/A2 implies odd target-column
capacity for the first player and even target-column capacity for the
second. The implementation checks the same condition in both roles
instead of branching on this consequence.

== 4 One deterministic selection order
<one-deterministic-selection-order>
=== 4.1 Qualified replies
<qualified-replies>
After the opponent's move, first stop if it wins or fills the board.
Otherwise, hypothetically drop $P$ in each legal column $j$. Call $j$
qualified if the candidate wins for $P$, is a no-win full board, or is
nonterminal and has an A, B, or C certificate. A hypothetical move is
not an actual move, and never repairs an existing opponent win.

=== 4.2 Priority rules
<priority-rules>
Let $c \, r$ be the opponent's last column and row.

#strong[Step 1.] If $c$ is still playable and either its cover is
qualified or both bottom corners $\( 1 \, 1 \) \, \( 4 \, 1 \)$ already
belong to $P$, cover in $c$. Playability is required for both
alternatives.

#strong[Step 2.] Otherwise, if qualified replies exist, choose an
immediately winning one if possible, breaking ties to the left. If none
wins immediately, prefer qualified columns whose capacity before the
reply is odd, then choose the leftmost.

#strong[Step 3.] If neither earlier step selected a move, then on
reachable histories $c$ is still playable. Cover if $r gt.eq 3$. If
$r lt.eq 2$, score each legal candidate by the number of bottom lines
already containing $P$ after it; maximize this score, preferring a cover
on ties and then the leftmost column.

To totalize the function on other nonterminal legal inputs, Step 3 first
checks whether $c$ is full and then returns the leftmost legal column if
so. The proof shows this fallback is unreachable from the specified
openings. There is no test of history compatibility in the executable
rule.

The only separate initialization is the first player's move at
$\( 1 \, 1 \)$ for $H > 0$. The remaining response code is identical for
both roles.

=== 4.3 Why the order matters
<why-the-order-matters>
A qualified cover or the two-corner condition can take precedence over
an immediate win elsewhere. This is deliberate: a non-losing strategy
need not take every opportunity to win, and a winning switch still costs
an active move. In the even-height uncertified phase, priority covering
prevents a second active switch.

The fallback score counts permanently blocked bottom lines, ignoring
out-of-board diagonals. It does not estimate future win probabilities.
The reference checker enumerates current lines and targets; it is not a
recursive game solver. With constant-time cell access, a straightforward
checker considers $O \( H \)$ lines and $O \( H \)$ targets and can make
a decision in $O \( H^2 \)$ time. This is an estimate under that access
model, not a proved machine-cost bound for the supplied Lean reference
implementation.

== 5 First-player correctness for all finite heights
<first-player-correctness-for-all-finite-heights>
=== 5.1 After certification
<after-certification>
A first-player certificate is A. Lemma 2 excludes the next opponent
first win. A legal cover is qualified and Step 1 chooses it. After a
column fills, a qualified reply exists and Step 2 chooses one. Its own
certificate, or safe terminal result, suffices regardless of which
witness was used to prove existence. Once certified, the first player
never switches actively again.

=== 5.2 Small and odd heights
<small-and-odd-heights>
Height zero terminates immediately. At heights one, two, and three, the
opening blocks the bottom horizontal; there are no diagonal or vertical
fours and no opponent exceptions, giving A0.

For odd $H gt.eq 5$, the opening blocks the bottom horizontal and rising
bottom diagonal. The only unresolved line is

$ D = \( \( 1 \, 4 \) \, \( 2 \, 3 \) \, \( 3 \, 2 \) \, \( 4 \, 1 \) \) . $

The target $\( 3 \, 2 \)$ has gap two and even outside capacity
$3 H - 1$, giving A1. Thus all these first-player cases start certified
and use no active switch.

=== 5.3 The first uncertified even-height family
<the-first-uncertified-even-height-family>
For even $H gt.eq 4$, an uncertified first-player state may have the
form

$ \[ F \( S F \)^a \, emptyset \, emptyset \, \( S F \)^d \] \, #h(2em) a \, d gt.eq 0 \, quad a gt.eq 1 arrow.r.double d gt.eq 1 . $

The root has $a = d = 0$. Only the first bottom corner belongs to $F$.
Every opponent move leaves an empty middle column, excluding nonvertical
wins, and exterior opponent stones are separated.

If $S$ enters column two, adding $F$ in column one is a qualified
witness. The resulting potential exception $\( 2 \, 2 \)$ has its
horizontal blocked by $\( 1 \, 2 \) = F$ if $a = 0$, or by
$\( 4 \, 2 \) = F$ when $a gt.eq 1$ and hence $d gt.eq 1$. Its other
relevant line and the bottom rising line are blocked by
$\( 1 \, 1 \) = F$. If $a = 1$, the new $\( 1 \, 4 \)$ blocks $D$ and
gives A0; otherwise $\( 2 \, 3 \)$ is an A1 target of gap two with even
outside capacity. The reply is legal because the old first-column height
is odd and less than even $H$.

If $S$ enters column three, covering at $\( 3 \, 2 \)$ blocks $D$ and
gives A0. If $S$ fills column one, replying at $\( 2 \, 1 \)$ gives A1
with target $\( 2 \, 3 \)$\; no new exception comes from the supported
full top stone. These are existence witnesses, not requirements that the
selector pick that exact column.

For an ordinary non-filling outside move, a qualified cover or other
qualified reply may enter the certified regime early. If none exists,
Step 3 has the following exhaustive cases:

- At opponent row at least three, covering preserves the family.
- A first move at $\( 4 \, 1 \)$ occurs here with $a = d = 0$. Every
  candidate still blocks the same two bottom lines, so the cover wins
  the tie, giving $d = 1$.
- A move at $\( 1 \, 2 \)$ with $d gt.eq 1$ admits no additional
  bottom-diagonal blocker in one legal reply; scores tie and the cover
  gives $a = 1$.
- The remaining low-row event is $S \( 1 \, 2 \)$ at the root. Only
  $F \( 4 \, 1 \)$ blocks all three bottom lines, so Step 3 chooses it
  and enters the second family.

At height four, Step 2 may already find a qualified reply and need not
follow the last transition. Thus remaining uncertified either uses
covers or spends one active switch to reach the two-corner family. Any
other active reply directly enters certification.

=== 5.4 The two-corner uncertified family
<the-two-corner-uncertified-family>
The second family is

$ \[ F S \( S F \)^a \, \( S F \)^b \, \( S F \)^e \, F \( S F \)^d \] . $

The first three heights are even and the fourth odd, and both bottom
corners belong to $F$. Only column four can be filled by $S$. The bottom
lines are blocked. The sole actual or potential exception is
$\( 1 \, 3 \)$: its horizontal is protected by $\( 4 \, 3 \)$, empty or
$F$, and its other valid line

$ U_1 = \( \( 1 \, 3 \) \, \( 2 \, 4 \) \, \( 3 \, 5 \) \, \( 4 \, 6 \) \) $

is protected by $\( 2 \, 4 \)$, empty or $F$. Vertical runs stay short,
and support descent excludes other first wins.

When the opponent's column remains nonfull, the two-corner clause forces
a cover, even if another column offers a win. It preserves the family or
enters A; no second active switch is spent. If neither termination nor
certification occurs earlier, finite capacity forces a fill in column
four. Stop if the board is full. Otherwise the following table supplies
a qualified reply:

#figure(
  align(center)[#table(
    columns: (50%, 50%),
    align: (auto,auto,),
    table.header([Conditions], [Witness],),
    table.hline(),
    [$H = 4$], [Any legal reply gives A0; $U_1$ is invalid.],
    [$H gt.eq 6 \, med a = 0$], [$\( 1 \, 3 \)$ eliminates the potential
    exception, giving A0.],
    [$H gt.eq 6 \, med a gt.eq 1 \, med b gt.eq 2$], [Any legal reply
    gives A0; $\( 2 \, 4 \) = F$.],
    [$H gt.eq 6 \, med a gt.eq 1 \, med b lt.eq 1 \, med e = 2$], [$\( 3 \, 5 \)$
    blocks $U_1$, giving A0.],
    [$H gt.eq 6 \, med a gt.eq 1 \, med b lt.eq 1 \, med e lt.eq 1$], [Add
    in column three; $\( 3 \, 5 \)$ is an A1 target.],
    [$H gt.eq 6 \, med a gt.eq 1 \, med b = 1 \, med e gt.eq 3$], [$\( 2 \, 3 \)$
    wins immediately on $D$.],
    [$H gt.eq 6 \, med a gt.eq 1 \, med b = 0 \, med e gt.eq 3$], [$\( 2 \, 1 \)$
    gives A2 with winning target $\( 2 \, 3 \)$.],
  )]
  , kind: table
  )

These disjoint cases exhaust the parameters. When $a gt.eq 1$, the
actual exception's horizontal is blocked by the filled column's
$\( 4 \, 3 \) = F$. In the $e lt.eq 1$ case the new gap to
$\( 3 \, 5 \)$ is $4 - 2 e$, positive and even, and the outside
capacities are even. In the $e gt.eq 3$ cases,
$\( 1 \, 4 \) \, \( 3 \, 2 \) \, \( 4 \, 1 \)$ are fixed $F$ stones,
while the square $\( 2 \, 4 \)$ required by $U_1$ lies above the winning
target. All specified replies lie at row at most five and fit in
$H gt.eq 6$.

The table establishes that Step 2 has a qualified option; the actual
selector still uses its common priority rule. All these replies follow a
filled column and are passive.

=== 5.5 Induction
<induction>
Small and odd heights start certified. At even heights, each uncertified
reachable state belongs to one of the two families. Every opponent move
is safe before the reply; the selector then preserves a safe family or
enters certification, and a full-column event always has a qualified
response. Finite capacity precludes endless waiting. The first-player
rule is non-losing.

The first family can spend an active switch only to enter certification
or the second family. The second family and the certified regime spend
no more. The active budget is at most one, and is zero at odd heights
and heights at most three.

== 6 Second-player correctness for all finite heights
<second-player-correctness-for-all-finite-heights>
=== 6.1 Initial qualified replies exist
<initial-qualified-replies-exist>
The following cases prove existence for the shared checker; they are not
runtime opening tables.

At $H = 1$, the opening column is full. Any other bottom reply blocks
the only horizontal and gives A0; the two remaining empty columns also
give B.

At odd $H gt.eq 3$, an exterior opening can be covered, giving C. Since
a qualified cover has first priority, the algorithm chooses it.

For an odd-height opening in column two, $\( 1 \, 1 \)$ is a B witness
with $R = { 3 \, 4 }$. The bottom horizontal and rising diagonal are
blocked. The falling diagonal is protected by $\( 2 \, 3 \)$, outside
$R$. The potential exception $\( 2 \, 2 \)$ has its horizontal protected
by $\( 3 \, 2 \)$ and $\( 4 \, 2 \)$\; whichever odd column receives a
later transfer, the other guard survives. Reflection handles column
three.

For positive even height, reply at the bottom of the opening column's
partner in ${ 1 \, 2 } \, { 3 \, 4 }$. The initial two columns have odd
capacity and the other adjacent pair has even capacity. It suffices to
check openings in columns one and two, with reflection covering the
rest.

After $F 1 \, S 2$, the bottom horizontal is blocked. The two bottom
diagonals can be guarded by $\( 4 \, 4 \)$ and $\( 3 \, 2 \)$. The
potential exception $\( 1 \, 2 \)$ has its horizontal guarded by
$\( 3 \, 2 \)$ and its rising line by $\( 3 \, 4 \)$. These guards lie
in empty even-capacity columns, outside either transfer column. After
$F 2 \, S 1$, the bottom horizontal and rising diagonal are blocked;
$\( 3 \, 2 \)$ guards the falling diagonal and, with $\( 4 \, 2 \)$, the
exceptional horizontal. The other relevant exceptional diagonal is
already blocked at $\( 1 \, 1 \)$. At $H = 2$ only horizontals require
inspection. Thus B holds in every even-height case.

=== 6.2 The selector remains certified
<the-selector-remains-certified>
In A and B, non-filling moves have qualified covers, selected by Step 1,
and filling moves have qualified replies, selected by Step 2. In C,
ordinary outside moves have qualified covers, while a first middle entry
or outside fill has a B witness by Lemma 4.

The exterior bottom stones of a C state are the opponent's, so the
two-corner clause cannot force the second player to cover wrongly after
a middle entry. In A and B a cover was already qualified. Before the
initial second-player move there are no second-player corners. Therefore
the second player is certified after its first reply and never invokes
Step 3. Each opponent move is first checked safe under the old
certificate; only then is closure used.

=== 6.3 Why the total count remains at most two
<why-the-total-count-remains-at-most-two>
After every second-player reply the total remaining capacity is even. On
first entering A or B there are at most two odd-capacity columns. To see
this, at a positive even-height opening, a cover leaves all capacities
even but no second-player bottom stone; the unblocked bottom horizontal
has no positive-even-gap bottom target, so neither A nor B accepts, and
C does not apply. A qualified reply must therefore switch, leaving two
odd capacities.

At an odd-height interior opening, a cover leaves four odd capacities,
no second-player bottom stone, and a nonempty middle column; A, B, and C
all fail. Thus a qualified opening again switches and leaves two odd
capacities.

An odd-height exterior opening enters C by covering. Ordinary C covers
retain four odd capacities and no second-player bottom stone. A0 fails;
an A target has odd outside capacity, so A1/A2 fail; B has the wrong
number of odd columns. A middle-entry cover similarly leaves four odd
capacities and no bottom block, and is not C; the other empty middle
column also excludes an immediate winning cover. Qualified event replies
must switch, turning two odd capacities even. An outside fill followed
by an off-column reply also leaves two. At height one the first reply
leaves two odd empty columns.

After entering A or B, ordinary covers preserve every capacity parity.
If the opponent fills a column, the old odd set had two members, and
there is a unique other odd-capacity column. B guarantees a qualified
reply there. A0 allows it as well. For A1/A2, even total and even
outside capacity imply that the target column has even capacity, so the
other odd column is outside the target and gives a safe reply.

If no immediate winning reply exists, Step 2's odd-capacity preference
therefore chooses that unique odd column, leaving all capacities even.
No later opponent move can fill a playable column before a cover. If a
winning reply is selected instead, play stops and no further count is
needed.

An active switch can occur at the opening or, after an exterior opening
cover, at the first C middle-entry event; these do not occur on the same
path. The opening or C exit contributes at most one total switch,
followed by at most one passive switch in A/B. Thus the second player's
active budget is at most one and its total count at most two. At $H = 1$
the opening switch is passive. Choosing an arbitrary qualified post-fill
move could retain safety while invalidating this particular count proof.

== 7 The uniform-response theorem
<the-uniform-response-theorem>
#strong[Theorem 5.] For every finite $H gt.eq 0$, with immediate
termination at $H = 0$ and the first-player opening at $\( 1 \, 1 \)$
otherwise, the shared response function of Section 4 is non-losing for
each player against every legal opponent continuation. Each active
budget is at most one. Total switches are at most four for the first
player and two for the second.

#strong[Proof.] Non-loss and active counts follow from Sections 5-6.
Each passive reply follows a distinct newly full column; when all four
are full there is no reply, so the first player has at most three
passive switches. The stronger second-player bound was proved in Section
6.3. When both non-losing strategies are used, finite capacity forces a
no-win full-board draw. $square.stroked.tiny$

#strong[Theorem 6.] This algorithm attains the minimum worst-case active
budget among all non-losing strategies:

#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,right,right,),
    table.header([Height], [First player], [Second player],),
    table.hline(),
    [$0 \, 1$], [0], [0],
    [$2 \, 3$], [0], [1],
    [Odd $H gt.eq 5$], [0], [1],
    [Even $H gt.eq 4$], [1], [1],
  )]
  , kind: table
  )

This is an optimality statement about active cost, not total switches,
formula length, or the number of certificates.

== 8 Interface to the lower-bound proof
<interface-to-the-lower-bound-proof>
The companion mathematical paper \[4, §7\] proves that a second-player
zero-active strategy loses at every $H gt.eq 2$, by successive
first-player bottom moves in all four columns. It also proves the
first-player lower bound at every even $H gt.eq 4$, with separate
exterior-opening and interior-opening traps. Those traps allow all
history-dependent passive replies after fills; they do not merely defeat
a chosen greedy rule. In the interior trap, preparation of column one to
exactly height four is essential.

These complete parametric lower bounds, together with our upper bounds,
prove Theorem 6. They remain in the mathematical paper rather than being
duplicated here. The Lean history-budget equivalence makes the
strategy-class scope explicit, including arbitrary complete-history
policies.

== 9 Conditions that cannot simply be deleted
<conditions-that-cannot-simply-be-deleted>
=== 9.1 A counterexample to omitting ordered B exits
<a-counterexample-to-omitting-ordered-b-exits>
At $H = 3$, consider the first-player turn

$ \[ F F \, med S F S \, med S F S \, med emptyset \] . $

It is reached legally by
$F 1 \, S 2 \, F 1 \, S 3 \, F 2 \, S 2 \, F 3 \, S 3$, without an
earlier win. For the second-player certificate, the odd-capacity columns
are one and four, and the only unresolved line is row two. The empty
$\( 4 \, 2 \)$ has gap two and is in the old $G$. A checker omitting B's
ordered-exit condition would accept.

But $F$ now fills column one, $S$ transfers to $\( 4 \, 1 \)$, and
$F \( 4 \, 2 \)$ completes the second-row horizontal. The old guard was
lost when the transfer entered column four. The correct condition asks
for protection outside column four or at its top $\( 4 \, 3 \)$ and
rejects this position.

=== 9.2 Safe choices need not produce the same trace
<safe-choices-need-not-produce-the-same-trace>
For the legal height-three prefix $F 1 \, S 2 \, F 2 \, S 2$, column two
has just filled. A selector taking the leftmost qualified reply picks
$\( 1 \, 2 \)$\; the rule of this paper prefers an odd-capacity column
and picks $\( 3 \, 1 \)$. Both are permanently safe, but they are
different moves.

Safety alone therefore does not establish trace equivalence between
selectors. We prove this rule's safety and budget, without claiming
equality with every allowed choice in the companion mathematical
construction.

== 10 Alternating segments and a linear target scan
<alternating-segments-and-a-linear-target-scan>
=== 10.1 At most nine segments in a candidate board
<at-most-nine-segments-in-a-candidate-board>
A maximal alternating segment is a maximal interval of a column whose
adjacent stones have different colors. Equal-color neighbors create a
boundary. Thus total segment count $K$ equals the number of nonempty
columns plus the number of equal-color adjacency pairs; segments are not
monochromatic runs.

#strong[Proposition 7.] Consider legal alternating gravity play from an
empty width-$w$ board, $w > 0$. A controlled player has so far made
$A lt.eq a$ actual active and $B$ actual passive switches. Immediately
after a nonterminal opponent move, every legal candidate reply produces
at most

$ K' lt.eq 2 w - 1 + 2 a $

maximal alternating segments.

#strong[Proof.] The controlled player's equal-color pairs number at most
$A + B$: covering creates none, and a free opening creates none. Charge
each opponent equal-color pair to the controlled reply immediately after
its lower stone was played and left uncovered. That column was nonfull,
since a later upper stone exists, so the charged reply was active.
Different pairs have different lower stones and hence different charged
replies. This includes any pair formed by the opponent's latest move.
Therefore, before the candidate,

$ K lt.eq w + 2 A + B . $

Each passive switch corresponds to a distinct full column, and a reply
is still required, so $B lt.eq w - 1$. If $B lt.eq w - 2$, the candidate
adds at most one segment and

$ K' lt.eq w + 2 a + \( w - 2 \) + 1 . $

If $B = w - 1$, at least $w - 1$ columns are already full. The sole
playable column is the opponent's last column, so every legal candidate
covers an opposite-color stone and adds no segment. The same bound
follows. We never impose the actual policy's budget on an unselected
hypothetical candidate. $square.stroked.tiny$

For $w = 4 \, a = 1$, this gives nine. The bound is attained at height
six along the legal sequence of column numbers

```text
1,2,1,1,1,2,2,2,2,2,1,3,3,3,3,4,4,1,3,3,4
```

With $P$ first, its final board is

$ \[ P P Q P P Q \, med Q Q P Q P Q \, med Q P Q P P Q \, med Q P P \] . $

It has nine segments, one active switch, and three passive switches, and
no prefix has ended the game. The supplied coordinate checker verifies
this witness. It is an actual response state and was also a legal
candidate. It prevents a uniform improvement to eight for this rule, but
does not prove that all non-losing strategies need four total switches.

A bound obtained by separately adding a possible opponent segment and a
candidate segment to a post-response estimate is loose. Counting at the
opponent-move boundary and using the number of full columns gives the
sharper bound above.

=== 10.2 A2 targets as interval intersections
<a2-targets-as-interval-intersections>
Fix a target column $j$ of height $h_j$. A target row $g$ satisfies

$ h_j + 2 lt.eq g lt.eq u \, #h(2em) g equiv h_j med \( mod med 2 \) \, $

where $u$ is bounded by $H$ and by the lowest intersection of unresolved
lines with column $j$. If an unresolved line has no such intersection,
this target column cannot protect it. A target at gap at least two
cannot complete a vertical line with three already fixed stones, so only
slopes $delta in { - 1 \, 0 \, 1 }$ need checking.

An alternating segment $\[ l \, r \]$ in another column $i$ contains $P$
stones at one row parity. A target line needs $P$ at
$g + delta \( i - j \)$, so that segment yields the interval

$ \[ l - delta \( i - j \) \, med r - delta \( i - j \) \] $

for $g$, with a specified parity. Filter segments incompatible with
$g equiv h_j med \( mod med 2 \)$. Each of the other three columns now
supplies an ordered disjoint interval stream. Intersect the streams and
the target range using three pointers.

At the current intervals let $L$ be the maximum lower endpoint and $R$
the minimum upper endpoint, including the target range. Round $L$ upward
to the required parity. If the rounded value is at most $R$, return that
target. Otherwise advance an interval with minimum upper endpoint, or
all tied such intervals. No discarded interval can participate in an
omitted solution with a later, higher interval of another stream. Every
pointer moves only forward, giving $O \( K \)$ work for fixed
$j \, delta$\; four columns and three slopes add constant factors.

This replaces cubic enumeration of triples of segments for the A2 target
search. It does not by itself make the complete checker linear:
unresolved-line construction, deduplication, and other certificate
queries remain separate tasks.

=== 10.3 Input model and implementation evidence
<input-model-and-implementation-evidence>
The interval-scan subroutine agreed with independent cellwise
enumeration in 80,020 comparisons, covering exhaustive small column-word
combinations and random taller words. A direct compressed input of
height $10^12$ with only three segments was also checked. These tests
validate the implementation over those inputs; they are not an all-input
refinement proof.

Along an accepted strategy, a constant segment bound permits storage in
a constant number of height-sized words. Reading a raw $H$-row board is
a different task and cannot ignore its input length. A height-sized word
needs $Theta \( log H \)$ bits, so a constant count of word operations
is not a claim of constant bit complexity.

The delivered executable optimization is the A2 interval-scan
subroutine. A complete integrated compressed engine, equivalence of all
its decisions to the accepted reference rule, and a machine-cost theorem
remain unfinished.

== 11 Formal scope and reproduction
<formal-scope-and-reproduction>
=== 11.1 Model, histories, and costs
<model-histories-and-costs>
The project uses a standalone finite four-column model with relative
colors $P \, Q$. The recursive budget semantics checks every legal
opponent move, first-win and full-board stopping, and the actual chosen
reply, including the charge on a winning reply.

The module #emph[HistoryBudget.lean] defines reachable legal prefixes
and proves #emph[budgetSafe\_iff\_historyBudget]. The
#emph[historyController] construction can carry the entire column
history, without a finite-memory or computability assumption on its
policy function. Thus the exact lower bounds are not confined to the
stateless implementation.

=== 11.2 Accepted roots and unfinished components
<accepted-roots-and-unfinished-components>
#figure(
  align(center)[#table(
    columns: (33.33%, 33.33%, 33.33%),
    align: (auto,auto,auto,),
    table.header([Result], [Main source], [Acceptance scope],),
    table.hline(),
    [Shared response, both roles, every finite
    height], [#emph[UniformFour/FirstRoot.lean],
    #emph[SecondRoot.lean]], [Parametric safety accepted],
    [Exact active budgets], [#emph[FirstExact.lean],
    #emph[SecondExact.lean]], [Upper and lower bounds accepted],
    [History semantics and exact history
    budgets], [#emph[HistoryBudget.lean],
    #emph[HistoryRoots.lean]], [Equivalence and roots accepted],
    [Release parity, two-odd transfer, interval
    parity], [#emph[ReserveArithmetic.lean]], [Arithmetic lemmas
    accepted],
    [Nine-segment bound], [#emph[SegmentBoundArithmetic.lean]], [Final
    arithmetic only; event injection and full-column premises remain
    explicit],
    [General multi-target lemma and total-switch bounds], [Companion
    mathematical paper], [Paper proofs],
    [Draws below four columns and at infinite
    height], [#emph[proof/Narrow]], [Separate verified model; not part
    of this finite algorithm],
    [Equivalence between the Covering and Narrow board models], [Between
    the two projects], [Not formalized],
    [Complete compressed engine and its cost], [Section 10], [No full
    refinement or complexity theorem],
  )]
  , kind: table
  )

The exact history roots are
#emph[UniformFour.​U1.​first\_exact\_history\_budget] and
#emph[UniformFour.​U1.​second\_exact\_history\_budget]. The shared
executable response is #emph[UniformFour.​U2.​respond], defined through
the finite checker. Selection order must be preserved to reuse the
proven cost theorem.

=== 11.3 Validation
<validation>
The accepted toolchain is Lean 4.34.0-rc2; \[3\] describes Lean 4, while
exact version and executable hash are fixed by the receipts. The source
uses Lean's bundled libraries, with no Mathlib or large search
certificate. All 55 modules compiled. Fourteen selected axiom closures
contain only #emph[propext], #emph[Classical.choice], and
#emph[Quot.sound]. A trust-zero replay of the complete local import
closure of #emph[Audit] exited successfully. Every source and compiled
artifact matched its recorded SHA-256 before and after replay.

Auxiliary checks include 396 coordinate instances of the first-player
lower bound, 199 of the second-player lower bound, and a rerun of the
supplied reference-rule checker for heights zero through twelve in both
roles, totaling 83,429 states and 238,014 opponent edges. That rerun
reused supplied code; only the added instrumentation and separately
identified new checkers are new implementations. Seventy boundary cases
compare the actual Lean response with the reference rule. None of these
finite tests replaces the parameterized theorem.

From the repository root, run:

```sh
python tools/verify_proof.py
python tools/verify_proof.py --build --replay
```

The first command checks published source hashes and acceptance
receipts; it does not run Lean. The second builds and kernel-replays the
55-module #emph[proof/Covering] project. Install the version in its
#emph[lean-toolchain] and set #emph[LEAN\_BIN] if needed. Each Lean
process uses all detected logical CPUs.

The separate #emph[proof/Narrow] project supplies
finite-width-one-to-three and infinite-height-width-one-to-four draw
theorems. Its four mathematical modules and audit entry were freshly
compiled, six selected axiom closures satisfied the same whitelist, and
a trust-zero import replay succeeded. It needs the pinned Mathlib
dependencies. Once these are installed, run #emph[python
tools/verify\_proof.py --supporting --build --replay]. No equivalence
between the two board models has been formalized. Full instructions and
the source manifest are in #emph[docs/verification.md] and
#emph[audit/].

== 12 Implementation boundaries and next steps
<implementation-boundaries-and-next-steps>
The deliverables are the accepted finite-board reference rule, the
segment-count argument, and the A2 scan subroutine. A complete
compressed implementation is not presented as finished software. The
next refinement should first establish agreement of compressed and
cellwise board access, drops, lines, and certificates; then prove that
the selector returns the same column; finally account for the chosen
machine model.

Order changes require their own checks. Immediate-win priority,
arbitrary qualified full-column transfers, or removal of an ordered-exit
condition may invalidate the established cost or safety proof.
Implementation work in this paper does not change the companion paper's
status as an independent mathematical strategy proof.

#block(breakable: false)[
== References
<references>
\[1\] L. Victor Allis. #emph[A Knowledge-based Approach of Connect-Four:
The Game is Solved: White Wins]. Master's thesis, Vrije Universiteit
Amsterdam, Report IR-163, 1988. Especially §§2.2, 6.1, 7.1.
#link("https://tromp.github.io/c4/connect4_thesis.pdf")[Full text].

\[2\] Yoshiaki Yamaguchi, Kazunori Yamaguchi, Tetsuro Tanaka, Tomoyuki
Kaneko. Infinite Connect-Four Is Solved: Draw. In #emph[Advances in
Computer Games], LNCS 7168, 2012, pp.~208-219.
#link("https://doi.org/10.1007/978-3-642-31866-5_18")[doi:10.1007/978-3-642-31866-5\_18].

\[3\] Leonardo de Moura, Sebastian Ullrich. The Lean 4 Theorem Prover
and Programming Language. In #emph[Automated Deduction - CADE 28], LNCS
12699, 2021, pp.~625-635.
#link("https://doi.org/10.1007/978-3-030-79876-5_37")[doi:10.1007/978-3-030-79876-5\_37].

\[4\] GPT. #emph[Draw Strategies for Gravity Connect Four on One to Four
Columns: Covering Strategies, Optimal Active-Switch Budgets, and Lean
Verification]. Companion mathematical paper, 8 November 2026.
#link("https://github.com/wugang6812/narrow-connect-four/blob/main/papers/paper-en.pdf")[PDF].

\[5\] GPT. #emph[UniformFour: Lean definitions and proofs].
#link("https://github.com/wugang6812/narrow-connect-four/tree/main/proof/Covering")[Source].
\2026.

\[6\] GPT. #emph[Interval scanning and coordinate checks].
#link("https://github.com/wugang6812/narrow-connect-four/tree/main/experiments")[Source].
\2026.

]
