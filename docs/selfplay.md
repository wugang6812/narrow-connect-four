# Computer difficulty self play

This is one paired empty-board tournament on eight representative board sizes. Each difficulty pair played once in each color, for 48 games. Each level participated in 32 games. These boards also guided difficulty tuning; this is a regression sample, not an independent universal strength estimate.

**Dimensions below are rows × columns**: 6 × 7 means seven columns and six rows. Each cell is wins / draws / losses out of four games for that level.

| Board | Easy | Normal | Super hard |
|---|---|---|---|
| 3 × 3 | 0 / 4 / 0 | 0 / 4 / 0 | 0 / 4 / 0 |
| 4 × 4 | 0 / 0 / 4 | 2 / 1 / 1 | 3 / 1 / 0 |
| 6 × 4 | 0 / 1 / 3 | 1 / 1 / 2 | 4 / 0 / 0 |
| 7 × 4 | 0 / 0 / 4 | 2 / 1 / 1 | 3 / 1 / 0 |
| 6 × 7 | 0 / 0 / 4 | 2 / 0 / 2 | 4 / 0 / 0 |
| 8 × 5 | 0 / 0 / 4 | 2 / 0 / 2 | 4 / 0 / 0 |
| 10 × 10 | 0 / 0 / 4 | 2 / 0 / 2 | 4 / 0 / 0 |
| 20 × 20 | 0 / 0 / 4 | 2 / 0 / 2 | 4 / 0 / 0 |

| Level | Wins | Draws | Losses | Win percentage |
|---|---:|---:|---:|---:|---:|
| Easy | 0 | 5 | 27 | 0.00% |
| Normal | 13 | 7 | 12 | 40.62% |
| Super hard | 26 | 6 | 0 | 81.25% |

No lower-level wins over a higher level occurred in this particular run. Draws remain possible, and board geometry and first-player advantage matter. These are not Elo ratings or proofs of difficulty dominance. Time budgets can change the last completed search depth on another machine.

The full move records, timing, search depths and playing-policy usage are in [audit/selfplay.json](../audit/selfplay.json). The earlier trial is retained at [audit/selfplay-v1.json](../audit/selfplay-v1.json); it used the earlier difficulty configuration.

Reproduce the paired tournament with `node tools/selfplay.cjs`. It uses the actual C engine and budgets, not a simulated win probability. No game is prematurely cut off to improve the reported result.
