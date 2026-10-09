# Narrow Connect Four

Draw strategies for gravity Connect Four on boards of width **one to four at every finite height**, with a bilingual paper, Lean proof sources, historical verification records and a browser game.

**Author:** GPT.

[中文说明](README.zh-CN.md) · [English paper](papers/paper-en.pdf) · [Chinese paper](papers/paper-zh.pdf) · [Verification guide](docs/verification.md)

## Play the game

Download this repository as a ZIP, extract it, and open **[game/index.html](game/index.html)** in your browser. No installation, server, account or internet connection is needed to play.

The online address, once GitHub Pages is enabled, is:
**https://wugang6812.github.io/narrow-connect-four/game/**

Choose **1–20 rows and 1–20 columns**, two players or a computer with Easy, Normal and Super hard levels, and Black or White when playing the computer. Black moves first. A piece falls to the lowest empty square in its column. The first horizontal, vertical or diagonal line of at least four pieces wins; a full board without a winner is a draw. A win on the last square takes precedence over a draw.

Mode, side and difficulty selections apply immediately; resizing starts a new game. You can undo, switch between English and Chinese, export a JSON move record, or import a record to replay it. Imported records are checked for legal columns, gravity and immediate termination. The browser saves the current game locally when storage is available. Large boards scroll horizontally on small screens.

The computer is written in C and runs as WebAssembly in a worker. Easy develops its own shapes; Normal blocks immediate threats and searches a few moves ahead; Super hard uses a deeper search and, when playing Black along its prescribed standard-board opening, the accepted first-player winning policy. Other positions are searched within a budget, without a universal optimal-play guarantee. See [the C bot guide](docs/bot.md). A player can lose on a theoretically drawn board by choosing a losing move.

## Mathematical results

| Board | Result in this project |
|---|---|
| Width 1–3, any finite height | Both players have non-losing strategies |
| Width 4, any finite height, even or odd | Both players have non-losing strategies |
| Width 1–4, genuinely infinite height | Fixed strategies prevent a first loss; endless play is a draw by convention |
| Width 5 or more | Outside this paper's classification |

For finite boards, the existence of a non-losing strategy for each player gives a draw under optimal play. It does not make every legal play a draw.

The odd-height construction uses a **seven-row control game in which only the bottom six rows score**, then lifts its certified strategy to all larger odd heights. The lift handles full-column legality, the opponent's first win, and continued real play after the control board is full. Heights one, three and five have separate certificates. The finite certificate material has **39,616 explicit nodes and fourteen roots**.

The paper attributes the classical even-height second-player defence to Allis and the known narrow infinite-board results to Yamaguchi and colleagues. It does not claim priority for the entire classification. The original accepted proof baseline is `5a1c02e`.

## Read and inspect the proof

The accepted source project is in **[proof/Connect4Proof](proof/Connect4Proof)**. Its mathematical source bytes and original reports are preserved; the editorial guide has been anonymized. Main entry points are:

| Statement | Source |
|---|---|
| Widths at most three, all finite heights | [NarrowBoards.lean](proof/Connect4Proof/experiments/NarrowBoards.lean) |
| Four columns, all positive even heights | [FourColumnsFinal.lean](proof/Connect4Proof/experiments/FourColumnsFinal.lean) |
| Four columns, odd and all finite heights, with actual certificate roots supplied | [FourColumnsOddFinal.lean](proof/Connect4Proof/experiments/FourColumnsOddFinal.lean) |
| Infinite-height fixed strategies | [InfiniteNarrowBoards.lean](proof/Connect4Proof/experiments/InfiniteNarrowBoards.lean) |

The original records contain nine earlier audited modules, sixty odd-height build results and sixty full odd-height kernel replays. Their audited axiom whitelist is `propext`, `Classical.choice`, and `Quot.sound`. The shared finite model adds one source, giving seventy local Lean source modules.

Check the preserved source hashes and historical acceptance records with Python 3.10 or later:

```sh
python tools/verify_proof.py
```

This command is a **source and receipt check**, not a new Lean compilation. Fresh compilation and kernel replay require the exact Lean `4.34.0-rc2` toolchain and pinned Mathlib dependencies; follow the [verification guide](docs/verification.md). A default `lake build` in the extracted project builds only the shared Basic module and is not a check of all final results.

## Test the browser game

The game has no npm dependencies. With Node.js 20 or later:

```sh
node --test tests/engine.test.cjs tests/bot.test.cjs
```

Tests include gravity, illegal/full columns, all four line orientations, terminal guards, last-square wins, draws, undo, record replay, and comparison with an independent whole-board winner detector on sampled legal games for all 400 dimension pairs. Browser interaction checks cover import/export, the C computer, storage recovery, keyboard controls and mobile layout. Tests are evidence for the game implementation, not a formal verification of JavaScript.

See [paired difficulty results](docs/selfplay.md) and the complete move records for the latest local self-play run.

## Project contents

- `game/`: offline browser game and standalone rules engine.
- `papers/`: English and Chinese manuscripts, PDFs, typesetting sources and references.
- `proof/`: accepted Lean source package and original verification records.
- `tools/`: public source/receipt checker and optional fresh build/replay entry point.
- `tests/`: game rule tests.
- `audit/`: source-preservation manifest and local game test receipts.

A compact playing policy from the separate accepted 7-column, 6-row first-player-win archive is included for Super hard. The complete standard-board Lean proof, large five-column search checkpoints, full Windows offline toolchains, personal backup settings and editorial correspondence are not included.

## Authorship and tool use

This project is published under the name GPT. Lean checks formal statements under their definitions; historical novelty and natural-language exposition require separate scrutiny. The paper has not been accepted by a journal.

## License and citation

Original game code, original Lean code and original supporting scripts are available under **[MIT](LICENSE)**. The paper and its manuscript sources are available under **[CC BY 4.0](papers/LICENSE.txt)**. Third-party code retains its own notices and licenses; in particular, the copied kernel replay utility remains Apache 2.0. See [third-party notices](THIRD_PARTY.md).

Citation metadata is in [CITATION.cff](CITATION.cff). Cite the paper title *Lean-Verified Draw Strategies for Narrow Connect Four* and author GPT. A GitHub repository is a public research artifact, not a peer-reviewed publication or a DOI.
