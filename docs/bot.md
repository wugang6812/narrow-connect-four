# The C computer opponent

Search and playing-policy lookup are written in `game/bot.c`. The same source can run as a native command-line program or as WebAssembly. The browser uses a worker so the interface stays responsive; resetting, undoing or switching modes cancels outstanding computation.

## Difficulty levels

| Level | Behaviour |
|---|---|
| Easy | Immediate wins and a one-ply own-shape heuristic; no automatic opponent-threat blocking |
| Normal | Iterative deepening with a longer search allowance |
| Super hard | The preserved standard-board first-player policy where applicable, otherwise a larger search allowance |

Easy uses a single-ply heuristic. Normal and Super hard have search allowances of 150 ms and 1,800 ms, with completed-iteration limits of 4 and 24 half-moves. Forced defensive replies can extend a horizon. The transposition table is bounded. Standard 7-column, 6-row positions use bitboards and immediate-threat pruning adapted from this project's existing Python solver; other sizes use the same rules and a window evaluation.

The bot uses the last completed iteration when it reaches its budget. It is a strong opponent, not a guarantee of optimal play on every arbitrary position. Completed small endgames are searched to their terminal outcomes. Tactical and completed small-board results are tested against independent game rules and minimax.

## The preserved standard-board winning policy

The author's separate accepted standard-board archive proves that Black wins from the empty 7-column, 6-row board by starting in the middle column. Its canonical strategy has **2,503,146 nodes, 5,619,953 reply edges and 329,912 reflected edges**. The compact browser policy preserves selected Black moves, all White replies and reflection flags. It omits board coordinates because the path can be reconstructed from the move history.

The exporter matches the original data hash to the accepted archive manifest and checks every selected move, legal reply and reflected board correspondence. The decoder follows the four roots and their reflections. Source and export hashes are in `audit/standard-policy-export.json`.

Super hard uses this policy when the computer is Black and the history follows its middle-column opening and subsequent replies. It therefore has the accepted first-player winning strategy on that path. Playing White, importing an arbitrary position, or changing Black's prescribed moves can leave that policy. The C bot then searches; it does not claim a certified second-player strategy for all such positions.

The complete standard-board Lean proof is a separate artifact. This repository includes its derived **playing policy**, with provenance and full board-edge checks. The narrow-board paper's non-losing strategies have not all been translated into this bot.

The policy loads only when needed. Its gzip payload is about 15.5 MiB and decodes to about 48.5 MiB. It works from extracted local files and static websites. The browser checks SHA256 before passing it to C. Modern WebAssembly, workers and gzip decompression support are needed. If the policy cannot load, the bot searches instead and reports that fallback.

## Rebuild WebAssembly

With Clang and LLD supporting the WebAssembly target:

```sh
python tools/build_bot.py --clang /path/to/clang --lld /path/to/ld.lld
```

The freestanding build needs no Emscripten, C library or npm package. Its only imported function provides the clock. Supplied `bot.wasm` and `bot-module.js` were built from the checked-in source; hashes and compiler version are in `audit/bot-build.json`.

## Run the native console bot

With a C compiler and standard C library:

```sh
cc -O3 game/bot.c -o bot
python tools/unpack_policy.py
./bot 6 7 3 "4,1" audit/standard-policy.bin
```

Arguments are rows, columns, difficulty 1–3, a comma-separated sequence of **1-based column choices**, and an optional decoded policy file. JSON output contains a 1-based chosen column and search statistics. Negative columns indicate invalid or terminal input. Black starts.

To reproduce export from the original complete archive:

```sh
python tools/export_standard_policy.py /path/to/standard-board-archive
```

The exporter uses accepted data already on disk; it performs no game-tree search or Lean rebuild. It creates a compact policy, gzip asset and receipt. Original C bot code and the author's derived policy data are MIT licensed. Lean/Mathlib and replay-utility licenses remain in force.
