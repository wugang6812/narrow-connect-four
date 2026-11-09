# Narrow Connect Four

[中文说明](README.zh-CN.md) · [Project website](https://wugang6812.github.io/narrow-connect-four/) · [Play](https://wugang6812.github.io/narrow-connect-four/game/)

Gravity Connect Four on **one to four columns is a draw at every finite height** under optimal play. Both players have fixed non-losing strategies, also on boards with a floor and no ceiling. This repository contains mathematical proofs, exact active-switch budgets, Lean sources, a companion algorithm paper, and a playable rules demonstration.

## Read the papers

| Paper | English | 中文 |
|---|---|---|
| **Draw strategies and optimal active-switch budgets**: finite and infinite heights, upper and lower bounds | [PDF](papers/paper-en.pdf) · [source](papers/paper-en.md) | [PDF](papers/paper-zh.pdf) · [正文](papers/paper-zh.md) |
| **Uniform response algorithm and alternating-segment compression**: certificates, selection order, nine-segment bound and interval scan | [PDF](papers/algorithm-en.pdf) · [source](papers/algorithm-en.md) | [PDF](papers/algorithm-zh.pdf) · [正文](papers/algorithm-zh.md) |

The first paper includes the optimality proofs. Algorithm design and compression are developed in the second. [Typesetting and bibliography](papers/README.md) accompany both.

## Results

| Board | Empty-board outcome |
|---|---|
| Widths 1–3, any finite height | Draw |
| Width 4, any finite height, odd or even | Draw |
| Widths 1–4, genuinely infinite height | Fixed strategies prevent a first win; infinite play is a draw |
| Width 5 or greater | Outside this classification |

For four columns the **minimum worst-case active-switch count** is:

| Height | First player | Second player |
|---|---:|---:|
| 0 or 1 | 0 | 0 |
| 2 or 3 | 0 | 1 |
| Odd, at least 5 | 0 | 1 |
| Even, at least 4 | 1 | 1 |
| Genuinely infinite | 0 | 1 |

An active switch means replying in another column while the opponent's last column remains playable. The first opening stone is free; a winning reply is charged. At widths at most three, both budgets are zero. Active cost differs from game value and total switch count.

The papers credit Allis for classical even-height second-player pairing and discuss the infinite-board work of Yamaguchi and coauthors. No priority claim is made for the entire draw classification.

## Verify the proofs

- [proof/Covering](proof/Covering/): **55 modules**, finite four-column heights, shared response, exact active budgets and full-history semantics. Only Lean's bundled libraries are needed.
- [proof/Narrow](proof/Narrow/): **5 modules**, finite widths 1–3 and genuinely infinite height at widths 1–4, using pinned Mathlib.

Both projects were freshly compiled and imported at trust level zero. Twenty selected axiom closures use only `propext`, `Classical.choice` and `Quot.sound`. Their board models are separate; formal equivalence is not supplied.

With Python 3.10+, check published source hashes and receipts:

~~~sh
python tools/verify_proof.py
~~~

This command does not run Lean. For a fresh finite four-column build and kernel replay, install Lean **4.34.0-rc2**, expose `lean` on PATH or set `LEAN_BIN`, then run:

~~~sh
python tools/verify_proof.py --build --replay
~~~

GitHub Actions runs these checks and the game tests. The Mathlib-dependent supporting project has a separate reproduction command. See the [verification guide](docs/verification.md) and [acceptance receipt](audit/proof-verification.json).

The generic multi-target lemma, total-switch bounds, full event-counting argument for nine segments, and a complete compressed engine with refinement and cost proofs remain outside the accepted formal roots. The papers identify these limits. Finite [experiments](experiments/) are supplementary evidence.

## Play and test

[Play online](https://wugang6812.github.io/narrow-connect-four/game/) or open [game/index.html](game/index.html) locally. Choose 1–20 rows and columns, two human players or a C/WebAssembly computer, and three difficulties. The game works offline, including its standard-board first-player policy.

The game bot is separate from the narrow-board formalization. Its standard 7-column, 6-row policy applies on the supported first-player branch; other positions use bounded search. See [bot details](docs/bot.md) and [self-play results](docs/selfplay.md).

With Node.js 20+:

~~~sh
node --test tests/engine.test.cjs tests/bot.test.cjs
python tools/check_publication.py
~~~

Tests cover gravity, all winning directions, terminal precedence, undo/replay, and sampled games across all 400 dimension pairs. Browser interaction checks use `tools/test_browser.py` with Playwright.

## License and citation

Published under **GPT**. Original code is [MIT](LICENSE); both papers and manuscript sources are [CC BY 4.0](papers/LICENSE.txt). [Third-party notices](THIRD_PARTY.md) remain applicable. Cite using [CITATION.cff](CITATION.cff) or [references.bib](papers/references.bib).

These are research manuscripts and reproducible artifacts, not a claim of journal acceptance or human peer review. Current links remain stable; commits and release tags record changes.
