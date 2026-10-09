# Verifying Narrow Connect Four

There are three different checks: browser rules, preserved proof evidence, and a fresh Lean build. Their results should be reported separately.

## Browser rules

Run `node --test tests/engine.test.cjs tests/bot.test.cjs` with Node.js 20 or later. This exercises the game engine independently of its interface. The browser test script is `tools/test_browser.py`; it needs Python Playwright plus an available Chromium installation. Supply a different executable with `--browser /path/to/chromium` on other systems. It performs local interaction tests and generates browser test receipts.

The computer core is C compiled to WebAssembly. Its standard-board Black policy is exported from a separate accepted proof archive; see [the bot guide](bot.md). Search on other positions is bounded. Neither the browser interface nor all searched choices are certified by the narrow-board Lean theorem.

## Preserved proof evidence

Run `python tools/verify_proof.py` from the repository root with Python 3.10 or later. No external Python package is needed. The checker verifies all 231 files in the distribution, including its anonymized editorial guide, all 69 source hashes in the original receipts, completion of the nine-module earlier audit and the sixty-module odd audit, the sixty-module full replay, and rejection of the three negative tests. It also constructs the seventy-module local import order.

These checks confirm the bytes and historical records. They are not a new kernel run. The original reports remain in:

- `proof/Connect4Proof/reports/narrow_review/audit.json`
- `proof/Connect4Proof/reports/narrow_odd/lean/audit.json`
- `proof/Connect4Proof/reports/narrow_odd/replay/audit.json`

Some original reports and scripts contain historical Windows paths. Their presence records provenance, not a requirement that your machine use those paths.

## Fresh compilation and replay

Install the exact version in `proof/Connect4Proof/lean-toolchain`: Lean **4.34.0-rc2**. The Mathlib revision is **cecebc3014fd27da46b2899d7639ea643a444a51**, with other dependencies pinned in the checked-in `lake-manifest.json`. Fetch these dependencies and the matching Mathlib compiled cache using Lake and Mathlib's cache tooling before compiling the local proofs. Preserve the pinned revisions; replacing them with a current release constitutes a separate port.

Then, from this repository's root:

```sh
python tools/verify_proof.py --print-order
python tools/verify_proof.py --build
python tools/verify_proof.py --replay
```

Pass `--lake /path/to/lake` if Lake is not on PATH. The builder runs `lake env lean`, verifies the Lean version, compiles the shared Basic and all 69 accepted modules in dependency order, and checks the final theorem axiom output. Generated files go to the extracted project's `.lake/build/lib/lean`. Fresh logs go to `audit/local-proof-check`; original audit records are not overwritten.

Replay checks all 69 accepted modules with Lean's own replay API in a fresh process per module. It is not a separate implementation of the Lean kernel, and it requires the compiled artifacts and dependencies. The copied replay entry point retains its Apache 2.0 notice. A full build or replay can take substantial CPU time and memory; it is not run by the lightweight default command or by the default GitHub workflow.

The new generic wrapper's receipt and dependency-order mode has been tested locally. Fresh Windows offline checks are also available in the author's complete original archive. A fresh cross-platform full build using this wrapper has not yet been accepted; report your actual build and replay results if you exercise those modes.

The original archive-specific verifier and builder scripts are preserved under `proof/`. The complete offline toolchain and compiled Mathlib cache are not part of this small public repository. The archived project's default `lake build` target is only `Connect4Proof.Basic`, so that command alone does not compile the experiment theorem chain.

## Trust and mathematical scope

The standard axiom whitelist is `propext`, `Classical.choice`, and `Quot.sound`. The accepted final odd-height theorem supplies the actual certificate roots. The earlier assembly theorem with an `OddRootBundle` parameter is an intermediate result, not the final unconditional theorem.

The control game scores only the bottom six rows for both players. Its seventh row is a capacity marker. The real board can have remaining space after the control board is full. The lift checks whether the opponent has won before making a defender reply. These distinctions are necessary to the unbounded-height result.

Lean validates the encoded statements and their proofs. Historical originality, the match between definitions and intended game rules, and the natural-language exposition require separate scrutiny. The paper explains and attributes the earlier mathematical results.
