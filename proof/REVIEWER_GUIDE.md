# Supplement S1: reviewer guide

Paper: *Lean-Verified Draw Strategies for Narrow Connect Four*.
Author: GPT. Proof baseline: 5a1c02e.

## What is supplied

The `Connect4Proof` directory is copied byte-for-byte from the source package
in the accepted September 2026 archive. It includes 69 specially audited
modules, the shared `Connect4Proof/Basic.lean`, the complete certificate
definitions, generation/checking scripts, original audit records and pinned
dependencies. This is not the separate 6-by-7 first-player-win project.

The source-only ZIP excludes the compiled Lean distribution and Mathlib
cache. It is therefore not a self-contained offline executable environment.
The corresponding author retains a complete Windows offline archive.

## Result entry points

Read Appendix A of the paper, then:

- `experiments/NarrowBoards.lean`: widths at most three, every finite height.
- `experiments/FourColumnsFinal.lean`: four columns, every positive even height.
- `experiments/FourColumnsOddFinal.lean`: actual roots supplied, every positive
  odd height and every finite height including zero. Do not substitute the
  earlier `OddAssembly` theorem that still takes a root-bundle hypothesis.
- `experiments/InfiniteNarrowBoards.lean`: a fixed strategy is chosen outside
  the universal finite-horizon quantifier.

The first-win guard must be read before defender replies. The odd control
game has capacity seven but scoring height six for BOTH players. Control
fullness does not imply real fullness. `odd_control_lift` supplies the
unbounded odd-height argument; finitely many tested real heights do not.

## Evidence and reproduction

The historical reports are `reports/narrow_review/audit.json` (nine modules),
`reports/narrow_odd/lean/audit.json` (60 modules), and
`reports/narrow_odd/replay/audit.json` (60 full replays, not an available-only
run). `lean_source_review.json` records the fourteen roots. Original absolute
paths in receipts are historical provenance, not a required installation
location. The axiom whitelist is propext, Classical.choice and Quot.sound.

For the tested offline Windows arrangement, request the full archive and run
its `快速验收.ps1`. The verifier has `--replay-all` and `--rebuild` modes;
the latter can take hours. Do not describe the default quick check as a
full rebuild. Keep the original acceptance receipts when doing new checks.

For a fresh source build, install the exact version in `lean-toolchain`,
respect `lake-manifest.json`, and obtain the corresponding Mathlib cache.
The minimal lakefile's default target is only `Connect4Proof.Basic`;
plain `lake build` alone is NOT an audit of the experiment modules.
The original builder/replay scripts document import order and kernel checks
but retain Windows-specific toolchain paths, which need adaptation on other
platforms. No newly tested cross-platform turnkey build is claimed here.

## September 28 manuscript revision

This revision changes exposition, bibliographic distinctions and navigation,
not the accepted Lean statements or certificates. A fresh comparison against
the stored source receipts matched all 69 audited modules. This is a hash
and report check, not a new full compilation or kernel replay.

## Rights and disclosures

Retain the third-party notices in the extracted project. Packaging itself
does not grant a new license for original material. Any public deposition
license will be chosen explicitly by the author. The paper discloses
substantial AI assistance; AI output and automated prose review are not
additional mathematical axioms or independent human peer review.
