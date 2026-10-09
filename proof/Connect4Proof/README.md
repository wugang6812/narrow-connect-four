# Narrow Connect Four: accepted proof sources

This extracted project proves draws for widths 1–4 at every finite height,
and widths 1–4 at infinite height under the endless-play draw convention.
It contains 69 audited modules plus the shared Connect4Proof/Basic.lean.
It does not contain the separate standard 6-row, 7-column winning certificate.

## Offline Windows archive

Use the root 快速验收.ps1 script. It invokes the bundled Python and Lean
directly, with search paths confined to this archive. No network or global
elan installation is needed. The original reports are never overwritten.
The first import from a slow disk can take several minutes.

The verifier also supports --replay-all (all 69 audited modules), or --rebuild
(all 70 local sources into a separate cache, then replay). Rebuilding may take
hours. Neither mode rebuilds third-party Mathlib from source.

## Compact source / arXiv ancillary package

Compiled dependencies and the toolchain are omitted from the compact package.
Install the exact toolchain in lean-toolchain; use the pinned lake-manifest.json.
The minimal lakefile builds the shared Basic module by default. Obtain the
matching Mathlib cache, then compile the experiment modules in import order.
The supplied original odd builder and replay scripts document the dependency
order and kernel checks. They expect the Windows toolchain at
../elan/toolchains/leanprover--lean4---v4.34.0-rc2.
The complete offline archive is the tested turnkey Windows arrangement.

Final entry points:
- experiments/NarrowBoards.lean
- experiments/FourColumnsFinal.lean
- experiments/FourColumnsOddFinal.lean
- experiments/InfiniteNarrowBoards.lean

Historical notes are provenance, not the current acceptance status. The final
odd build/replay reports are complete; all 14 roots are supplied. Both odd and
even heights are included in four_columns_finite_draw.

Proof baseline: 5a1c02e. Mathlib revision:
cecebc3014fd27da46b2899d7639ea643a444a51.
Standard audited axiom whitelist: propext, Classical.choice, Quot.sound.
No new license is granted by packaging; retain third-party license notices.
