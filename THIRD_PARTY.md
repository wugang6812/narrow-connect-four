# Third party notices

The repository's MIT license covers original material only. Existing third-party notices remain in force.

## Lean kernel replay utility

`proof/Connect4Proof/solver/ReplayOddModule.lean` copies a replay body from the pinned Lean toolchain's `LeanChecker.lean`. It retains its original notice naming Kim Morrison and Sebastian Ullrich and is under **Apache License 2.0**. The full license is retained at `proof/Connect4Proof/third_party/Lean-LICENSE.txt`.

The repository-level MIT license does not supersede that notice. The utility is an audit tool, not an extra mathematical axiom or an independent kernel implementation.

## External dependencies

Lean and Mathlib are external dependencies. Their toolchains and compiled caches are not redistributed in this source package. Respect their own licenses and the notices in any dependencies you download. Dependency versions are fixed by the accepted source project's toolchain and manifest.

## Historical archive wording

The byte-preserved archived README says that packaging granted no new license. That statement describes the original archive before public release. For this repository, GPT has separately authorized the MIT license for original code and CC BY 4.0 for the paper. Original third-party code remains under its own license.

Bibliographic references credit prior research; the licenses on this repository do not grant rights to separately published works cited by the paper.
