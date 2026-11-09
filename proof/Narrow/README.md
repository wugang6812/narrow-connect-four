# Narrow widths and genuinely infinite height

The four mathematical source files preserve their accepted source bytes:

- experiments/NarrowBoards.lean: widths one to three at all finite heights.
- experiments/InfiniteNarrowBoards.lean: one fixed strategy protects every
  finite prefix at widths one to four with no ceiling.
- experiments/FourColumns.lean and Connect4Proof/Basic.lean: required model
  definitions and proof dependencies.

NarrowAudit.lean imports these files and checks six selected theorem axiom
closures. The retained source headers describe the time the sources were
written; current compilation/replay acceptance is recorded in ../../audit/.

Install the version in lean-toolchain and obtain the dependencies fixed by
lake-manifest.json, including the corresponding Mathlib compiled cache.
From the repository root:

~~~sh
python tools/verify_proof.py --supporting --build --replay
~~~

The optional --dependencies-from PATH flag reuses a prepared project's
identically pinned dependency cache after checking its revisions. Local modules
are still compiled into this project's separate build directory. Each Lean
process uses all detected logical CPUs. No shared compilation lock is used.

The inherited Lake default target is Basic only; plain lake build does not
check these result modules. Use the command above.

This is a separate model from proof/Covering. The fixed-strategy infinite
quantifier is not obtained by taking a limit of finite-height strategies.
