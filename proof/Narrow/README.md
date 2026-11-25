# Narrow widths and genuinely infinite height

The eight local modules use pinned Mathlib. The original draw proofs are in
[finite narrow boards](experiments/NarrowBoards.lean) and
[unbounded boards](experiments/InfiniteNarrowBoards.lean). In the unbounded
model the player fixes one strategy before the horizon is chosen.

- [NarrowCost](Completion/NarrowCost.lean) proves the exact zero active budget for both players at finite widths one to three.
- [InfiniteCost](Completion/InfiniteCost.lean) counts switches on histories of the fixed infinite-height strategies.
- [InfiniteExact](Completion/InfiniteExact.lean) proves both optima, including the white zero-budget contradiction by a bottom-row four.

[NarrowAudit](NarrowAudit.lean) imports the local closure and lists ten audited
declarations. Acceptance records are in the repository's audit directory.

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
