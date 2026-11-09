# Four-column covering strategies

55 Lean source modules prove the shared response function non-losing at every
finite height for both player roles, and establish the optimal active budgets.
The first player's opening is free; winning replies are charged; an opponent
first win stops play before a reply.

## Main entry points

- src/HistoryRoots.lean: exact budgets for policies using the complete history.
- src/HistoryBudget.lean: equivalence of recursive budgets and reachable-prefix semantics.
- src/FirstExact.lean and src/SecondExact.lean: upper and lower bounds.
- src/UniformFour/FiniteChecker.lean: the executable shared response function.
- src/UniformFour/FirstRoot.lean and src/UniformFour/SecondRoot.lean: safety.
- src/Audit.lean: complete local import closure and selected axiom declarations.

Only Lean's bundled libraries are required. Install the exact version in
lean-toolchain and expose lean on PATH, or set LEAN_BIN to its executable.

~~~sh
python build.py Audit
python verify.py
~~~

Each process uses the detected logical CPU count. Independent compilations
use isolated outputs without a shared lock; optional psutil enables up to three
workers when sufficient memory is available. Generated build/, logs/, replay/,
audit.json and kernel_audit.json stay local and are ignored by Git.

Published acceptance records are under ../../audit/. The build script checks
the compiler version, source/dependency fingerprints, and artifact hashes before
reusing a result. The verifier checks the complete source closure, selected
axioms, 70 executable response samples, and all transitive imports at trust zero.

This model does not include infinite height or a formal correspondence with
the supporting model. ReserveArithmetic proves arithmetic interfaces, while
SegmentBoundArithmetic proves the numerical end of the nine-segment argument:
its geometric/event-counting premises remain explicit.
