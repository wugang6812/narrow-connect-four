# Verification

The public source package contains a 60-module finite four-column development
and a eight-module supporting development for small widths and infinite height.
Their definitions are separate; a formal bridge between the models is not supplied.

## 1. Source and receipt check

With Python 3.10 or later, from the repository root:

~~~sh
python tools/verify_proof.py
~~~

This checks all 68 local Lean source hashes, the module counts, the recorded
trust-zero results, and 32 selected axiom closures. It performs no new Lean run.
The public records are [source manifest](../audit/proof-manifest.json) and
[verification receipt](../audit/proof-verification.json).

## 2. Fresh four-column build and kernel replay

Install Lean **4.34.0-rc2** as pinned in proof/Covering/lean-toolchain. No Mathlib
is required for this project. Put lean on PATH or set LEAN_BIN to its executable:

~~~sh
python tools/verify_proof.py --build --replay
~~~

The command builds all 60 modules, checks 22 selected axiom closures and 70
runtime response comparisons, then imports the complete local closure with
Lean's trust level set to zero. Axiom use is restricted to propext,
Classical.choice, and Quot.sound. Runtime examples are auxiliary tests; the
all-height conclusions are parameterized proof terms.

Outputs go to proof/Covering/build, logs, replay, audit.json and kernel_audit.json.
They are ignored by Git and do not overwrite published receipts. Each Lean
process uses all detected logical CPUs; no cross-task lock is used.

GitHub Actions runs this build/replay in addition to the source checks and game
tests. Its run log is an additional platform-specific verification record.

## 3. Supporting model

Use the same Lean version, with Mathlib revision
cecebc3014fd27da46b2899d7639ea643a444a51 and the other revisions in
proof/Narrow/lake-manifest.json. Install these dependencies and the matching
Mathlib cache in that project using Lake, then run:

~~~sh
python tools/verify_proof.py --supporting --build --replay
~~~

This compiles eight local modules in dependency order, checks ten selected axiom closures, and replays
the transitive imports at trust zero. Local output stays in proof/Narrow/build
and logs. A prepared project with exactly matching dependency pins can be reused
with --dependencies-from PATH. The default Lake target alone compiles only Basic.

The supplied acceptance receipt includes a fresh local supporting build/replay.
The lightweight GitHub workflow checks its source hashes and receipt, while the
Mathlib-dependent supporting build remains a separately requested check.

## 4. Browser game and auxiliary experiments

~~~sh
node --test tests/engine.test.cjs tests/bot.test.cjs
python tools/check_publication.py
~~~

The game tests cover gravity, legal moves, terminal precedence, replay, undo,
four line directions, the C bot, and sampled games across all 400 dimension
pairs. tools/test_browser.py additionally tests a real Chromium browser via
Playwright; it accepts --browser PATH.

The experiments/ scripts check coordinate traps, the reference policy, the
nine-segment witness, and the A2 interval scan. Their finite results do not prove
an all-height statement or a compressed-program refinement.

## Paper 1 theorem index

| Mathematical statement | Lean entry |
|---|---|
| Finite width four, exact active budgets | [HistoryRoots](../proof/Covering/src/HistoryRoots.lean), both exact history budgets |
| Finite widths one to three, including height zero | [NarrowCost](../proof/Narrow/Completion/NarrowCost.lean), `narrow_finite_exact` |
| No ceiling, fixed strategy for every finite horizon | [InfiniteExact](../proof/Narrow/Completion/InfiniteExact.lean), `narrow_infinite_exact`, `four_infinite_first_exact`, `four_infinite_second_exact` |
| Four columns, first-player total ≤ 4, including winning replies | [TotalSwitch](../proof/Covering/src/Completion/TotalSwitch.lean), `first_total_from_root` and `first_total_zero` |
| Four columns, second-player total ≤ 2 and exact active upper bound for the same policy | [SecondTotal](../proof/Covering/src/Completion/SecondTotal.lean), `second_total_and_active` |
| Nonvertical support descent and permanent defence | [Support](../proof/Covering/src/OddHeight/Support.lean), [Permanent](../proof/Covering/src/OddHeight/Permanent.lean) |
| Protected cells, a reserved cell is taken unless play ends earlier | [ProtectedCells](../proof/Covering/src/Completion/ProtectedCells.lean), `even_distance_protected` and the two single-target theorems |
| Multiple pending targets, safe half-moves, ordinary release and finite resolution | [Reserves](../proof/Covering/src/Completion/Reserves.lean), `multitarget_resource` |
| At most one passive transfer after the two-odd-column rule starts | [TwoOdd](../proof/Covering/src/Completion/TwoOdd.lean), `two_odd_controller` |

Finite four-column histories use the relative roles P and Q. The supporting
project uses Black and White with Black first. Each model proves the results
listed for it directly. The second paper’s full nine-segment event count,
compressed implementation, refinement, and computational cost are separate
from the first paper’s three theorems.
