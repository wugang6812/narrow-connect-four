# Verification

The public source package contains a 55-module finite four-column development
and a five-module supporting development for small widths and infinite height.
Their definitions are separate; a formal bridge between the models is not supplied.

## 1. Source and receipt check

With Python 3.10 or later, from the repository root:

~~~sh
python tools/verify_proof.py
~~~

This checks all 60 local Lean source hashes, the module counts, the recorded
trust-zero results, and 20 selected axiom closures. It performs no new Lean run.
The public records are [source manifest](../audit/proof-manifest.json) and
[verification receipt](../audit/proof-verification.json).

## 2. Fresh four-column build and kernel replay

Install Lean **4.34.0-rc2** as pinned in proof/Covering/lean-toolchain. No Mathlib
is required for this project. Put lean on PATH or set LEAN_BIN to its executable:

~~~sh
python tools/verify_proof.py --build --replay
~~~

The command builds all 55 modules, checks 14 selected axiom closures and 70
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

This compiles Basic, NarrowBoards, FourColumns, InfiniteNarrowBoards and
NarrowAudit in dependency order, checks six selected axiom closures, and replays
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

## Scope

The first paper contains the draw classification and complete mathematical
active-budget lower bounds. The second paper develops the current-board
certificate rule and compression. The accepted finite roots include the exact
budgets and their equivalence to complete-history semantics.

The general multi-target resource lemma, total-switch counts, event injection
for the full nine-segment argument, complete compressed engine, and machine-cost
theorem are not all formalized. The papers state these limits explicitly.
The browser bot is a separate bounded-search implementation; the narrow-board
theorem does not certify every move of that bot.
