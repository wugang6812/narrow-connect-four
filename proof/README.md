# Formal proofs

The two projects cover complementary parts of the mathematical paper.

| Project | Results | Dependencies |
|---|---|---|
| [Covering](Covering/) | Four columns, every finite height; a shared non-losing rule; exact active-switch budgets and complete-history semantics | Lean 4.34.0-rc2, bundled libraries only |
| [Narrow](Narrow/) | One to three columns at finite heights; fixed strategies at genuinely infinite height for one to four columns | Same Lean version, pinned Mathlib |

The projects use distinct board models. Their formal equivalence is not proved.
The mathematical paper explains the game rules and how the conclusions fit
together; neither model's theorem is silently substituted for the other's.

Read [the verification guide](../docs/verification.md) for commands, source
hash checks, fresh compilation and trust-zero replay. No compiled toolchain,
Mathlib cache, or large finite-strategy enumeration is included.

The axiom whitelist is propext, Classical.choice, Quot.sound.
The complete generic multi-target resource lemma, total-switch upper bounds,
and the compressed engine's refinement and cost are not accepted Lean roots.
