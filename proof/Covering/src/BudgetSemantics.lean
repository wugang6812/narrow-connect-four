import SafetyKernel

/-!
U1 budget interface. Local validation records accompany this copy.
This is a conservative budget enrichment of UniformFour.RoundSafe, not a proof
of U1's upper or lower bounds. No root theorem is postulated here.
-/
namespace UniformFour.U1
open OddHeight OddHeight.Player

/-- `post` is the board AFTER the opponent's actual move, BEFORE our reply.
An own winning reply is charged; no cost is assessed for an absent reply. -/
def activeCost (H : Nat) (post : Board) (last reply : Col) : Nat :=
  if reply ≠ last ∧ Legal H post last then 1 else 0

/-- Zero active cost forces cover precisely when the old column remains legal.
This says nothing about the arbitrary choice after an opponent-filled column. -/
theorem zero_cost_forces_cover {H : Nat} {post : Board} {q c : Col}
    (available : Legal H post q) (zero : activeCost H post q c = 0) : c = q := by
  apply Classical.byContradiction
  intro different
  simp [activeCost, different, available] at zero

/-- The first player's initial placement must be made separately, with no debit.
For the second player the initial board is empty, so their opening reply IS
charged. The stop ordering matches RoundSafe exactly. -/
def BudgetRoundSafe {S : Type} (H : Nat) (f : Controller S) :
    Nat → Nat → Board → S → Prop
  | 0, _, b, _ => ¬ Wins H b Q
  | k + 1, budget, b, s =>
      ¬ Wins H b Q ∧
      (Wins H b P ∨ Full H b ∨
        ∀ q, Legal H b q →
          ¬ Wins H (drop b q Q) Q ∧
          (Full H (drop b q Q) ∨
            ∃ c next,
              f b q s = some (c, next) ∧
              Legal H (drop b q Q) c ∧
              activeCost H (drop b q Q) q c ≤ budget ∧
              BudgetRoundSafe H f k
                (budget - activeCost H (drop b q Q) q c)
                (drop (drop b q Q) c P) next))

def BudgetSafe {S : Type} (H : Nat) (f : Controller S)
    (budget : Nat) (b : Board) (s : S) : Prop :=
  ∀ k, BudgetRoundSafe H f k budget b s

/-- Budget safety cannot hide a loss or an illegal/missing response. -/
theorem forget_budget_round {S : Type} {H : Nat} {f : Controller S}
    (k : Nat) {budget : Nat} {b : Board} {s : S}
    (h : BudgetRoundSafe H f k budget b s) : RoundSafe H f k b s := by
  induction k generalizing budget b s with
  | zero => exact h
  | succ k ih =>
      refine ⟨h.1, ?_⟩
      rcases h.2 with win | full | moves
      · exact Or.inl win
      · exact Or.inr (Or.inl full)
      · apply Or.inr
        apply Or.inr
        intro q hq
        rcases moves q hq with ⟨safeQ, full | response⟩
        · exact ⟨safeQ, Or.inl full⟩
        · rcases response with ⟨c, next, selected, legal, _, tail⟩
          exact ⟨safeQ, Or.inr ⟨c, next, selected, legal, ih tail⟩⟩

theorem forget_budget {S : Type} {H : Nat} {f : Controller S}
    {budget : Nat} {b : Board} {s : S}
    (h : BudgetSafe H f budget b s) : Safe H f b s :=
  fun k => forget_budget_round k (h k)

#print axioms zero_cost_forces_cover
#print axioms forget_budget
end UniformFour.U1
