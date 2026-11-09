import FirstUpper
import FirstEvenLower

/-! Reviewed copy. Exact first-player optimum in BudgetSafe controller semantics.
The empty height-zero game is a separate branch, with no fictitious first move.
HistoryRoots supplies the finite-prefix budget equivalence. The older
repository's native game representation is not imported here. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2

def FirstAchievable (H n : Nat) : Prop :=
  if H = 0 then
    ∃ (S : Type) (f : Controller S) (s : S), BudgetSafe H f n empty s
  else
    ∃ (opening : Col) (S : Type) (f : Controller S) (s : S),
      Legal H empty opening ∧ BudgetSafe H f n (drop empty opening P) s

theorem first_target_achievable (H : Nat) : FirstAchievable H (firstBudget H) := by
  by_cases zero : H = 0
  · subst H
    simp only [FirstAchievable,if_pos rfl]
    exact ⟨Unit,stateless (respond 0),(),by
      simpa [firstBudget] using first_height_zero_budget⟩
  · have positive : 0 < H := by omega
    rw [FirstAchievable,if_neg zero]
    refine ⟨c1,Unit,stateless (respond H),(),?_,?_⟩
    · exact empty_move_legal positive c1
    · simpa only [firstBoard_eq_opening] using first_positive_budget positive

theorem first_exact_controller_budget (H : Nat) :
    FirstAchievable H (firstBudget H) ∧
      ∀ n, FirstAchievable H n → firstBudget H ≤ n := by
  refine ⟨first_target_achievable H,?_⟩
  intro n achievable
  by_cases exceptional : 4 ≤ H ∧ H%2 = 0
  · have nonzero : H ≠ 0 := by omega
    rw [FirstAchievable,if_neg nonzero] at achievable
    rcases achievable with ⟨opening,S,f,s,legal,safe⟩
    have target : firstBudget H = 1 := by simp [firstBudget,exceptional]
    rw [target]
    apply Classical.byContradiction
    intro h
    have zero : n = 0 := by omega
    subst n
    exact first_even_zero_budget_impossible exceptional.2 exceptional.1 f s opening safe
  · have target : firstBudget H = 0 := by simp [firstBudget,exceptional]
    rw [target]
    exact Nat.zero_le n

#print axioms first_exact_controller_budget
end UniformFour.U1
