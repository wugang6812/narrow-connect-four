import SecondUpper
import SecondLowerBound

/-! Reviewed copy. Exact second-player optimum in BudgetSafe semantics only.
The finite-prefix budget equivalence is proved separately in HistoryBudget.
This module concerns the second player; FirstExact proves the first optimum. -/
namespace UniformFour.U1
open OddHeight UniformFour.U2

def SecondAchievable (H n : Nat) : Prop :=
  ∃ (S : Type) (f : Controller S) (s : S), BudgetSafe H f n empty s

def secondBudget (H : Nat) : Nat := if 2 ≤ H then 1 else 0

theorem second_exact_controller_budget (H : Nat) :
    SecondAchievable H (secondBudget H) ∧
      ∀ n, SecondAchievable H n → secondBudget H ≤ n := by
  by_cases large : 2 ≤ H
  · have target : secondBudget H = 1 := by simp [secondBudget,large]
    rw [target]
    refine ⟨⟨Unit,stateless (respond H),(),second_budget_one H⟩,?_⟩
    intro n hn
    rcases hn with ⟨S,f,s,hs⟩
    apply Classical.byContradiction
    intro h
    have zero : n = 0 := by omega
    subst n
    exact second_zero_budget_impossible large f s hs
  · have small : H ≤ 1 := by omega
    have target : secondBudget H = 0 := by simp [secondBudget,large]
    rw [target]
    exact ⟨⟨Unit,stateless (respond H),(),second_budget_zero_of_le_one small⟩,
      fun n _ => Nat.zero_le n⟩

#print axioms second_exact_controller_budget
end UniformFour.U1
