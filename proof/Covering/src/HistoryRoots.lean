import U1
import HistoryBudget

namespace UniformFour.U1
open OddHeight OddHeight.Player

def FirstHistoryAchievable (H n : Nat) : Prop :=
  if H = 0 then
    ∃ (S : Type) (f : Controller S) (s : S), HistoryBudget H f n empty s
  else
    ∃ (opening : Col) (S : Type) (f : Controller S) (s : S),
      Legal H empty opening ∧ HistoryBudget H f n (drop empty opening P) s

def SecondHistoryAchievable (H n : Nat) : Prop :=
  ∃ (S : Type) (f : Controller S) (s : S), HistoryBudget H f n empty s

theorem first_history_iff (H n : Nat) :
    FirstHistoryAchievable H n ↔ FirstAchievable H n := by
  simp only [FirstHistoryAchievable,FirstAchievable,budgetSafe_iff_historyBudget]

theorem second_history_iff (H n : Nat) :
    SecondHistoryAchievable H n ↔ SecondAchievable H n := by
  simp only [SecondHistoryAchievable,SecondAchievable,budgetSafe_iff_historyBudget]

theorem first_exact_history_budget (H : Nat) :
    FirstHistoryAchievable H (firstBudget H) ∧
      ∀ n, FirstHistoryAchievable H n → firstBudget H ≤ n := by
  have exactBudget := first_exact_controller_budget H
  exact ⟨(first_history_iff _ _).mpr exactBudget.1,
    fun n hn => exactBudget.2 n ((first_history_iff _ _).mp hn)⟩

theorem second_exact_history_budget (H : Nat) :
    SecondHistoryAchievable H (secondBudget H) ∧
      ∀ n, SecondHistoryAchievable H n → secondBudget H ≤ n := by
  have exactBudget := second_exact_controller_budget H
  exact ⟨(second_history_iff _ _).mpr exactBudget.1,
    fun n hn => exactBudget.2 n ((second_history_iff _ _).mp hn)⟩

/-- Explicit specialization to policies that inspect the entire move history.
The free first move is present in the history but not charged as a reply. -/
theorem no_zero_first_history_policy {H : Nat} (even : H%2 = 0) (height : 4 ≤ H)
    (policy : List Col → Option Col) (opening : Col) :
    ¬ HistoryBudget H (historyController policy) 0 (drop empty opening P) [opening] := by
  intro h
  exact first_even_zero_budget_impossible even height _ _ opening (history_to_budget h)

theorem no_zero_second_history_policy {H : Nat} (height : 2 ≤ H)
    (policy : List Col → Option Col) :
    ¬ HistoryBudget H (historyController policy) 0 empty [] := by
  intro h
  exact second_zero_budget_impossible height _ _ (history_to_budget h)

#print axioms first_exact_history_budget
#print axioms second_exact_history_budget
#print axioms no_zero_first_history_policy
#print axioms no_zero_second_history_policy
end UniformFour.U1
