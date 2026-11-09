import BudgetSemantics
import OddHeight.Assembly

/-! Reviewed copy. Generic arithmetic on the actual U2 budget semantics. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player

theorem activeCost_le_one (H : Nat) (b : Board) (q p : Col) :
    activeCost H b q p ≤ 1 := by
  unfold activeCost
  split <;> omega

theorem activeCost_self (H : Nat) (b : Board) (q : Col) :
    activeCost H b q q = 0 := by simp [activeCost]

theorem activeCost_of_unavailable {H : Nat} {b : Board} {q p : Col}
    (h : ¬ Legal H b q) : activeCost H b q p = 0 := by simp [activeCost, h]

theorem budget_terminal {S : Type} {H : Nat} {f : Controller S} {b : Board}
    (h : SafeTerminal H b) (k budget : Nat) (s : S) :
    BudgetRoundSafe H f k budget b s := by
  cases k with
  | zero => exact h.1
  | succ k =>
    refine ⟨h.1, ?_⟩
    rcases h.2 with win | full
    · exact Or.inl win
    · exact Or.inr (Or.inl full)

theorem budget_round_mono {S : Type} {H : Nat} {f : Controller S}
    (k : Nat) {lo hi : Nat} {b : Board} {s : S}
    (hle : lo ≤ hi) (h : BudgetRoundSafe H f k lo b s) :
    BudgetRoundSafe H f k hi b s := by
  induction k generalizing lo hi b s with
  | zero => exact h
  | succ k ih =>
    refine ⟨h.1, ?_⟩
    rcases h.2 with win | full | moves
    · exact Or.inl win
    · exact Or.inr (Or.inl full)
    · apply Or.inr; apply Or.inr
      intro q hq
      rcases moves q hq with ⟨safe, full | ⟨p,next,chosen,legal,cost,tail⟩⟩
      · exact ⟨safe, Or.inl full⟩
      · exact ⟨safe, Or.inr ⟨p,next,chosen,legal,by omega,
          ih (by omega) tail⟩⟩

theorem budget_safe_mono {S : Type} {H : Nat} {f : Controller S}
    {lo hi : Nat} {b : Board} {s : S} (hle : lo ≤ hi)
    (h : BudgetSafe H f lo b s) : BudgetSafe H f hi b s :=
  fun k => budget_round_mono k hle (h k)
end UniformFour.U1
