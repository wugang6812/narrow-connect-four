import BottomBudget
import UniformFour.FirstRoot

/-! Reviewed copy. Full finite-height first-player active upper bounds for the
actual U2 respond function, in the real OddHeight.Board / BudgetSafe model.
No certificate-existence or closure hypothesis is left at the opening root. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2

theorem firstBoard_bottomP : BottomP firstBoard := by
  exact ⟨c1, by simp [stoneAt,firstBoard,board]⟩

theorem w_bottomP (a d : Nat) : BottomP (wBoard a d) := by
  exact ⟨c1, by simp [stoneAt,wBoard,board]⟩

theorem v_bottomP (a b e d : Nat) : BottomP (vBoard a b e d) :=
  ⟨c1,(v_corners a b e d).1⟩

theorem good_bottom_budget_round {H : Nat} {b : Board}
    (good : Good H b) (bottom : BottomP b) (k budget : Nat) :
    BudgetRoundSafe H (stateless (respond H)) k budget b () := by
  rcases good with terminal | certificate
  · exact budget_terminal terminal k budget ()
  · exact budget_round_mono k (Nat.zero_le budget)
      (certificate_bottom_budget_round certificate bottom k)

theorem v_selected_cost_zero {H : Nat} {b : Board} (shape : VShape H b)
    {q p : Col} {o : Observation} (obs : Observes H (drop b q Q) o)
    (chosen : select H (drop b q Q) q o = some p) :
    activeCost H (drop b q Q) q p = 0 := by
  by_cases available : Legal H (drop b q Q) q
  · rcases shape with ⟨a,d,e,t,rfl,_⟩
    have corners := v_corners a d e t
    have after : BothCorners (drop (vBoard a d e t) q Q) :=
      ⟨stoneAt_drop_preserves corners.1 q Q, stoneAt_drop_preserves corners.2 q Q⟩
    have eq := select_cover_of_corners obs available after
    have same : p = q := Option.some.inj (chosen.symm.trans eq)
    subst p
    exact activeCost_self _ _ _
  · exact activeCost_of_unavailable available

theorem v_budget_round {H : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    {b : Board} (shape : VShape H b) (k : Nat) :
    BudgetRoundSafe H (stateless (respond H)) k 0 b () := by
  induction k generalizing b with
  | zero =>
    rcases shape with ⟨a,d,e,t,rfl,_⟩
    exact v_noQ H a d e t
  | succ k ih =>
    have bound : Bounded H b := by rcases shape with ⟨a,d,e,t,rfl,h⟩; exact h
    have bottom : BottomP b := by
      rcases shape with ⟨a,d,e,t,rfl,_⟩; exact v_bottomP a d e t
    have safe : ¬ Wins H b Q := by
      rcases shape with ⟨a,d,e,t,rfl,_⟩; exact v_noQ H a d e t
    refine ⟨safe,Or.inr (Or.inr ?_)⟩
    intro q hq
    have safeQ : ¬ Wins H (drop b q Q) Q := by
      rcases shape with ⟨a,d,e,t,rfl,_⟩; exact v_Q_move_safe hq
    refine ⟨safeQ,?_⟩
    by_cases full : Full H (drop b q Q)
    · exact Or.inl full
    · obtain ⟨p,chosen,legal⟩ := select_total_legal
        (q := q) (o := referenceObservation H (drop b q Q))
        (drop_bounded bound hq Q) full
      have obs := referenceObserves H (drop b q Q)
      have zero := v_selected_cost_zero shape obs chosen
      have closed := (v_select_closed even h4 shape hq full obs chosen).2
      refine Or.inr ⟨p,(),?_,legal,by omega,?_⟩
      · simp only [stateless,respond,chosen,Option.map_some]
      · rw [zero,Nat.sub_zero]
        rcases closed with good | child
        · exact good_bottom_budget_round good
            (bottomP_drop (bottomP_drop bottom q Q) p P) k 0
        · exact ih child

/-- A W-to-W round cannot be an active switch: the two middle columns remain
empty, while the first and fourth column parities remain odd/even. -/
theorem w_to_w_same {H a d : Nat} {q p : Col}
    (shape : WShape H (afterRound (wBoard a d) q p)) : p = q := by
  rcases shape with ⟨a',d',eq,_,_⟩
  have h1 := congrArg (fun b => height b c1) eq
  have h2 := congrArg (fun b => height b c2) eq
  have h3 := congrArg (fun b => height b c3) eq
  have h4 := congrArg (fun b => height b c4) eq
  cases q <;> cases p <;>
    simp [afterRound,height,drop,wBoard,board] at h1 h2 h3 h4 ⊢ <;> omega

theorem w_budget_round {H : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    {b : Board} (shape : WShape H b) (k : Nat) :
    BudgetRoundSafe H (stateless (respond H)) k 1 b () := by
  induction k generalizing b with
  | zero =>
    rcases shape with ⟨a,d,rfl,_,_⟩
    exact w_noQ H a d
  | succ k ih =>
    rcases shape with ⟨a,d,rfl,bound,ad⟩
    refine ⟨w_noQ H a d,Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨w_Q_move_safe hq,?_⟩
    by_cases full : Full H (drop (wBoard a d) q Q)
    · exact Or.inl full
    · obtain ⟨p,chosen,legal⟩ := select_total_legal
        (q := q) (o := referenceObservation H (drop (wBoard a d) q Q))
        (drop_bounded bound hq Q) full
      have obs := referenceObserves H (drop (wBoard a d) q Q)
      have closed := (w_select_closed even h4 ⟨a,d,rfl,bound,ad⟩ hq obs chosen).2
      refine Or.inr ⟨p,(),?_,legal,activeCost_le_one _ _ _ _,?_⟩
      · simp only [stateless,respond,chosen,Option.map_some]
      · rcases closed with good | childW | childV
        · exact good_bottom_budget_round good
            (bottomP_drop (bottomP_drop (w_bottomP a d) q Q) p P) k _
        · have same := w_to_w_same childW
          subst p
          rw [activeCost_self,Nat.sub_zero]
          exact ih childW
        · exact budget_round_mono k (Nat.zero_le _)
            (v_budget_round even h4 childV k)

/-- The exact first-player target budget for positive finite heights. -/
def firstBudget (H : Nat) : Nat := if 4 ≤ H ∧ H%2 = 0 then 1 else 0

theorem first_positive_budget {H : Nat} (positive : 0 < H) :
    BudgetSafe H (stateless (respond H)) (firstBudget H) firstBoard () := by
  by_cases small : H ≤ 3
  · have target : firstBudget H = 0 := by
      have hn : ¬ 4 ≤ H := by omega
      simp [firstBudget,hn]
    rw [target]
    exact certificate_bottom_budget (firstBoard_certificate_small positive small) firstBoard_bottomP
  · have h4 : 4 ≤ H := by omega
    by_cases even : H%2 = 0
    · have target : firstBudget H = 1 := by simp [firstBudget,h4,even]
      rw [target]
      have root : WShape H firstBoard := by
        refine ⟨0,0,?_,firstBoard_bounded positive,?_⟩
        · funext c; cases c <;> rfl
        · omega
      exact fun k => w_budget_round even h4 root k
    · have odd : H%2 = 1 := by omega
      have target : firstBudget H = 0 := by simp [firstBudget,even]
      rw [target]
      exact certificate_bottom_budget (firstBoard_certificate_odd odd) firstBoard_bottomP

/-- Height zero has no first placement; the empty root is already terminal. -/
theorem first_height_zero_budget :
    BudgetSafe 0 (stateless (respond 0)) 0 empty () := by
  intro k
  apply budget_terminal (k := k) (budget := 0)
  exact ⟨empty_no_win 0 Q, Or.inr (by intro c; cases c <;> rfl)⟩

#print axioms first_positive_budget
#print axioms first_height_zero_budget
end UniformFour.U1
