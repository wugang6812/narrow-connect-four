import BudgetTools
import UniformFour.CertificateController

/-! Reviewed copy. Actual U2 has zero remaining active cost once a certificate
and a permanent P-owned bottom square are present. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2

def BottomP (b : Board) : Prop := ∃ c, stoneAt b ⟨c,1⟩ = some P

theorem bottomP_drop {b : Board} (h : BottomP b) (q : Col) (p : Player) :
    BottomP (drop b q p) := by
  rcases h with ⟨c,hc⟩
  exact ⟨c,stoneAt_drop_preserves hc q p⟩

theorem c_no_bottomP {H : Nat} {b : Board} (h : C H b) : ¬ BottomP b := by
  rcases c_outer_shape h with ⟨a,d,rfl,_⟩
  rintro ⟨c,hc⟩
  cases c <;> simp [stoneAt_readRow, outerBoard, board, read_qp_P] at hc

theorem certificate_bottom_selected_cost {H : Nat} {b : Board} {q p : Col}
    (cert : Certificate H b) (bottom : BottomP b) (hq : Legal H b q)
    {o : Observation} (obs : Observes H (drop b q Q) o)
    (chosen : select H (drop b q Q) q o = some p) :
    activeCost H (drop b q Q) q p = 0 := by
  by_cases available : Legal H (drop b q Q) q
  · have good : Qualified H (drop b q Q) q := by
      refine ⟨available,?_⟩
      rcases cert.2 with ha | hb | hc
      · exact a_cover_good cert.1 ha hq available
      · exact b_cover_good cert.1 hb hq available
      · exact False.elim (c_no_bottomP hc bottom)
    have eq := select_cover_of_qualified obs good
    have same : p = q := Option.some.inj (chosen.symm.trans eq)
    subst p
    exact activeCost_self H (drop b q Q) q
  · exact activeCost_of_unavailable available

theorem certificate_bottom_budget_round {H : Nat} {b : Board}
    (cert : Certificate H b) (bottom : BottomP b) (k : Nat) :
    BudgetRoundSafe H (stateless (respond H)) k 0 b () := by
  induction k generalizing b with
  | zero => exact cert.1.1.2.2.1
  | succ k ih =>
    refine ⟨cert.1.1.2.2.1,Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨certificate_Q_move_safe cert hq,?_⟩
    by_cases full : Full H (drop b q Q)
    · exact Or.inl full
    · obtain ⟨p,chosen,legal⟩ := select_total_legal
        (q := q) (o := referenceObservation H (drop b q Q))
        (drop_bounded cert.1.1.1 hq Q) full
      have obs := referenceObserves H (drop b q Q)
      have good := certificate_selected_good cert hq full obs chosen
      have zero := certificate_bottom_selected_cost cert bottom hq obs chosen
      refine Or.inr ⟨p,(),?_,legal,by omega,?_⟩
      · simp only [stateless,respond,chosen,Option.map_some]
      · rw [zero, Nat.sub_zero]
        rcases good.2 with terminal | child
        · exact budget_terminal terminal k 0 ()
        · exact ih child (bottomP_drop (bottomP_drop bottom q Q) p P)

theorem certificate_bottom_budget {H : Nat} {b : Board}
    (cert : Certificate H b) (bottom : BottomP b) :
    BudgetSafe H (stateless (respond H)) 0 b () :=
  fun k => certificate_bottom_budget_round cert bottom k

#print axioms certificate_bottom_budget
end UniformFour.U1
