import UniformFour.AClosure
import OddHeight.OpeningProofs

/-! Actual U2 certificates at the edge opening. Reviewed copy. Old strategy
nonloss is NOT used; only its already-written board geometry is reused. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- Old single-line single-target geometry implies the more general U2 A1 body.
This does not identify the two controllers or transfer a strategy by existence. -/
theorem singleton_candidate_a1 {H : Nat} {b : Board} {L : Line} {t : Target}
    (h : CandidateHyp H b L [t]) : A1 H b := by
  rcases h with ⟨E, h⟩
  have mem : t ∈ [t] := by simp
  refine ⟨t, ?_, ?_⟩
  · exact ⟨h.lineValid _ (h.onLine t mem),
      cell_empty_above_height (h.positive t mem),
      h.positive t mem, h.evenGap t mem, h.outsideEven⟩
  · intro M unresolved
    by_cases eq : M = L
    · subst M
      exact h.onLine t mem
    · exact False.elim (unresolved.2
        (h.otherBlocked M (toCheck_mono h.structural.complete unresolved.1) eq))

theorem firstBoard_common {H : Nat} (positive : 1 ≤ H) : Common H firstBoard := by
  have st := firstBoard_structure positive
  refine ⟨⟨st.bounded, ?_, st.noQ, ?_⟩, st.topRun⟩
  · rw [firstBoard_eq_opening]
    exact oneStone_no_win H c1 P
  · intro full
    have h := full c2
    simp [height, firstBoard, board] at h
    omega

theorem firstBoard_certificate_small {H : Nat} (positive : 1 ≤ H) (small : H ≤ 3) :
    Certificate H firstBoard := by
  exact ⟨firstBoard_common positive,
    Or.inl (Or.inl (a0_of_permanent (firstBoard_permanent_small positive small)))⟩

theorem firstBoard_certificate_odd {H : Nat} (odd : H % 2 = 1) :
    Certificate H firstBoard := by
  have positive : 1 ≤ H := by omega
  by_cases small : H ≤ 3
  · exact firstBoard_certificate_small positive small
  · have large : 5 ≤ H := by omega
    exact ⟨firstBoard_common positive,
      Or.inl (Or.inr (Or.inl (singleton_candidate_a1 (firstBoard_candidate large odd))))⟩

#print axioms firstBoard_certificate_small
#print axioms firstBoard_certificate_odd
end UniformFour.U2
