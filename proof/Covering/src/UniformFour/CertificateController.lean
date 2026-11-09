import UniformFour.AClosure
import UniformFour.CClosure
import UniformFour.FiniteChecker
import UniformFour.InitialCertificates

/-! The actual U2 reference selector is closed on all exact certificates.
No assumed closure or future-nonloss theorem is an argument. Reviewed copy. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- Every certificate provides at least one accepted real response. -/
theorem certificate_qualified_exists {H : Nat} {b : Board} {q : Col}
    (h : Certificate H b) (hq : Legal H b q) (notFull : ¬ Full H (drop b q Q)) :
    ∃ p, Qualified H (drop b q Q) p := by
  rcases h with ⟨common, ha | hb | hc⟩
  · rcases a_reply_exists common ha hq notFull with ⟨p, hp, good, _⟩
    exact ⟨p, hp, good⟩
  · rcases b_reply_exists common hb hq with ⟨p, hp, good⟩
    exact ⟨p, hp, good⟩
  · rcases c_reply_exists common hc hq with ⟨p, hp, good⟩
    exact ⟨p, hp, good⟩

/-- The double-corner override is not ignored: A/B permit coverage; C cannot
have both P-owned corners, even after Q's move. -/
theorem certificate_corner_cover_good {H : Nat} {b : Board} {q : Col}
    (h : Certificate H b) (hq : Legal H b q) (hp : Legal H (drop b q Q) q)
    (corners : BothCorners (drop b q Q)) : Good H (afterRound b q q) := by
  rcases h with ⟨common, ha | hb | hc⟩
  · exact a_cover_good common ha hq hp
  · exact b_cover_good common hb hq hp
  · exact False.elim (c_no_bothCorners_after_Q hc q corners)

/-- Every action actually chosen by U2 from a certificate is accepted, including
corner-priority coverage. The proof does not substitute an arbitrary witness. -/
theorem certificate_selected_good {H : Nat} {b : Board} {q p : Col} {o : Observation}
    (h : Certificate H b) (hq : Legal H b q) (notFull : ¬ Full H (drop b q Q))
    (obs : Observes H (drop b q Q) o)
    (chosen : select H (drop b q Q) q o = some p) :
    Qualified H (drop b q Q) p := by
  have witness := certificate_qualified_exists h hq notFull
  rcases select_qualified_or_corner_cover obs witness chosen with good | corner
  · exact good
  · rcases corner with ⟨rfl, corners⟩
    have hp := select_legal chosen
    exact ⟨hp, certificate_corner_cover_good h hq hp corners⟩

theorem certificate_closed (H : Nat) :
    UniformFour.Closed H (UniformFour.stateless (respond H))
      (fun b _ => Certificate H b) := by
  constructor
  · intro b unit h
    exact ⟨h.1.1.1, h.1.1.2.2.1⟩
  · intro b unit h live q hq
    refine ⟨certificate_Q_move_safe h hq, ?_⟩
    by_cases full : Full H (drop b q Q)
    · exact Or.inl full
    · have bounded := drop_bounded h.1.1.1 hq Q
      rcases select_total_legal (q := q) (o := referenceObservation H (drop b q Q))
        bounded full with ⟨p, chosen, hp⟩
      have good := certificate_selected_good h hq full
        (referenceObserves H (drop b q Q)) chosen
      refine Or.inr ⟨p, (), ?_, hp, ?_⟩
      · simp only [UniformFour.stateless, respond, chosen, Option.map_some]
      · exact good.2

theorem certificate_allSafe {H : Nat} {b : Board} (h : Certificate H b) :
    UniformFour.Safe H (UniformFour.stateless (respond H)) b () :=
  UniformFour.closed_safe (certificate_closed H) h

/-- Actual U2, not the old odd-height controller, is now safe from its odd-height
first-player edge opening, for every finite continuation horizon. -/
theorem first_odd_allSafe {H : Nat} (odd : H % 2 = 1) :
    UniformFour.Safe H (UniformFour.stateless (respond H)) firstBoard () :=
  certificate_allSafe (firstBoard_certificate_odd odd)

theorem first_small_allSafe {H : Nat} (positive : 1 ≤ H) (small : H ≤ 3) :
    UniformFour.Safe H (UniformFour.stateless (respond H)) firstBoard () :=
  certificate_allSafe (firstBoard_certificate_small positive small)

#print axioms certificate_closed
#print axioms certificate_allSafe
#print axioms first_odd_allSafe
end UniformFour.U2
