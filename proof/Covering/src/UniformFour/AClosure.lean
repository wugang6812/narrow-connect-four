import UniformFour.RoundFacts

/-!
U2 A0/A1/A2 closure and legal full-column exits. Reviewed copy.
Targets may guard arbitrarily many unresolved lines; this is not old single-line C6.
-/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

theorem targetRound_cover_or_full {H : Nat} {b : Board} {t : Target} {q p : Col}
    (bounded : Bounded H b) (hq : Legal H b q)
    (policy : TargetRound H b t q p) :
    p = q ∨ height (drop b q Q) q = H := by
  by_cases full : height (drop b q Q) q = H
  · exact Or.inr full
  · have bound := drop_bounded bounded hq Q q
    exact Or.inl (policy.1 (by omega))

theorem fixedWinningTarget_preserved {H : Nat} {b : Board} {t : Target}
    (h : FixedWinningTarget H b t) (q p : Col) :
    FixedWinningTarget H (afterRound b q p) t := by
  rcases h with ⟨L, valid, onLine, fixed⟩
  refine ⟨L, valid, onLine, ?_⟩
  intro x hx hne
  exact stoneAt_drop_preserves (stoneAt_drop_preserves (fixed x hx hne) q Q) p P

theorem a0_round_good {H : Nat} {b : Board} (common : Common H b)
    (h : A0 H b) {q p : Col} (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (cover : p = q ∨ height (drop b q Q) q = H) :
    Good H (afterRound b q p) := by
  have safeQ := a0_Q_move_safe common h hq
  have s := structural_after_cover (common_structural common) hq hp safeQ cover
  apply good_of_structural s
  intro noP notFull
  exact Or.inl (Or.inl ((a0_cover_closed common h hq hp cover noP notFull).2))

theorem a1_round_good {H : Nat} {b : Board} {t : Target}
    (common : Common H b) (h : A1Data H b t) {q p : Col}
    (hq : Legal H b q) (hp : Legal H (drop b q Q) p)
    (policy : TargetRound H b t q p) : Good H (afterRound b q p) := by
  have safeQ := a1_Q_move_safe common ⟨t, h⟩ hq
  have cover := targetRound_cover_or_full common.1.1 hq policy
  have s := structural_after_cover (common_structural common) hq hp safeQ cover
  apply good_of_structural s
  intro noP notFull
  rcases target_after_round h.target hq hp policy with hit | keep
  · exact Or.inl (Or.inl (a1_capture_is_a0 h hq cover hit))
  · apply Or.inl
    apply Or.inr
    apply Or.inl
    refine ⟨t, keep, ?_⟩
    intro L unresolved
    exact h.commonTarget L (unresolved_after_cover_subset hq cover unresolved)

theorem a2_round_good {H : Nat} {b : Board} {t : Target}
    (common : Common H b) (h : A2Data H b t) {q p : Col}
    (hq : Legal H b q) (hp : Legal H (drop b q Q) p)
    (policy : TargetRound H b t q p) : Good H (afterRound b q p) := by
  have safeQ := a2_Q_move_safe common ⟨t, h⟩ hq
  have cover := targetRound_cover_or_full common.1.1 hq policy
  have s := structural_after_cover (common_structural common) hq hp safeQ cover
  apply good_of_structural s
  intro noP notFull
  rcases target_after_round h.target hq hp policy with hit | keep
  · exact False.elim (noP (a2_capture_wins q p h hit))
  · apply Or.inl
    apply Or.inr
    apply Or.inr
    refine ⟨t, keep, fixedWinningTarget_preserved h.fixedWin q p, ?_⟩
    intro L unresolved
    exact h.commonUpperColumn L (unresolved_after_cover_subset hq cover unresolved)

/-- Same-column coverage remains accepted for every A certificate. -/
theorem a_cover_good {H : Nat} {b : Board} (common : Common H b)
    (h : A H b) {q : Col} (hq : Legal H b q)
    (coverLegal : Legal H (drop b q Q) q) : Good H (afterRound b q q) := by
  rcases h with h0 | ⟨t, h1⟩ | ⟨t, h2⟩
  · exact a0_round_good common h0 hq coverLegal (Or.inl rfl)
  · exact a1_round_good common h1 hq coverLegal ⟨fun _ => rfl, fun ne => ne⟩
  · exact a2_round_good common h2 hq coverLegal ⟨fun _ => rfl, fun ne => ne⟩

/-- The A1/A2 target survives any legal full-column response outside its column. -/
theorem a_target_full_good {H : Nat} {b : Board} {t : Target}
    (common : Common H b) (h : A1Data H b t ∨ A2Data H b t)
    {q p : Col} (hq : Legal H b q) (hp : Legal H (drop b q Q) p)
    (full : height (drop b q Q) q = H) (outside : p ≠ t.col) :
    Good H (afterRound b q p) := by
  have policy : TargetRound H b t q p :=
    ⟨fun lt => False.elim (by omega), fun _ => outside⟩
  rcases h with h1 | h2
  · exact a1_round_good common h1 hq hp policy
  · exact a2_round_good common h2 hq hp policy

/-- A full Q column always has an accepted legal escape, when a response is due.
For a target certificate this escape is constructed outside the target column. -/
theorem a_full_reply_exists {H : Nat} {b : Board} (common : Common H b)
    (h : A H b) {q : Col} (hq : Legal H b q)
    (full : height (drop b q Q) q = H) (notFull : ¬ Full H (drop b q Q)) :
    ∃ p, Legal H (drop b q Q) p ∧ Good H (afterRound b q p) := by
  rcases h with h0 | ⟨t, h1⟩ | ⟨t, h2⟩
  · rcases bounded_notFull_exists_legal (drop_bounded common.1.1 hq Q) notFull with ⟨p, hp⟩
    exact ⟨p, hp, a0_round_good common h0 hq hp (Or.inr full)⟩
  · rcases target_outside_reply_exists h1.target hq full with ⟨p, hp, outside⟩
    exact ⟨p, hp, a_target_full_good common (Or.inl h1) hq hp full outside⟩
  · rcases target_outside_reply_exists h2.target hq full with ⟨p, hp, outside⟩
    exact ⟨p, hp, a_target_full_good common (Or.inr h2) hq hp full outside⟩

/-- Local A closure without a strategy or future-safety hypothesis. -/
theorem a_reply_exists {H : Nat} {b : Board} (common : Common H b)
    (h : A H b) {q : Col} (hq : Legal H b q) (notFull : ¬ Full H (drop b q Q)) :
    ∃ p, Legal H (drop b q Q) p ∧ Good H (afterRound b q p) ∧
      (height (drop b q Q) q < H → p = q) := by
  by_cases full : height (drop b q Q) q = H
  · rcases a_full_reply_exists common h hq full notFull with ⟨p, hp, good⟩
    exact ⟨p, hp, good, fun lt => False.elim (by omega)⟩
  · have bound := drop_bounded common.1.1 hq Q q
    have legal : Legal H (drop b q Q) q := by unfold Legal; omega
    exact ⟨q, legal, a_cover_good common h hq legal, fun _ => rfl⟩

#print axioms a_cover_good
#print axioms a_full_reply_exists
#print axioms a_reply_exists
end UniformFour.U2
