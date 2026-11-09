import OddHeight.Assembly
import UniformFour.Certificates
import OddHeight.CandidateCapacity

/-! Shared U2 one-round facts. Reviewed copy; these contain no future-safety field. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

abbrev afterRound (b : Board) (q p : Col) : Board := drop (drop b q Q) p P

/-- Exact acceptance of a successor: safe terminal, or a new current certificate. -/
def Good (H : Nat) (b : Board) : Prop := SafeTerminal H b ∨ Certificate H b

theorem common_after_cover {H : Nat} {b : Board} (h : Common H b)
    {q p : Col} (hq : Legal H b q) (hp : Legal H (drop b q Q) p)
    (safeQ : ¬ Wins H (drop b q Q) Q)
    (cover : p = q ∨ height (drop b q Q) q = H)
    (noP : ¬ Wins H (afterRound b q p) P) (notFull : ¬ Full H (afterRound b q p)) :
    Common H (afterRound b q p) := by
  have s := structural_after_cover (common_structural h) hq hp safeQ cover
  exact ⟨⟨s.bounded, noP, s.noQ, notFull⟩, s.topRun⟩

theorem good_of_structural {H : Nat} {b : Board} {E : Cell → Prop}
    (s : Structural H b E)
    (body : ¬ Wins H b P → ¬ Full H b → A H b ∨ B H b ∨ C H b) :
    Good H b := by
  by_cases win : Wins H b P
  · exact Or.inl ⟨s.noQ, Or.inl win⟩
  by_cases full : Full H b
  · exact Or.inl ⟨s.noQ, Or.inr full⟩
  exact Or.inr ⟨⟨⟨s.bounded, win, s.noQ, full⟩, s.topRun⟩, body win full⟩

theorem good_noQ {H : Nat} {b : Board} (h : Good H b) : ¬ Wins H b Q := by
  rcases h with terminal | certificate
  · exact terminal.1
  · exact certificate.1.1.2.2.1

@[simp] theorem inJ_singleton (t : Target) (c : Col) :
    inJ [t] c = true ↔ c = t.col := by
  simp only [inJ_iff, List.mem_singleton]
  constructor
  · rintro ⟨u, rfl, h⟩
    exact h.symm
  · intro h
    exact ⟨t, rfl, h.symm⟩

theorem inJ_singleton_false (t : Target) (c : Col) :
    inJ [t] c = false ↔ c ≠ t.col := by
  cases e : inJ [t] c with
  | false =>
      have ne : c ≠ t.col := by
        intro eq
        have ht := (inJ_singleton t c).2 eq
        rw [e] at ht
        cases ht
      simp [ne]
  | true =>
      have eq := (inJ_singleton t c).1 e
      simp [eq]

/-- A candidate target column cannot be filled by the Q half-turn. -/
theorem target_cover_legal {H : Nat} {b : Board} {t : Target}
    (h : TargetCondition H b t) : Legal H (drop b t.col Q) t.col := by
  have room := target_room h
  have roof : t.row ≤ H := h.inBoard.2
  unfold Legal
  rw [height_drop_same]
  omega

/-- Full-q fallback has a real legal move OUTSIDE the reserved target column. -/
theorem target_outside_reply_exists {H : Nat} {b : Board} {t : Target} {q : Col}
    (h : TargetCondition H b t) (hq : Legal H b q)
    (full : height (drop b q Q) q = H) :
    ∃ p, Legal H (drop b q Q) p ∧ p ≠ t.col := by
  have nq : q ≠ t.col := by
    intro eq
    subst q
    have legal := target_cover_legal h
    unfold Legal at legal
    omega
  rcases outside_reply_exists h.outsideEven hq
    ((inJ_singleton_false t q).2 nq) with ⟨p, hp, out⟩
  exact ⟨p, hp, (inJ_singleton_false t p).1 out⟩

/-- This is the cover-or-full-and-outside geometric condition, not a controller. -/
def TargetRound (H : Nat) (b : Board) (t : Target) (q p : Col) : Prop :=
  (height (drop b q Q) q < H → p = q) ∧ (q ≠ t.col → p ≠ t.col)

theorem target_round_outside_even {H : Nat} {b : Board} {t : Target} {q p : Col}
    (h : TargetCondition H b t) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p) (policy : TargetRound H b t q p) :
    outsideTarget H (afterRound b q p) t % 2 = 0 := by
  by_cases eq : q = t.col
  · subst q
    have pp := policy.1 (target_cover_legal h)
    subst p
    have inside : inJ [t] t.col = true := (inJ_singleton t t.col).2 rfl
    change outside H (drop (drop b t.col Q) t.col P) [t] % 2 = 0
    rw [outside_drop_inside inside P, outside_drop_inside inside Q]
    exact h.outsideEven
  · have old := h.outsideEven
    have first := outside_drop hq ((inJ_singleton_false t q).2 eq) Q
    have second := outside_drop hp ((inJ_singleton_false t p).2 (policy.2 eq)) P
    simp only [outsideTarget, afterRound] at old ⊢
    omega

/-- The actual two drops either acquire P's target or retain its exact conditions. -/
theorem target_after_round {H : Nat} {b : Board} {t : Target} {q p : Col}
    (h : TargetCondition H b t) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p) (policy : TargetRound H b t q p) :
    stoneAt (afterRound b q p) (targetCell t) = some P ∨
      TargetCondition H (afterRound b q p) t := by
  have evenOutside := target_round_outside_even h hq hp policy
  by_cases eq : q = t.col
  · subst q
    have pp := policy.1 (target_cover_legal h)
    subst p
    have room := target_room h
    have even := h.evenGap
    have hh : height (afterRound b t.col t.col) t.col = height b t.col + 2 := by
      simp [afterRound, Nat.add_assoc]
    by_cases hit : t.row = height b t.col + 2
    · left
      have x : targetCell t = ⟨t.col, height (drop b t.col Q) t.col + 1⟩ := by
        unfold targetCell
        rw [height_drop_same, hit]
      rw [x]
      exact candidate_stoneAt_new_top (drop b t.col Q) t.col P
    · right
      have pos : height (afterRound b t.col t.col) t.col < t.row := by omega
      exact ⟨h.inBoard, cell_empty_above_height pos, pos, by omega, evenOutside⟩
  · have pp : p ≠ t.col := policy.2 eq
    have hh : height (afterRound b q p) t.col = height b t.col := by
      simp [height, drop, Ne.symm eq, Ne.symm pp]
    right
    have pos : height (afterRound b q p) t.col < t.row := by rw [hh]; exact h.positive
    exact ⟨h.inBoard, cell_empty_above_height pos, pos,
      by rw [hh]; exact h.evenGap, evenOutside⟩

end UniformFour.U2
