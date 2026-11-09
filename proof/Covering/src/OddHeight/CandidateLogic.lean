import OddHeight.Arithmetic
import OddHeight.Strategy
import OddHeight.Support

/-!
The single-line guard in C6. Local validation records accompany this copy.
No nonloss theorem is assumed: targets are proved empty after every legal Q move
from their positive even distance, and support descent handles unchecked lines.
-/
namespace OddHeight
open Player Col

private theorem list_lookup_none_above {α : Type} (xs : List α) (n : Nat)
    (hn : xs.length ≤ n) : xs[n]? = none := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hs : xs.length ≤ n := by simpa using hn
          simpa using ih n hs

theorem stoneAt_none_above_height {b : Board} {x : Cell}
    (hx : height b x.col < x.row) : stoneAt b x = none := by
  have hz : x.row ≠ 0 := by omega
  simp only [stoneAt, if_neg hz]
  apply list_lookup_none_above
  unfold height at hx
  omega

theorem height_drop_le_succ (b : Board) (q c : Col) (s : Player) :
    height (drop b q s) c ≤ height b c + 1 := by
  by_cases he : c = q
  · subst c
    simp
  · simp [height, drop, he]

/-- A positive even distance leaves the target ABOVE Q's next stone, in every column. -/
theorem candidate_targets_empty_after_Q
    {H : Nat} {b : Board} {L : Line} {ts : List Target} {E : Cell → Prop}
    (h : CandidateData H b L ts E) (q : Col) :
    ∀ t ∈ ts, stoneAt (drop b q Q) (targetCell t) = none := by
  intro t ht
  have room := (positive_even_gap_room H (height b t.col) t.row
    (h.positive t ht) (h.evenGap t ht) (h.belowRoof t ht)).1
  have raised := height_drop_le_succ b q t.col Q
  apply stoneAt_none_above_height
  change height (drop b q Q) t.col < t.row
  omega

theorem candidate_targets_empty_before
    {H : Nat} {b : Board} {L : Line} {ts : List Target} {E : Cell → Prop}
    (h : CandidateData H b L ts E) :
    ∀ t ∈ ts, stoneAt b (targetCell t) = none := by
  intro t ht
  exact stoneAt_none_above_height (h.positive t ht)

theorem allQ_impossible_of_empty {b : Board} {L : Line}
    (empty : ∃ x ∈ L.cells, stoneAt b x = none) :
    ¬ (∀ x ∈ L.cells, stoneAt b x = some Q) := by
  rcases empty with ⟨x, hx, he⟩
  intro hall
  have hq := hall x hx
  rw [he] at hq
  cases hq

theorem allQ_impossible_of_P {b : Board} {L : Line}
    (blocked : HasP b L) :
    ¬ (∀ x ∈ L.cells, stoneAt b x = some Q) := by
  rcases blocked with ⟨x, hx, hp⟩
  intro hall
  have hq := hall x hx
  rw [hp] at hq
  cases hq

/-- This covers even a vertical distinguished L; its empty target is enough. -/
theorem candidate_line_not_allQ_after_Q
    {H : Nat} {b : Board} {L : Line} {ts : List Target} {E : Cell → Prop}
    (h : CandidateData H b L ts E) (q : Col) :
    ¬ (∀ x ∈ L.cells, stoneAt (drop b q Q) x = some Q) := by
  apply allQ_impossible_of_empty
  cases ts with
  | nil => exact False.elim (h.nonempty rfl)
  | cons t ts =>
      have ht : t ∈ t :: ts := by simp
      exact ⟨targetCell t, h.onLine t ht,
        candidate_targets_empty_after_Q h q t ht⟩

/-- All nonvertical Q wins are excluded by the guarded line, fixed blockers,
or support descent. Only ACTUAL exceptions need coverage at the Q intermediate
board; new potential exceptions above the fresh Q are removed by P's cover. -/
theorem candidate_excludes_nonvertical_after_Q
    {H : Nat} {b : Board} {L : Line} {ts : List Target} {E : Cell → Prop}
    (h : CandidateData H b L ts E) (q : Col)
    (noP : ¬ Wins H b P)
    (actualComplete : ∀ x, existingException (drop b q Q) x → E x)
    {M : Line} (valid : ValidLine H M) (nonvertical : M.Nonvertical) :
    ¬ (∀ x ∈ M.cells, stoneAt (drop b q Q) x = some Q) := by
  by_cases same : M = L
  · subst M
    exact candidate_line_not_allQ_after_Q h q
  · intro allQ
    by_cases checked : ∃ x ∈ M.cells, x.row = 1 ∨ E x
    · have blocked := h.otherBlocked M ⟨valid, nonvertical, checked⟩ same
      exact allQ_impossible_of_P (hasP_drop_preserves blocked q Q) allQ
    · have aboveBottom : ∀ x ∈ M.cells, 2 ≤ x.row := by
        intro x hx
        have pos := (valid x hx).1
        have ne : x.row ≠ 1 := fun he => checked ⟨x, hx, Or.inl he⟩
        omega
      apply noP
      apply supported_Q_move_implies_previous_P_win q valid nonvertical aboveBottom
      intro x hx
      apply Q_supported_of_not_exception (aboveBottom x hx) (allQ x hx)
      intro ex
      exact checked ⟨x, hx, Or.inr (actualComplete x ex)⟩

private theorem playerOption_beq_eq (x y : Option Player) :
    (x == y) = true ↔ x = y := by
  cases x with
  | none =>
      cases y with
      | none => decide
      | some p => cases p <;> decide
  | some p =>
      cases y with
      | none => cases p <;> decide
      | some q => cases p <;> cases q <;> decide

/-- Reflect the controller's Bool hit test into a concrete P-owned target. -/
theorem target_hit_iff (b : Board) (ts : List Target) :
    (ts.any (fun t => stoneAt b (targetCell t) == some P)) = true ↔
      ∃ t ∈ ts, stoneAt b (targetCell t) = some P := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.any_cons, Bool.or_eq_true, playerOption_beq_eq, ih]
      constructor
      · intro hit
        rcases hit with first | later
        · exact ⟨t, by simp, first⟩
        · rcases later with ⟨u, hu, hp⟩
          exact ⟨u, by simp [hu], hp⟩
      · rintro ⟨u, hu, hp⟩
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact Or.inl hp
        · exact Or.inr ⟨u, hu, hp⟩

theorem target_hit_blocks_line
    {b : Board} {L : Line} {ts : List Target}
    (onLine : ∀ t ∈ ts, targetCell t ∈ L.cells)
    (hit : (ts.any (fun t => stoneAt b (targetCell t) == some P)) = true) :
    HasP b L := by
  rcases (target_hit_iff b ts).mp hit with ⟨t, ht, hp⟩
  exact ⟨targetCell t, onLine t ht, hp⟩

/-- On a hit, fixed blockers plus the newly owned target block EVERY checked line.
The structural hypothesis is supplied by the separate cover-preservation theorem. -/
theorem candidate_hit_permanent
    {H : Nat} {b after : Board} {L : Line} {ts : List Target} {E : Cell → Prop}
    (h : CandidateData H b L ts E)
    (structureAfter : Structural H after E)
    (keepBlockers : ∀ M, HasP b M → HasP after M)
    (hit : (ts.any (fun t => stoneAt after (targetCell t) == some P)) = true) :
    PermanentHyp H after := by
  refine ⟨E, structureAfter, ?_⟩
  intro M hm
  by_cases same : M = L
  · subst M
    exact target_hit_blocks_line h.onLine hit
  · exact keepBlockers M (h.otherBlocked M hm same)

#print axioms candidate_targets_empty_after_Q
#print axioms candidate_excludes_nonvertical_after_Q
#print axioms candidate_hit_permanent
end OddHeight
