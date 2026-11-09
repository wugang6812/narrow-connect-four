import OddHeight.Strategy
import OddHeight.Capacity
import OddHeight.CandidateLogic

/-! Candidate capacity and reply legality, in the actual list-column board model.
Local compilation and replay records accompany this reviewed copy. -/
namespace OddHeight
open Player Col

theorem outside_expanded (H : Nat) (b : Board) (ts : List Target) :
    outside H b ts =
      (if inJ ts c1 then 0 else H - height b c1) +
      (if inJ ts c2 then 0 else H - height b c2) +
      (if inJ ts c3 then 0 else H - height b c3) +
      (if inJ ts c4 then 0 else H - height b c4) := by
  simp [outside, allCols]

private theorem candidate_col_beq_eq (x y : Col) :
    (x == y) = true ↔ x = y := by
  cases x <;> cases y <;> decide

theorem inJ_iff {ts : List Target} {c : Col} :
    inJ ts c = true ↔ ∃ t ∈ ts, t.col = c := by
  unfold inJ
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.any_cons, Bool.or_eq_true, candidate_col_beq_eq, ih]
      constructor
      · intro hj
        rcases hj with he | he
        · exact ⟨t, by simp, he⟩
        · rcases he with ⟨u, hu, he⟩
          exact ⟨u, by simp [hu], he⟩
      · rintro ⟨u, hu, he⟩
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact Or.inl he
        · exact Or.inr ⟨u, hu, he⟩

theorem inJ_of_mem {ts : List Target} {t : Target} (ht : t ∈ ts) :
    inJ ts t.col = true := inJ_iff.mpr ⟨t, ht, rfl⟩

theorem outside_positive_iff {H : Nat} {b : Board} {ts : List Target} :
    0 < outside H b ts ↔ ∃ c, Legal H b c ∧ inJ ts c = false := by
  constructor
  · intro hpos
    apply Classical.byContradiction
    intro hn
    have hz : ∀ c, (if inJ ts c then 0 else H - height b c) = 0 := by
      intro c
      cases hj : inJ ts c with
      | true => simp [hj]
      | false =>
          have hnl : ¬ Legal H b c := fun hc => hn ⟨c, hc, hj⟩
          unfold Legal at hnl
          simp [hj]
          omega
    rw [outside_expanded, hz c1, hz c2, hz c3, hz c4] at hpos
    omega
  · rintro ⟨c, hc, hj⟩
    unfold Legal at hc
    cases c <;> simp [outside_expanded, hj] <;> omega

/-- An actual legal move outside J consumes exactly one outside vacancy. -/
theorem outside_drop {H : Nat} {b : Board} {ts : List Target} {c : Col}
    (hc : Legal H b c) (hj : inJ ts c = false) (p : Player) :
    outside H (drop b c p) ts + 1 = outside H b ts := by
  unfold Legal at hc
  cases c <;> simp_all [outside_expanded, height, drop] <;> omega

/-- Moves in target columns leave the outside count unchanged. -/
theorem outside_drop_inside {H : Nat} {b : Board} {ts : List Target} {c : Col}
    (hj : inJ ts c = true) (p : Player) :
    outside H (drop b c p) ts = outside H b ts := by
  cases c <;> simp [outside_expanded, height, drop, hj]

/-- Even outside capacity ensures a fallback still exists after Q uses one slot. -/
theorem outside_reply_exists {H : Nat} {b : Board} {ts : List Target} {q : Col}
    (heven : outside H b ts % 2 = 0)
    (hq : Legal H b q) (hj : inJ ts q = false) :
    ∃ p, Legal H (drop b q Q) p ∧ inJ ts p = false := by
  have hpos := outside_positive_iff.mpr ⟨q, hq, hj⟩
  have hstep := outside_drop hq hj Q
  apply outside_positive_iff.mp
  omega

/-- Positive even target gaps prohibit Q from filling a target column. -/
theorem candidate_cover_legal {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q : Col}
    (d : CandidateData H b L ts E) (hj : inJ ts q = true) :
    Legal H (drop b q Q) q := by
  rcases inJ_iff.mp hj with ⟨t, ht, he⟩
  have hp := d.positive t ht
  have hv := d.evenGap t ht
  have hr := d.belowRoof t ht
  rw [he] at hp hv
  have hroom := positive_even_gap_room H (height b q) t.row hp hv hr
  unfold Legal
  rw [height_drop_same]
  omega

/-- The candidate branch of the executable policy returns a legal P move.
A nonfilled Q column is covered, and an outside Q move gets an outside reply. -/
theorem candidate_reply_legal {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q : Col}
    (d : CandidateData H b L ts E) (hq : Legal H b q)
    (_hnotfull : ¬ Full H (drop b q Q)) :
    ∃ p, rawReply H b q (.candidate L ts) = some (p, .candidate L ts) ∧
      Legal H (drop b q Q) p ∧
      (height (drop b q Q) q < H → p = q) ∧
      (inJ ts q = false → inJ ts p = false) := by
  cases hj : inJ ts q with
  | true =>
      refine ⟨q, ?_, candidate_cover_legal d hj, ?_, ?_⟩
      · simp [rawReply, hj]
      · intro _; rfl
      · intro hfalse; cases hfalse
  | false =>
      by_cases hf : height (drop b q Q) q = H
      · rcases outside_reply_exists d.outsideEven hq hj with ⟨p, hp, hjp⟩
        have hw : ∃ c ∈ allCols,
            height (drop b q Q) c < H ∧ inJ ts c = false := by
          refine ⟨p, ?_, hp, hjp⟩
          cases p <;> simp [allCols]
        rcases firstAvailable_complete hw with ⟨c, hc⟩
        have hs := firstAvailable_sound hc
        refine ⟨c, ?_, hs.1, ?_, ?_⟩
        · simp [rawReply, hj, hf, hc]
        · intro hlt; omega
        · intro _; exact hs.2
      · have hb := drop_bounded d.structural.bounded hq Q q
        have hp : Legal H (drop b q Q) q := by unfold Legal; omega
        refine ⟨q, ?_, hp, ?_, ?_⟩
        · have hf' : ¬ height b q + 1 = H := by simpa only [height_drop_same] using hf
          simp [rawReply, hj, hf']
        · intro _; rfl
        · intro _; exact hj

/-- Outside parity is preserved by the actual two drops chosen by the policy. -/
theorem candidate_outside_even_after_round {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q p : Col}
    (d : CandidateData H b L ts E) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (hcover : height (drop b q Q) q < H → p = q)
    (hout : inJ ts q = false → inJ ts p = false) :
    outside H (drop (drop b q Q) p P) ts % 2 = 0 := by
  cases hj : inJ ts q with
  | true =>
      have he := hcover (candidate_cover_legal d hj)
      subst p
      rw [outside_drop_inside hj P, outside_drop_inside hj Q]
      exact d.outsideEven
  | false =>
      have hfirst := outside_drop hq hj Q
      have hsecond := outside_drop hp (hout hj) P
      have he := d.outsideEven
      omega

private theorem candidate_get_none {α : Type} (xs : List α) (n : Nat)
    (hn : xs.length ≤ n) : xs[n]? = none := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hn' : xs.length ≤ n := by simpa using hn
          simpa using ih n hn'

/-- A target strictly above a column's actual height is empty. -/
theorem candidate_stoneAt_empty {b : Board} {x : Cell}
    (hh : height b x.col < x.row) : stoneAt b x = none := by
  have hz : x.row ≠ 0 := by omega
  have hi : (b x.col).length ≤ x.row - 1 := by
    unfold height at hh
    omega
  simp only [stoneAt, if_neg hz]
  exact candidate_get_none _ _ hi

private theorem candidate_get_new_top {α : Type} (xs : List α) (v : α) :
    (xs ++ [v])[xs.length]? = some v := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa using ih

/-- The actual newly appended stone occupies the new top cell. -/
theorem candidate_stoneAt_new_top (b : Board) (c : Col) (v : Player) :
    stoneAt (drop b c v) ⟨c, height b c + 1⟩ = some v := by
  have hz : height b c + 1 ≠ 0 := by omega
  simpa [stoneAt, hz, height, drop] using candidate_get_new_top (b c) v

/-- Every candidate target remains strictly above the board immediately after Q. -/
theorem candidate_targets_above_after_Q {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} (d : CandidateData H b L ts E)
    (q : Col) : ∀ t ∈ ts, height (drop b q Q) t.col < t.row := by
  intro t ht
  have hp := d.positive t ht
  have he := d.evenGap t ht
  by_cases hc : t.col = q
  · rw [hc, height_drop_same]
    rw [hc] at hp he
    omega
  · simpa [height, drop, hc] using hp

/-- A policy reply can enter a target column only when Q played that same column. -/
theorem candidate_reply_target_column {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q p : Col}
    (d : CandidateData H b L ts E)
    (hcover : height (drop b q Q) q < H → p = q)
    (hout : inJ ts q = false → inJ ts p = false)
    {t : Target} (ht : t ∈ ts) (hp : p = t.col) : q = t.col := by
  cases hj : inJ ts q with
  | true =>
      have he := hcover (candidate_cover_legal d hj)
      exact he.symm.trans hp
  | false =>
      have hfalse := hout hj
      rw [hp, inJ_of_mem ht] at hfalse
      cases hfalse

/-- Each actual target either receives P or retains a positive even gap. -/
theorem candidate_target_after_round {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q p : Col}
    (d : CandidateData H b L ts E)
    (hcover : height (drop b q Q) q < H → p = q)
    (hout : inJ ts q = false → inJ ts p = false)
    {t : Target} (ht : t ∈ ts) :
    stoneAt (drop (drop b q Q) p P) (targetCell t) = some P ∨
      (height (drop (drop b q Q) p P) t.col < t.row ∧
       (t.row - height (drop (drop b q Q) p P) t.col) % 2 = 0) := by
  have hpos := d.positive t ht
  have heven := d.evenGap t ht
  by_cases hq : q = t.col
  · have hj : inJ ts q = true := by rw [hq]; exact inJ_of_mem ht
    have hp := hcover (candidate_cover_legal d hj)
    subst p
    subst q
    have hheight : height (drop (drop b t.col Q) t.col P) t.col =
        height b t.col + 2 := by simp only [height_drop_same] <;> omega
    by_cases he : t.row = height b t.col + 2
    · left
      have hcell : targetCell t = ⟨t.col, height (drop b t.col Q) t.col + 1⟩ := by
        unfold targetCell
        rw [height_drop_same, he]
      rw [hcell]
      exact candidate_stoneAt_new_top (drop b t.col Q) t.col P
    · right
      rw [hheight]
      constructor <;> omega
  · have hp : p ≠ t.col := fun hp => hq (candidate_reply_target_column d hcover hout ht hp)
    have hqt : t.col ≠ q := Ne.symm hq
    have hpt : t.col ≠ p := Ne.symm hp
    right
    simpa [height, drop, hqt, hpt] using And.intro hpos heven

/-- Candidate target geometry and outside parity survive until a target is acquired.
This is a board-level round statement, not an assumption of C6 or structural safety. -/
theorem candidate_targets_preserved {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q p : Col}
    (d : CandidateData H b L ts E) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (hcover : height (drop b q Q) q < H → p = q)
    (hout : inJ ts q = false → inJ ts p = false) :
    (∃ t ∈ ts, stoneAt (drop (drop b q Q) p P) (targetCell t) = some P) ∨
      ((∀ t ∈ ts, height (drop (drop b q Q) p P) t.col < t.row ∧
        (t.row - height (drop (drop b q Q) p P) t.col) % 2 = 0) ∧
       (∀ t ∈ ts, t.row ≤ H ∧ targetCell t ∈ L.cells) ∧
       outside H (drop (drop b q Q) p P) ts % 2 = 0) := by
  classical
  by_cases hacquired : ∃ t ∈ ts,
      stoneAt (drop (drop b q Q) p P) (targetCell t) = some P
  · exact Or.inl hacquired
  · right
    refine ⟨?_, ?_, candidate_outside_even_after_round d hq hp hcover hout⟩
    · intro t ht
      rcases candidate_target_after_round d hcover hout ht with hs | hg
      · exact False.elim (hacquired ⟨t, ht, hs⟩)
      · exact hg
    · intro t ht
      exact ⟨d.belowRoof t ht, d.onLine t ht⟩

/-- With the independently proved structural closure, a no-hit round preserves
all fields of CandidateData. No candidate invariant is assumed at the new board. -/
theorem candidateData_after_round_no_hit {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop} {q p : Col}
    (d : CandidateData H b L ts E) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (hcover : height (drop b q Q) q < H → p = q)
    (hout : inJ ts q = false → inJ ts p = false)
    (hs : Structural H (drop (drop b q Q) p P) E)
    (hnohit : (ts.any (fun t =>
      stoneAt (drop (drop b q Q) p P) (targetCell t) == some P)) = false) :
    CandidateData H (drop (drop b q Q) p P) L ts E := by
  have hnone : ¬ ∃ t ∈ ts,
      stoneAt (drop (drop b q Q) p P) (targetCell t) = some P := by
    intro he
    have hh := (target_hit_iff _ ts).mpr he
    rw [hnohit] at hh
    cases hh
  have htargets : ∀ t ∈ ts,
      height (drop (drop b q Q) p P) t.col < t.row ∧
      (t.row - height (drop (drop b q Q) p P) t.col) % 2 = 0 := by
    intro t ht
    rcases candidate_target_after_round d hcover hout ht with hh | hg
    · exact False.elim (hnone ⟨t, ht, hh⟩)
    · exact hg
  refine {
    structural := hs
    nonempty := d.nonempty
    distinctColumns := d.distinctColumns
    lineValid := d.lineValid
    otherBlocked := ?_
    onLine := d.onLine
    positive := fun t ht => (htargets t ht).1
    evenGap := fun t ht => (htargets t ht).2
    belowRoof := d.belowRoof
    outsideEven := candidate_outside_even_after_round d hq hp hcover hout }
  intro M hm hne
  exact hasP_drop_preserves (hasP_drop_preserves (d.otherBlocked M hm hne) q Q) p P

/-- The executable settle operation agrees with the no-hit candidate invariant. -/
theorem candidate_reply_phase_no_hit {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {q p : Col}
    (hr : rawReply H b q (.candidate L ts) = some (p, .candidate L ts))
    (hnohit : (ts.any (fun t =>
      stoneAt (drop (drop b q Q) p P) (targetCell t) == some P)) = false) :
    reply H b q (.candidate L ts) = some (p, .candidate L ts) := by
  simp only [reply, hr, Option.map_some, settle, hnohit, Bool.false_eq_true, ite_false]

#print axioms candidate_reply_legal
#print axioms candidate_targets_preserved

end OddHeight
