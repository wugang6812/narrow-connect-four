import UniformFour.BCClosure
import UniformFour.Observations
import OddHeight.SecondTransitions

/-! U2 C's actual column-string exits. We reuse v2's lookup/geometry lemmas,
not its strategy, its I/E/Delay invariant, or a nonloss theorem.
Reviewed local copy; see audit.json and kernel_audit.json. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

theorem alternatingPairs_eq_qp (n : Nat) : alternatingPairs n = qp n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [alternatingPairs, qp, ih]

theorem c_outer_shape {H : Nat} {b : Board} (h : C H b) :
    ∃ a d, b = outerBoard a d ∧ 0 < a + d := by
  rcases h.outerPattern with ⟨a, d, ha, hd, pos⟩
  refine ⟨a, d, ?_, pos⟩
  funext c
  cases c <;> simp [outerBoard, board, ha, hd, h.middleTwo, h.middleThree,
    alternatingPairs_eq_qp]

theorem c_height_at_least_three {H : Nat} {b : Board}
    (bounded : Bounded H b) (h : C H b) : 3 ≤ H := by
  have odd := c_height_odd h
  rcases c_outer_shape h with ⟨a, d, rfl, pos⟩
  have ha := bounded c1
  have hd := bounded c4
  simp only [outer_height_one, outer_height_four] at ha hd
  omega

theorem c_no_bothCorners_after_Q {H : Nat} {b : Board}
    (h : C H b) (q : Col) : ¬ BothCorners (drop b q Q) := by
  intro corners
  have fixed := stoneAt_drop_other_colour (by decide : P ≠ Q) q corners.1
  rcases c_outer_shape h with ⟨a,d,rfl,_⟩
  simpa [outerBoard, board] using fixed

theorem odd_pair_length {H : Nat} {b : Board} {f t : Col}
    (ne : f ≠ t) (pair : ∀ c, OddColumn H b c ↔ c = f ∨ c = t) :
    (oddColumns H b).length = 2 := by
  have h1 := pair c1
  have h2 := pair c2
  have h3 := pair c3
  have h4 := pair c4
  cases f <;> cases t <;> simp_all [OddColumn, oddColumns, allCols]

/-- A useful stronger B witness: a guard outside EVERY odd column makes both
ordered exit checks true with that same guard. -/
theorem b_of_outside_odd_guards {H : Nat} {b : Board}
    (count : (oddColumns H b).length = 0 ∨ (oddColumns H b).length = 2)
    (guards : ∀ L, Unresolved H b L → ∃ x ∈ L.cells,
      Protected H b x ∧ ∀ t, OddColumn H b t → x.col ≠ t) : B H b := by
  refine ⟨count, ?_, ?_⟩
  · intro L hL
    rcases guards L hL with ⟨x, hx, hp, _⟩
    exact ⟨x, hx, hp⟩
  · intro f t _ _ ht L hL
    rcases guards L hL with ⟨x, hx, hp, outside⟩
    exact ⟨x, hx, Or.inl ⟨hp, outside t ht⟩⟩

theorem protected_of_even_height_gap {H : Nat} {b : Board} {x : Cell}
    (inside : InBoard H x) (pos : height b x.col < x.row)
    (even : (x.row - height b x.col) % 2 = 0) : Protected H b x :=
  ⟨inside, Or.inr ⟨cell_empty_above_height pos, pos, even⟩⟩

/-- Exact finite geometric check for the two middle-event exits. -/
theorem middle_exit_B {H : Nat} {b : Board}
    (complete : ExceptionComplete H b middleExceptions)
    (pair : ∀ c, OddColumn H b c ↔ c = c1 ∨ c = c4)
    (bottom : HasP b (.horizontal 1)) (row2 : HasP b rowTwo)
    (h2 : height b c2 = 1) (h3 : height b c3 = 1) : B H b := by
  apply b_of_outside_odd_guards (Or.inr (odd_pair_length (by decide) pair))
  intro L hL
  have casesL := middle_check_lines (toCheck_mono complete hL.1)
  rcases casesL with rfl | rfl | rfl | rfl
  · exact False.elim (hL.2 bottom)
  · refine ⟨⟨c3,3⟩, by simp [rise, Line.cells], ?_, ?_⟩
    · apply protected_of_even_height_gap
      · exact hL.1.1 _ (by simp [rise, Line.cells])
      · simpa [h3]
      · simp [h3]
    · intro t ht
      rcases (pair t).mp ht with rfl | rfl <;> decide
  · refine ⟨⟨c2,3⟩, by simp [down, Line.cells], ?_, ?_⟩
    · apply protected_of_even_height_gap
      · exact hL.1.1 _ (by simp [down, Line.cells])
      · simpa [h2]
      · simp [h2]
    · intro t ht
      rcases (pair t).mp ht with rfl | rfl <;> decide
  · exact False.elim (hL.2 row2)

theorem middle_event_elementary {H a d : Nat} (hH : 1 ≤ H)
    (ha : 2*a ≤ H) (hd : 2*d ≤ H) :
    ElementarySecond H (a1 a d) ∧ ElementarySecond H (a2 a d) := by
  constructor
  all_goals
    constructor
    · intro c; cases c <;> simp_all [height, a1, a2, board] <;> omega
    · intro c hc r hq
      rcases hc with rfl | rfl <;> simp_all [height, a1, a2, board] <;> omega
    · intro c hc r hq
      rcases hc with rfl | rfl <;> simp_all [height, a1, a2, board] <;> omega
    · intro c hc hq
      rcases hc with rfl | rfl <;> simp_all [height, a1, a2, board] <;> omega
    · intro c hc hn hq
      rcases hc with rfl | rfl <;> simp_all [height, a1, a2, board] <;> omega
    · intro r hq
      simp_all [height, a1, a2, board] <;> omega

theorem c_middle_events_B {H a d : Nat} (odd : H % 2 = 1)
    (ha : 2*a ≤ H) (hd : 2*d ≤ H) (pos : 0 < a+d) :
    B H (a1 a d) ∧ B H (a2 a d) := by
  have hH : 1 ≤ H := by omega
  have structural := middle_event_elementary hH ha hd
  have rowFirst : HasP (a1 a d) rowTwo := by
    by_cases ap : 0 < a
    · refine ⟨⟨c1,2⟩, by simp [rowTwo, Line.cells], ?_⟩
      simp [a1, board]
      omega
    · refine ⟨⟨c4,2⟩, by simp [rowTwo, Line.cells], ?_⟩
      simp [a1, board]
      omega
  have rowSecond : HasP (a2 a d) rowTwo := by
    by_cases ap : 0 < a
    · refine ⟨⟨c1,2⟩, by simp [rowTwo, Line.cells], ?_⟩
      simp [a2, board]
      omega
    · refine ⟨⟨c4,2⟩, by simp [rowTwo, Line.cells], ?_⟩
      simp [a2, board]
      omega
  constructor
  · refine middle_exit_B structural.1.complete ?_ ?_ rowFirst ?_ ?_
    · intro c; cases c <;> simp [OddColumn, height, a1, board] <;> omega
    · exact ⟨⟨c3,1⟩, by simp [Line.cells], by simp [a1, board, readRow]⟩
    · simp [height, a1, board]
    · simp [height, a1, board]
  · refine middle_exit_B structural.2.complete ?_ ?_ rowSecond ?_ ?_
    · intro c; cases c <;> simp [OddColumn, height, a2, board] <;> omega
    · exact ⟨⟨c2,1⟩, by simp [Line.cells], by simp [a2, board, readRow]⟩
    · simp [height, a2, board]
    · simp [height, a2, board]

/-- At a full-left exit, only the rising bottom diagonal can remain unresolved;
its row-three middle guard is outside the two odd columns. -/
theorem c_left_full_B {H a d : Nat} (odd : H % 2 = 1)
    (full : 2*a+1 = H) (hd : 2*d ≤ H) (h3 : 3 ≤ H) : B H (a3 a d) := by
  have st := second_endpoint_structural (SecondEndpoint.event3 a d full hd (by omega))
  have pair : ∀ c, OddColumn H (a3 a d) c ↔ c = c2 ∨ c = c4 := by
    intro c; cases c <;> simp [OddColumn, height, a3, board] <;> omega
  apply b_of_outside_odd_guards (Or.inr (odd_pair_length (by decide) pair))
  intro L hL
  rcases middle_check_lines (toCheck_mono st.complete hL.1) with rfl | rfl | rfl | rfl
  · apply False.elim; apply hL.2
    exact ⟨⟨c3,1⟩, by simp [Line.cells], by simp [a3, board, readRow]⟩
  · refine ⟨⟨c3,3⟩, by simp [rise, Line.cells], ?_, ?_⟩
    · apply protected_of_even_height_gap (hL.1.1 _ (by simp [rise, Line.cells]))
      · simp [height, a3, board]
      · simp [height, a3, board]
    · intro t ht
      rcases (pair t).mp ht with rfl | rfl <;> decide
  · have roof : 4 ≤ H := (hL.1.1 ⟨c1,4⟩ (by simp [down, Line.cells])).2
    apply False.elim; apply hL.2
    refine ⟨⟨c1,4⟩, by simp [down, Line.cells], ?_⟩
    simp [a3, board]
    omega
  · apply False.elim; apply hL.2
    refine ⟨⟨c1,2⟩, by simp [rowTwo, Line.cells], ?_⟩
    simp [a3, board]
    omega

theorem c_right_full_B {H a d : Nat} (odd : H % 2 = 1)
    (ha : 2*a ≤ H) (full : 2*d+1 = H) (h3 : 3 ≤ H) : B H (a4 a d) := by
  have st := second_endpoint_structural (SecondEndpoint.event4 a d ha full (by omega))
  have pair : ∀ c, OddColumn H (a4 a d) c ↔ c = c1 ∨ c = c3 := by
    intro c; cases c <;> simp [OddColumn, height, a4, board] <;> omega
  apply b_of_outside_odd_guards (Or.inr (odd_pair_length (by decide) pair))
  intro L hL
  rcases middle_check_lines (toCheck_mono st.complete hL.1) with rfl | rfl | rfl | rfl
  · apply False.elim; apply hL.2
    exact ⟨⟨c2,1⟩, by simp [Line.cells], by simp [a4, board, readRow]⟩
  · have roof : 4 ≤ H := (hL.1.1 ⟨c4,4⟩ (by simp [rise, Line.cells])).2
    apply False.elim; apply hL.2
    refine ⟨⟨c4,4⟩, by simp [rise, Line.cells], ?_⟩
    simp [a4, board]
    omega
  · refine ⟨⟨c2,3⟩, by simp [down, Line.cells], ?_, ?_⟩
    · apply protected_of_even_height_gap (hL.1.1 _ (by simp [down, Line.cells]))
      · simp [height, a4, board]
      · simp [height, a4, board]
    · intro t ht
      rcases (pair t).mp ht with rfl | rfl <;> decide
  · apply False.elim; apply hL.2
    refine ⟨⟨c4,2⟩, by simp [rowTwo, Line.cells], ?_⟩
    simp [a4, board]
    omega

theorem c_cover_body {H : Nat} {b : Board} {q : Col}
    (h : C H b) (outer : q = c1 ∨ q = c4)
    (hp : Legal H (drop b q Q) q) : C H (afterRound b q q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact (odd_column_cover_iff hp c).mpr (h.fourOdd c)
  · rcases outer with rfl | rfl <;> simpa [drop] using h.middleTwo
  · rcases outer with rfl | rfl <;> simpa [drop] using h.middleThree
  · rcases h.outerPattern with ⟨a,d,ha,hd,pos⟩
    rcases outer with rfl | rfl
    · exact ⟨a+1,d, by simp [drop, ha, alternatingPairs, List.append_assoc],
        by simpa [drop] using hd, by omega⟩
    · exact ⟨a,d+1, by simpa [drop] using ha,
        by simp [drop, hd, alternatingPairs, List.append_assoc], by omega⟩

theorem c_cover_good {H : Nat} {b : Board} {q : Col}
    (common : Common H b) (h : C H b) (hq : Legal H b q)
    (outer : q = c1 ∨ q = c4) (hp : Legal H (drop b q Q) q) :
    Good H (afterRound b q q) := by
  apply good_of_structural (structural_after_cover (common_structural common)
    hq hp (c_Q_move_safe common h hq) (Or.inl rfl))
  intro _ _
  exact Or.inr (Or.inr (c_cover_body h outer hp))

/-- All four C events are handled, with both empty-outer boundary cases allowed.
The state is rechecked as B; this is not an appeal to the old phase controller. -/
theorem c_reply_exists {H : Nat} {b : Board} {q : Col}
    (common : Common H b) (h : C H b) (hq : Legal H b q) :
    ∃ p, Legal H (drop b q Q) p ∧ Good H (afterRound b q p) := by
  have odd := c_height_odd h
  have h3 := c_height_at_least_three common.1.1 h
  rcases c_outer_shape h with ⟨a,d,eq,pos⟩
  subst b
  have ha : 2*a ≤ H := by simpa using common.1.1 c1
  have hd : 2*d ≤ H := by simpa using common.1.1 c4
  have cross : Legal H (drop (outerBoard a d) c2 Q) c3 ∧
      Legal H (drop (outerBoard a d) c3 Q) c2 ∧
      Legal H (drop (outerBoard a d) c1 Q) c3 ∧
      Legal H (drop (outerBoard a d) c4 Q) c2 := by
    simp [Legal, height, drop, outerBoard, board]
    omega
  cases q with
  | c1 =>
      by_cases cover : Legal H (drop (outerBoard a d) c1 Q) c1
      · exact ⟨c1, cover, c_cover_good common h hq (Or.inl rfl) cover⟩
      · have full : 2*a+1 = H := by
          have bound := drop_bounded common.1.1 hq Q c1
          simp only [Legal, height_drop_same, outer_height_one] at cover bound
          omega
        refine ⟨c3, cross.2.2.1, ?_⟩
        simp only [afterRound, outer_event1_shape]
        apply good_of_structural
          (second_endpoint_structural (SecondEndpoint.event3 a d full hd (by omega)))
        intro _ _
        exact Or.inr (Or.inl (c_left_full_B odd full hd h3))
  | c2 =>
      refine ⟨c3, cross.1, ?_⟩
      simp only [afterRound, outer_event2_shape]
      apply good_of_structural (middle_event_elementary (by omega) ha hd).1.structural
      intro _ _
      exact Or.inr (Or.inl (c_middle_events_B odd ha hd pos).1)
  | c3 =>
      refine ⟨c2, cross.2.1, ?_⟩
      simp only [afterRound, outer_event3_shape]
      apply good_of_structural (middle_event_elementary (by omega) ha hd).2.structural
      intro _ _
      exact Or.inr (Or.inl (c_middle_events_B odd ha hd pos).2)
  | c4 =>
      by_cases cover : Legal H (drop (outerBoard a d) c4 Q) c4
      · exact ⟨c4, cover, c_cover_good common h hq (Or.inr rfl) cover⟩
      · have full : 2*d+1 = H := by
          have bound := drop_bounded common.1.1 hq Q c4
          simp only [Legal, height_drop_same, outer_height_four] at cover bound
          omega
        refine ⟨c2, cross.2.2.2, ?_⟩
        simp only [afterRound, outer_event4_shape]
        apply good_of_structural
          (second_endpoint_structural (SecondEndpoint.event4 a d ha full (by omega)))
        intro _ _
        exact Or.inr (Or.inl (c_right_full_B odd ha full h3))

end UniformFour.U2
