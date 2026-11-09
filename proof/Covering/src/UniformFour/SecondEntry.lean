import UniformFour.CClosure
import OddHeight.OpeningProofs

/-! Second-player entry witnesses for the exact U2 certificates.
The parity split is in the proof only; it is not the executable response rule.
Local compilation and replay records accompany this reviewed copy. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

def partner : Col → Col
  | c1 => c2 | c2 => c1 | c3 => c4 | c4 => c3

@[simp] theorem partner_ne (q : Col) : partner q ≠ q := by cases q <;> decide
@[simp] theorem ne_partner (q : Col) : q ≠ partner q := by cases q <;> decide

def singleQException (q : Col) (x : Cell) : Prop := x.col = q ∧ x.row = 2

theorem cross_opening_Q_unique {q p : Col} {x : Cell}
    (h : stoneAt (afterRound empty q p) x = some Q) : x = ⟨q,1⟩ :=
  oneStone_cell (stoneAt_drop_other_colour (by decide : Q ≠ P) p h)

theorem cross_opening_height_le_one {q p : Col} (ne : q ≠ p) (c : Col) :
    height (afterRound empty q p) c ≤ 1 := by
  by_cases cp : c = p
  · subst c
    simp [height, drop, Ne.symm ne]
  · by_cases cq : c = q
    · subst c
      simp [height, drop, ne]
    · simp [height, drop, cp, cq]

theorem cross_opening_legal {H : Nat} (positive : 0 < H) (q : Col) :
    Legal H (drop empty q Q) (partner q) := by
  simp [Legal, height, drop]
  exact positive

theorem cross_opening_complete {H : Nat} {q p : Col} (ne : q ≠ p) :
    ExceptionComplete H (afterRound empty q p) (singleQException q) := by
  intro x hx
  rcases hx with ⟨row,Qcell,_⟩ | ⟨_,_,row,top⟩
  · have same := cross_opening_Q_unique Qcell
    have r := congrArg Cell.row same
    dsimp at r
    ((try dsimp only at *); omega)
  · have same := cross_opening_Q_unique top
    have c := congrArg Cell.col same
    have r := congrArg Cell.row same
    dsimp at c r
    exact ⟨c, by ((try dsimp only at *); omega)⟩

theorem cross_opening_structural {H : Nat} (positive : 0 < H) (q : Col) :
    Structural H (afterRound empty q (partner q)) (singleQException q) := by
  refine ⟨?_, ?_, ?_, cross_opening_complete (ne_partner q)⟩
  · exact drop_bounded (drop_bounded (empty_bounded H) (empty_move_legal positive q) Q)
      (cross_opening_legal positive q) P
  · intro win
    exact oneStone_no_win H q Q (wins_drop_other_colour (by decide : Q ≠ P) (partner q) win)
  · intro c _ three
    have low := cross_opening_height_le_one (ne_partner q) c
    ((try dsimp only at *); omega)

/-- The only two extra nonbottom diagonals come from an OUTER row-two
potential exception. This keeps the even-height outer openings honest. -/
theorem single_exception_check_lines {H : Nat} {q : Col} {L : Line}
    (h : ToCheck H (singleQException q) L) :
    L = .horizontal 1 ∨ L = rowTwo ∨ L = rise ∨ L = down ∨
      (q = c1 ∧ L = .rising 2) ∨ (q = c4 ∧ L = .falling 5) := by
  rcases h with ⟨valid, nonvertical, x, mem, touch⟩
  cases L with
  | vertical c r => exact False.elim nonvertical
  | horizontal r =>
      have rr : r = 1 ∨ r = 2 := by
        simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl
        all_goals
          rcases touch with first | ex
          · exact Or.inl first
          · exact Or.inr ex.2
      rcases rr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  | rising r =>
      have lower := (valid ⟨c1,r⟩ (by simp [Line.cells])).1
      have rr : r = 1 ∨ (q = c1 ∧ r = 2) := by
        simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl
        · rcases touch with first | ⟨col,row⟩
          · exact Or.inl first
          · exact Or.inr ⟨col.symm,row⟩
        · rcases touch with first | ⟨_,row⟩ <;> left <;> ((try dsimp only at *); omega)
        · rcases touch with first | ⟨_,row⟩ <;> ((try dsimp only at *); omega)
        · rcases touch with first | ⟨_,row⟩ <;> ((try dsimp only at *); omega)
      rcases rr with rfl | ⟨col,rfl⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨col,rfl⟩))))
  | falling r =>
      have lower := (valid ⟨c4,r-3⟩ (by simp [Line.cells])).1
      have rr : r = 4 ∨ (q = c4 ∧ r = 5) := by
        simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl
        · rcases touch with first | ⟨_,row⟩ <;> ((try dsimp only at *); omega)
        · rcases touch with first | ⟨_,row⟩ <;> ((try dsimp only at *); omega)
        · rcases touch with first | ⟨_,row⟩ <;> left <;> ((try dsimp only at *); omega)
        · rcases touch with first | ⟨col,row⟩
          · left; ((try dsimp only at *); omega)
          · right; exact ⟨col.symm,by ((try dsimp only at *); omega)⟩
      rcases rr with rfl | ⟨col,rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨col,rfl⟩))))

theorem cross_opening_bottom (q : Col) :
    HasP (afterRound empty q (partner q)) (.horizontal 1) := by
  refine ⟨⟨partner q,1⟩, ?_, ?_⟩
  · cases q <;> simp [partner, Line.cells]
  · have height0 : height (drop empty q Q) (partner q) = 0 := by
      simp [height, drop]
    simpa [height0] using candidate_stoneAt_new_top (drop empty q Q) (partner q) P

theorem height_one_cross_A0 (q : Col) : A0 1 (afterRound empty q (partner q)) := by
  intro L hL
  have checked := toCheck_mono (cross_opening_complete (ne_partner q)) hL.1
  rcases single_exception_check_lines checked with rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact hL.2 (cross_opening_bottom q)
  · have bad := (hL.1.1 ⟨c1,2⟩ (by simp [rowTwo, Line.cells])).2
    ((try dsimp only at *); omega)
  · have bad := (hL.1.1 ⟨c4,4⟩ (by simp [rise, Line.cells])).2
    ((try dsimp only at *); omega)
  · have bad := (hL.1.1 ⟨c1,4⟩ (by simp [down, Line.cells])).2
    ((try dsimp only at *); omega)
  · have bad := (hL.1.1 ⟨c1,2⟩ (by simp [Line.cells])).2
    ((try dsimp only at *); omega)
  · have bad := (hL.1.1 ⟨c1,5⟩ (by simp [Line.cells])).2
    ((try dsimp only at *); omega)

/-- In even height, each unused column has even remaining capacity. -/
theorem even_opening_odd_pair {H : Nat} (even : H % 2 = 0)
    (positive : 0 < H) (q : Col) (c : Col) :
    OddColumn H (afterRound empty q (partner q)) c ↔ c = q ∨ c = partner q := by
  cases q <;> cases c <;> simp [OddColumn, height, drop, partner] <;> ((try dsimp only at *); omega)

theorem even_opening_empty_guard {H : Nat} {q c : Col} {r : Nat}
    (inside : InBoard H ⟨c,r⟩) (cq : c ≠ q) (cp : c ≠ partner q)
    (even : r % 2 = 0) : Protected H (afterRound empty q (partner q)) ⟨c,r⟩ := by
  apply protected_of_even_height_gap inside
  · have pos : 1 ≤ r := inside.1
    simp [height, drop, cq, cp]
    omega
  · simpa [height, drop, cq, cp] using even

theorem even_opening_guard_outside {H : Nat} (even : H % 2 = 0)
    (positive : 0 < H) {q c : Col} {r : Nat} (cq : c ≠ q) (cp : c ≠ partner q) :
    ∀ t, OddColumn H (afterRound empty q (partner q)) t → (⟨c,r⟩ : Cell).col ≠ t := by
  intro t ht
  rcases (even_opening_odd_pair even positive q t).mp ht with rfl | rfl
  · exact cq
  · exact cp

/-- All four first columns, including the reflected outer exceptional diagonal.
No finite height enumeration occurs: H remains arbitrary throughout. -/
theorem even_cross_opening_B {H : Nat} (even : H % 2 = 0)
    (positive : 0 < H) (q : Col) : B H (afterRound empty q (partner q)) := by
  apply b_of_outside_odd_guards
    (Or.inr (odd_pair_length (ne_partner q) (even_opening_odd_pair even positive q)))
  intro L hL
  have checked := toCheck_mono (cross_opening_complete (ne_partner q)) hL.1
  rcases single_exception_check_lines checked with rfl | rfl | rfl | rfl | ⟨qeq,rfl⟩ | ⟨qeq,rfl⟩
  · exact False.elim (hL.2 (cross_opening_bottom q))
  · cases q
    all_goals
      first
      | (refine ⟨⟨c3,2⟩, by simp [rowTwo, Line.cells], ?_, ?_⟩
         · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
             (by decide) (by decide) (by decide)
         · exact even_opening_guard_outside even positive (by decide) (by decide))
      | (refine ⟨⟨c1,2⟩, by simp [rowTwo, Line.cells], ?_, ?_⟩
         · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
             (by decide) (by decide) (by decide)
         · exact even_opening_guard_outside even positive (by decide) (by decide))
  · cases q with
    | c1 =>
        refine ⟨⟨c4,4⟩, by simp [rise, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [rise, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
    | c2 =>
        apply False.elim; apply hL.2
        exact ⟨⟨c1,1⟩, by simp [rise, Line.cells], by decide⟩
    | c3 =>
        refine ⟨⟨c2,2⟩, by simp [rise, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [rise, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
    | c4 =>
        refine ⟨⟨c2,2⟩, by simp [rise, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [rise, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
  · cases q with
    | c1 =>
        refine ⟨⟨c3,2⟩, by simp [down, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [down, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
    | c2 =>
        refine ⟨⟨c3,2⟩, by simp [down, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [down, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
    | c3 =>
        apply False.elim; apply hL.2
        exact ⟨⟨c4,1⟩, by simp [down, Line.cells], by decide⟩
    | c4 =>
        refine ⟨⟨c1,4⟩, by simp [down, Line.cells], ?_, ?_⟩
        · exact even_opening_empty_guard (hL.1.1 _ (by simp [down, Line.cells]))
            (by decide) (by decide) (by decide)
        · exact even_opening_guard_outside even positive (by decide) (by decide)
  · subst q
    refine ⟨⟨c3,4⟩, by simp [Line.cells], ?_, ?_⟩
    · exact even_opening_empty_guard (hL.1.1 _ (by simp [Line.cells]))
        (by decide) (by decide) (by decide)
    · exact even_opening_guard_outside even positive (by decide) (by decide)
  · subst q
    refine ⟨⟨c2,4⟩, by simp [Line.cells], ?_, ?_⟩
    · exact even_opening_empty_guard (hL.1.1 _ (by simp [Line.cells]))
        (by decide) (by decide) (by decide)
    · exact even_opening_guard_outside even positive (by decide) (by decide)

/-- Two guards in different columns suffice for both ordered exit checks. -/
theorem b_of_guard_or_two_reserves {H : Nat} {b : Board}
    (count : (oddColumns H b).length = 0 ∨ (oddColumns H b).length = 2)
    (guards : ∀ L, Unresolved H b L →
      (∃ x ∈ L.cells, Protected H b x ∧ ∀ t, OddColumn H b t → x.col ≠ t) ∨
      (∃ x ∈ L.cells, ∃ y ∈ L.cells,
        Protected H b x ∧ Protected H b y ∧ x.col ≠ y.col)) : B H b := by
  refine ⟨count, ?_, ?_⟩
  · intro L hL
    rcases guards L hL with ⟨x,hx,hp,_⟩ | ⟨x,hx,y,hy,hp,hp',ne⟩
    · exact ⟨x,hx,hp⟩
    · exact ⟨x,hx,hp⟩
  · intro f t _ _ ht L hL
    rcases guards L hL with ⟨x,hx,hp,outside⟩ | ⟨x,hx,y,hy,hp,hp',ne⟩
    · exact ⟨x,hx,Or.inl ⟨hp,outside t ht⟩⟩
    · by_cases xt : x.col = t
      · have yt : y.col ≠ t := by intro yt; exact ne (xt.trans yt.symm)
        exact ⟨y,hy,Or.inl ⟨hp',yt⟩⟩
      · exact ⟨x,hx,Or.inl ⟨hp,xt⟩⟩

theorem odd_cross_opening_not_odd {H : Nat} (odd : H % 2 = 1) (q : Col) :
    ¬ OddColumn H (afterRound empty q (partner q)) q := by
  cases q <;> simp [OddColumn, height, drop, partner] <;> ((try dsimp only at *); omega)

theorem odd_inner_opening_B {H : Nat} (odd : H % 2 = 1) {q : Col}
    (inner : q = c2 ∨ q = c3) : B H (afterRound empty q (partner q)) := by
  have count : (oddColumns H (afterRound empty q (partner q))).length = 2 := by
    rcases inner with rfl | rfl
    · apply odd_pair_length (f := c3) (t := c4) (by decide)
      intro c; cases c <;> simp [OddColumn, height, drop, partner] <;> ((try dsimp only at *); omega)
    · apply odd_pair_length (f := c1) (t := c2) (by decide)
      intro c; cases c <;> simp [OddColumn, height, drop, partner] <;> ((try dsimp only at *); omega)
  apply b_of_guard_or_two_reserves (Or.inr count)
  intro L hL
  have checked := toCheck_mono (cross_opening_complete (ne_partner q)) hL.1
  rcases single_exception_check_lines checked with rfl | rfl | rfl | rfl | ⟨qeq,rfl⟩ | ⟨qeq,rfl⟩
  · exact False.elim (hL.2 (cross_opening_bottom q))
  · right
    rcases inner with rfl | rfl
    · refine ⟨⟨c3,2⟩, by simp [rowTwo, Line.cells],
        ⟨c4,2⟩, by simp [rowTwo, Line.cells], ?_, ?_, by decide⟩
      · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
          (by decide) (by decide) (by decide)
      · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
          (by decide) (by decide) (by decide)
    · refine ⟨⟨c1,2⟩, by simp [rowTwo, Line.cells],
        ⟨c2,2⟩, by simp [rowTwo, Line.cells], ?_, ?_, by decide⟩
      · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
          (by decide) (by decide) (by decide)
      · exact even_opening_empty_guard (hL.1.1 _ (by simp [rowTwo, Line.cells]))
          (by decide) (by decide) (by decide)
  · rcases inner with rfl | rfl
    · apply False.elim; apply hL.2
      exact ⟨⟨c1,1⟩, by simp [rise, Line.cells], by decide⟩
    · left
      refine ⟨⟨c3,3⟩, by simp [rise, Line.cells], ?_, ?_⟩
      · apply protected_of_even_height_gap (hL.1.1 _ (by simp [rise, Line.cells]))
        · decide
        · decide
      · intro t ht eq
        have tt : t = c3 := eq.symm
        subst t
        exact odd_cross_opening_not_odd odd c3 ht
  · rcases inner with rfl | rfl
    · left
      refine ⟨⟨c2,3⟩, by simp [down, Line.cells], ?_, ?_⟩
      · apply protected_of_even_height_gap (hL.1.1 _ (by simp [down, Line.cells]))
        · decide
        · decide
      · intro t ht eq
        have tt : t = c2 := eq.symm
        subst t
        exact odd_cross_opening_not_odd odd c2 ht
    · apply False.elim; apply hL.2
      exact ⟨⟨c4,1⟩, by simp [down, Line.cells], by decide⟩
  · rcases inner with rfl | rfl <;> cases qeq
  · rcases inner with rfl | rfl <;> cases qeq

theorem odd_outer_opening_C {H : Nat} (odd : H % 2 = 1) (h3 : 3 ≤ H)
    {q : Col} (outer : q = c1 ∨ q = c4) : C H (afterRound empty q q) := by
  rcases outer with rfl | rfl
  · refine ⟨?_, rfl, rfl, ?_⟩
    · intro c; cases c <;> simp [OddColumn, height, drop] <;> ((try dsimp only at *); omega)
    · exact ⟨1,0,rfl,rfl,by decide⟩
  · refine ⟨?_, rfl, rfl, ?_⟩
    · intro c; cases c <;> simp [OddColumn, height, drop] <;> ((try dsimp only at *); omega)
    · exact ⟨0,1,rfl,rfl,by decide⟩

theorem odd_outer_opening_good {H : Nat} (odd : H % 2 = 1) (h3 : 3 ≤ H)
    {q : Col} (outer : q = c1 ∨ q = c4) :
    Legal H (drop empty q Q) q ∧ Good H (afterRound empty q q) := by
  have legal : Legal H (drop empty q Q) q := by
    simp [Legal, height, drop]
    ((try dsimp only at *); omega)
  refine ⟨legal, ?_⟩
  have body := odd_outer_opening_C odd h3 outer
  have st : Structural H (afterRound empty q q) middleExceptions := by
    rcases outer with rfl | rfl
    · have eq : afterRound empty c1 c1 = outerBoard 1 0 := by
        funext c; cases c <;> rfl
      rw [eq]
      exact second_endpoint_structural (SecondEndpoint.outer 1 0 (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
    · have eq : afterRound empty c4 c4 = outerBoard 0 1 := by
        funext c; cases c <;> rfl
      rw [eq]
      exact second_endpoint_structural (SecondEndpoint.outer 0 1 (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
  apply good_of_structural st
  intro _ _
  exact Or.inr (Or.inr body)

/-- For every positive height and every first Q move there really is a legal
qualified response. Neither a certificate existence premise nor an old
strategy theorem is assumed. H=1 and both parity cases are included. -/
theorem second_opening_reply_exists {H : Nat} (positive : 0 < H) (q : Col) :
    ∃ p, Legal H (drop empty q Q) p ∧ Good H (afterRound empty q p) := by
  by_cases one : H = 1
  · subst H
    refine ⟨partner q, cross_opening_legal positive q, ?_⟩
    apply good_of_structural (cross_opening_structural positive q)
    intro _ _
    exact Or.inl (Or.inl (height_one_cross_A0 q))
  by_cases odd : H % 2 = 1
  · have h3 : 3 ≤ H := by ((try dsimp only at *); omega)
    cases q with
    | c1 => exact ⟨c1, odd_outer_opening_good odd h3 (Or.inl rfl)⟩
    | c2 =>
        refine ⟨partner c2, cross_opening_legal positive c2, ?_⟩
        apply good_of_structural (cross_opening_structural positive c2)
        intro _ _
        exact Or.inr (Or.inl (odd_inner_opening_B odd (Or.inl rfl)))
    | c3 =>
        refine ⟨partner c3, cross_opening_legal positive c3, ?_⟩
        apply good_of_structural (cross_opening_structural positive c3)
        intro _ _
        exact Or.inr (Or.inl (odd_inner_opening_B odd (Or.inr rfl)))
    | c4 => exact ⟨c4, odd_outer_opening_good odd h3 (Or.inr rfl)⟩
  · have even : H % 2 = 0 := by ((try dsimp only at *); omega)
    refine ⟨partner q, cross_opening_legal positive q, ?_⟩
    apply good_of_structural (cross_opening_structural positive q)
    intro _ _
    exact Or.inr (Or.inl (even_cross_opening_B even positive q))

theorem second_before_response_no_corners (q : Col) : ¬ BothCorners (drop empty q Q) := by
  intro corners
  have old := stoneAt_drop_other_colour (by decide : P ≠ Q) q corners.1
  exact empty_no_cell ⟨c1,1⟩ P old

/-- The SAME executable priority rule chooses a qualified opening; the proof's
explicit witnesses never replace the selector's chosen action. -/
theorem second_selected_opening_good {H : Nat} (positive : 0 < H)
    {q p : Col} {o : Observation} (obs : Observes H (drop empty q Q) o)
    (chosen : select H (drop empty q Q) q o = some p) :
    Qualified H (drop empty q Q) p := by
  exact select_qualified_of_no_corners obs (second_opening_reply_exists positive q)
    (second_before_response_no_corners q) chosen

end UniformFour.U2
