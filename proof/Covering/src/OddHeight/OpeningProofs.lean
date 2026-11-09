import OddHeight.Assembly
import OddHeight.Support

/-!
Concrete opening certificates for the odd-height proof.
Local compilation and replay records accompany this reviewed copy.
This module does not assume C6 soundness or either global nonloss theorem.
-/
namespace OddHeight
open Player Col

/-- Four constructors always give a nonempty line. -/
theorem winning_cell_exists {H : Nat} {b : Board} {p : Player}
    (hw : Wins H b p) : ∃ x, stoneAt b x = some p := by
  rcases hw with ⟨L, _, hL⟩
  cases L with
  | horizontal r => exact ⟨⟨c1,r⟩, hL _ (by simp [Line.cells])⟩
  | vertical c r => exact ⟨⟨c,r⟩, hL _ (by simp [Line.cells])⟩
  | rising r => exact ⟨⟨c1,r⟩, hL _ (by simp [Line.cells])⟩
  | falling r => exact ⟨⟨c1,r⟩, hL _ (by simp [Line.cells])⟩

theorem firstBoard_no_Q_cell (x : Cell) : stoneAt firstBoard x ≠ some Q := by
  rcases x with ⟨c,r⟩
  cases c <;> cases r with
  | zero => simp [stoneAt]
  | succ r =>
      cases r <;> simp [stoneAt, firstBoard, board]

theorem firstBoard_no_Q_win (H : Nat) : ¬ Wins H firstBoard Q := by
  intro hw
  rcases winning_cell_exists hw with ⟨x,hx⟩
  exact firstBoard_no_Q_cell x hx

theorem firstBoard_bounded {H : Nat} (h1 : 1 ≤ H) : Bounded H firstBoard := by
  intro c
  cases c <;> simp [height, firstBoard, board] <;> omega

theorem firstBoard_no_exception (H : Nat) (x : Cell) :
    ¬ exceptionSet H firstBoard x := by
  intro hx
  rcases hx with actual | potential
  · exact firstBoard_no_Q_cell x actual.2.1
  · exact firstBoard_no_Q_cell ⟨x.col, height firstBoard x.col⟩ potential.2.2.2

theorem firstBoard_structure {H : Nat} (h1 : 1 ≤ H) :
    Structural H firstBoard (fun _ => False) := by
  refine ⟨firstBoard_bounded h1, firstBoard_no_Q_win H, ?_, ?_⟩
  · intro c _ h3
    cases c <;> simp [height, firstBoard, board] at h3
  · intro x hx
    exact firstBoard_no_exception H x hx

/-- A complete classification of the nonvertical bottom lines, with validity checked. -/
theorem bottom_line_cases {H : Nat} {L : Line}
    (valid : ValidLine H L) (nonvertical : L.Nonvertical)
    (bottom : ∃ x ∈ L.cells, x.row = 1) :
    L = .horizontal 1 ∨ L = rise ∨ L = down := by
  rcases bottom with ⟨x,hx,hr⟩
  cases L with
  | vertical c r => exact False.elim nonvertical
  | horizontal r =>
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        change r = 1 at hr
        subst r
        exact Or.inl rfl
  | rising r =>
      have hmin : 1 ≤ r := (valid ⟨c1,r⟩ (by simp [Line.cells])).1
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        dsimp at hr
        have he : r = 1 := by omega
        subst r
        exact Or.inr (Or.inl rfl)
  | falling r =>
      have hmin : 1 ≤ r - 3 := (valid ⟨c4,r-3⟩ (by simp [Line.cells])).1
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        dsimp at hr
        have he : r = 4 := by omega
        rw [he]
        exact Or.inr (Or.inr rfl)

theorem firstBoard_blocks_bottom : HasP firstBoard (.horizontal 1) := by
  exact ⟨⟨c1,1⟩, by simp [Line.cells], by decide⟩

theorem firstBoard_blocks_rise : HasP firstBoard rise := by
  exact ⟨⟨c1,1⟩, by simp [rise, Line.cells], by decide⟩

theorem firstBoard_other_lines {H : Nat} {L : Line}
    (check : ToCheck H (fun _ => False) L) (ne : L ≠ down) :
    HasP firstBoard L := by
  rcases check with ⟨hv,hn,x,hx,hbottom | hfalse⟩
  · rcases bottom_line_cases hv hn ⟨x,hx,hbottom⟩ with he | he | he
    · subst L; exact firstBoard_blocks_bottom
    · subst L; exact firstBoard_blocks_rise
    · exact False.elim (ne he)
  · exact False.elim hfalse

theorem down_valid {H : Nat} (h4 : 4 ≤ H) : ValidLine H down := by
  intro x hx
  simp only [down, Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals
    constructor <;> dsimp <;> omega

theorem firstBoard_outside_count (H : Nat) :
    outside H firstBoard [⟨c3,2⟩] = (H - 1) + H + H := by
  simp [outside, allCols, inJ, height, firstBoard, board]

/-- The actual C6 premise certificate for theorem A; no soundness of C6 is assumed. -/
theorem firstBoard_candidate {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1) :
    CandidateHyp H firstBoard down [⟨c3,2⟩] := by
  refine ⟨(fun _ => False), ?_⟩
  refine {
    structural := firstBoard_structure (by omega)
    nonempty := by decide
    distinctColumns := by decide
    lineValid := down_valid (by omega)
    otherBlocked := ?_
    onLine := ?_
    positive := ?_
    evenGap := ?_
    belowRoof := ?_
    outsideEven := ?_
  }
  · intro L hL hne
    exact firstBoard_other_lines hL hne
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact first_target_on_down
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    decide
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    decide
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    dsimp
    omega
  · rw [firstBoard_outside_count]
    omega

/-- At H<=3 the descending diagonal is not a board line. -/
theorem down_invalid_small {H : Nat} (small : H ≤ 3) : ¬ ValidLine H down := by
  intro hv
  have hh : 4 ≤ H := (hv ⟨c1,4⟩ (by simp [down, Line.cells])).2
  omega

/-- The edge opening has a permanent-defense certificate at H=1 or H=3.
    This certificate does not falsely claim the reserved square (c3,2) exists at H=1. -/
theorem firstBoard_permanent_small {H : Nat} (h1 : 1 ≤ H) (small : H ≤ 3) :
    PermanentHyp H firstBoard := by
  refine ⟨(fun _ => False), firstBoard_structure h1, ?_⟩
  intro L hL
  apply firstBoard_other_lines hL
  intro he
  exact down_invalid_small small (he ▸ hL.1)

theorem firstBoard_phase_certificate {H : Nat} (odd : H % 2 = 1) :
    ClaudeInvariant H firstBoard (firstPhase H) := by
  have h1 : 1 ≤ H := by omega
  refine ⟨firstBoard_bounded h1, firstBoard_no_Q_win H, ?_⟩
  rcases odd_height_cases H odd with h | h | h5
  · subst H
    change PermanentHyp 1 firstBoard
    exact firstBoard_permanent_small (by decide) (by decide)
  · subst H
    change PermanentHyp 3 firstBoard
    exact firstBoard_permanent_small (by decide) (by decide)
  · have hn1 : H ≠ 1 := by omega
    have hn3 : H ≠ 3 := by omega
    simp only [firstPhase, if_neg hn1, if_neg hn3, PhaseInvariant]
    exact firstBoard_candidate h5 odd


/-- Four-in-a-row contains two distinct cells, so one stone of a color cannot win. -/
theorem no_win_of_unique_colored_cell {H : Nat} {b : Board} {p : Player}
    (unique : ∀ x y, stoneAt b x = some p → stoneAt b y = some p → x = y) :
    ¬ Wins H b p := by
  rintro ⟨L,_,all⟩
  cases L with
  | horizontal r =>
      have he := unique ⟨c1,r⟩ ⟨c2,r⟩
        (all _ (by simp [Line.cells])) (all _ (by simp [Line.cells]))
      have hc := congrArg Cell.col he
      cases hc
  | vertical c r =>
      have he := unique ⟨c,r⟩ ⟨c,r+1⟩
        (all _ (by simp [Line.cells])) (all _ (by simp [Line.cells]))
      have hr := congrArg Cell.row he
      dsimp at hr
      omega
  | rising r =>
      have he := unique ⟨c1,r⟩ ⟨c2,r+1⟩
        (all _ (by simp [Line.cells])) (all _ (by simp [Line.cells]))
      have hc := congrArg Cell.col he
      cases hc
  | falling r =>
      have he := unique ⟨c1,r⟩ ⟨c2,r-1⟩
        (all _ (by simp [Line.cells])) (all _ (by simp [Line.cells]))
      have hc := congrArg Cell.col he
      cases hc

@[simp] theorem empty_column (c : Col) : empty c = [] := by cases c <;> rfl

theorem oneStone_cell {c : Col} {p : Player} {x : Cell}
    (hx : stoneAt (drop empty c p) x = some p) : x = ⟨c,1⟩ := by
  rcases x with ⟨d,r⟩
  by_cases hd : d = c
  · subst d
    cases r with
    | zero => simp [stoneAt] at hx
    | succ r =>
        cases r with
        | zero => rfl
        | succ r => simp [stoneAt, drop] at hx
  · simp [stoneAt, drop, hd] at hx

theorem oneStone_no_win (H : Nat) (c : Col) (p : Player) :
    ¬ Wins H (drop empty c p) p := by
  apply no_win_of_unique_colored_cell
  intro x y hx hy
  exact (oneStone_cell hx).trans (oneStone_cell hy).symm

theorem innerZero_Q_cell {x : Cell} (hx : stoneAt (innerBoard 0) x = some Q) :
    x = ⟨c2,1⟩ := by
  rcases x with ⟨c,r⟩
  cases c <;> cases r with
  | zero => simp [stoneAt] at hx
  | succ r =>
      cases r with
      | zero => simp [stoneAt, innerBoard, qp, board] at hx ⊢
      | succ r => simp [stoneAt, innerBoard, qp, board] at hx

theorem outerOneZero_Q_cell {x : Cell} (hx : stoneAt (outerBoard 1 0) x = some Q) :
    x = ⟨c1,1⟩ := by
  rcases x with ⟨c,r⟩
  cases c <;> cases r with
  | zero => simp [stoneAt] at hx
  | succ r =>
      cases r with
      | zero => simp [stoneAt, outerBoard, qp, board] at hx ⊢
      | succ r =>
          cases r <;> simp [stoneAt, outerBoard, qp, board] at hx

theorem innerZero_entry {H : Nat} (h1 : 1 ≤ H) :
    ClaudeInvariant H (innerBoard 0) .innerWait := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    cases c <;> simp [height, innerBoard, qp, board] <;> omega
  · apply no_win_of_unique_colored_cell
    intro x y hx hy
    exact (innerZero_Q_cell hx).trans (innerZero_Q_cell hy).symm
  · exact ⟨0, rfl, by omega⟩

theorem outerOneZero_entry {H : Nat} (h2 : 2 ≤ H) :
    ClaudeInvariant H (outerBoard 1 0) .outerWait := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    cases c <;> simp [height, outerBoard, qp, board] <;> omega
  · apply no_win_of_unique_colored_cell
    intro x y hx hy
    exact (outerOneZero_Q_cell hx).trans (outerOneZero_Q_cell hy).symm
  · exact ⟨1, 0, by decide, rfl, by omega, by omega⟩

def secondInitial (q : Col) : Board :=
  drop (drop empty q Q) (secondOpening q).1 P

def secondInitialPhase (q : Col) : Phase := (secondOpening q).2.1
def secondInitialFlip (q : Col) : Bool := (secondOpening q).2.2

theorem second_opening_normalizes (q : Col) :
    (logicalBoard (secondInitialFlip q) (secondInitial q) = outerBoard 1 0 ∧
      secondInitialPhase q = .outerWait) ∨
    (logicalBoard (secondInitialFlip q) (secondInitial q) = innerBoard 0 ∧
      secondInitialPhase q = .innerWait) := by
  cases q with
  | c1 =>
      left; constructor
      · funext c; cases c <;> rfl
      · rfl
  | c2 =>
      right; constructor
      · funext c; cases c <;> rfl
      · rfl
  | c3 =>
      right; constructor
      · funext c; cases c <;> rfl
      · rfl
  | c4 =>
      left; constructor
      · funext c; cases c <;> rfl
      · rfl

theorem second_opening_entry {H : Nat} (h2 : 2 ≤ H) (q : Col) :
    ClaudeInvariant H (logicalBoard (secondInitialFlip q) (secondInitial q))
      (secondInitialPhase q) := by
  rcases second_opening_normalizes q with ⟨hb,hp⟩ | ⟨hb,hp⟩
  · rw [hb,hp]
    exact outerOneZero_entry h2
  · rw [hb,hp]
    exact innerZero_entry (by omega)

theorem second_opening_reply_legal {H : Nat} (h2 : 2 ≤ H) (q : Col) :
    Legal H (drop empty q Q) (secondOpening q).1 := by
  cases q <;> simp [Legal, height, drop, secondOpening] <;> omega

/-- The empty board has no occupied cell, independently of the height. -/
theorem empty_no_cell (x : Cell) (p : Player) : stoneAt empty x ≠ some p := by
  simp [stoneAt]

theorem empty_no_win (H : Nat) (p : Player) : ¬ Wins H empty p := by
  intro hw
  rcases winning_cell_exists hw with ⟨x,hx⟩
  exact empty_no_cell x p hx

theorem empty_bounded (H : Nat) : Bounded H empty := by
  intro c
  simp [height]

theorem empty_move_legal {H : Nat} (positive : 0 < H) (c : Col) :
    Legal H empty c := by
  simpa [Legal, height] using positive

/-- The abstract first-player entry is exactly the actual edge opening. -/
theorem firstBoard_eq_opening : firstBoard = drop empty c1 P := by
  funext c
  cases c <;> rfl

theorem first_opening_legal {H : Nat} (odd : H % 2 = 1) :
    Legal H empty c1 := empty_move_legal (by omega) c1

/-- Both physical opening moves are legal; reflection is used only afterwards. -/
theorem second_initial_moves_legal {H : Nat} (h2 : 2 ≤ H) (q : Col) :
    Legal H empty q ∧ Legal H (drop empty q Q) (secondOpening q).1 := by
  exact ⟨empty_move_legal (by omega) q, second_opening_reply_legal h2 q⟩

theorem second_initial_bounded {H : Nat} (h2 : 2 ≤ H) (q : Col) :
    Bounded H (secondInitial q) := by
  exact drop_bounded
    (drop_bounded (empty_bounded H) (empty_move_legal (by omega) q) Q)
    (second_opening_reply_legal h2 q) P

/-- Q cannot already have won during the two-move physical opening. -/
theorem second_initial_no_Q_win (H : Nat) (q : Col) :
    ¬ Wins H (secondInitial q) Q := by
  intro hw
  have before := wins_drop_other_colour (by decide : Q ≠ P) (secondOpening q).1 hw
  exact oneStone_no_win H q Q before

#print axioms firstBoard_candidate
#print axioms firstBoard_permanent_small
#print axioms firstBoard_phase_certificate
#print axioms second_opening_entry

end OddHeight
