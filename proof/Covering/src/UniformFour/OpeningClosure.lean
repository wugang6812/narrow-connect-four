import UniformFour.AClosure
import OddHeight.OpeningProofs
import OddHeight.SecondTransitions

/-!
U2, section 5: the two concrete first-player opening shapes.
Reviewed additive copy. See audit.json and kernel_audit.json for validation.
The statements below quantify arbitrary natural parameters, not a height cutoff.
P is the first player in this module. No conclusion about future safety occurs
as a field of a shape. The shapes are literal lists of already placed stones.
-/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- First uncertified shape, U2 §5.3. -/
def wBoard (a d : Nat) : Board := board ([P] ++ qp a) [] [] (qp d)
/-- Second uncertified shape, U2 §5.4. -/
def vBoard (a b e d : Nat) : Board :=
  board ([P,Q] ++ qp a) (qp b) (qp e) ([P] ++ qp d)

def WShape (H : Nat) (z : Board) : Prop :=
  ∃ a d, z = wBoard a d ∧ Bounded H z ∧ (0 < a → 0 < d)
def VShape (H : Nat) (z : Board) : Prop :=
  ∃ a b e d, z = vBoard a b e d ∧ Bounded H z

def firstException (x : Cell) : Prop := x = ⟨c1,3⟩
def rowThree : Line := .horizontal 3
def riseThree : Line := .rising 3

@[simp] theorem w_height_one (a d : Nat) : height (wBoard a d) c1 = 2*a+1 := by
  simp [height, wBoard, board] <;> omega
@[simp] theorem w_height_two (a d : Nat) : height (wBoard a d) c2 = 0 := rfl
@[simp] theorem w_height_three (a d : Nat) : height (wBoard a d) c3 = 0 := rfl
@[simp] theorem w_height_four (a d : Nat) : height (wBoard a d) c4 = 2*d := by
  simp [height, wBoard, board]
@[simp] theorem v_height_one (a b e d : Nat) : height (vBoard a b e d) c1 = 2*a+2 := by
  simp [height, vBoard, board] <;> omega
@[simp] theorem v_height_two (a b e d : Nat) : height (vBoard a b e d) c2 = 2*b := by
  simp [height, vBoard, board]
@[simp] theorem v_height_three (a b e d : Nat) : height (vBoard a b e d) c3 = 2*e := by
  simp [height, vBoard, board]
@[simp] theorem v_height_four (a b e d : Nat) : height (vBoard a b e d) c4 = 2*d+1 := by
  simp [height, vBoard, board] <;> omega

@[simp] theorem read_pqqp_Q (a r : Nat) :
    readRow (P :: Q :: qp a) r = some Q ↔
      r = 2 ∨ (3 ≤ r ∧ r ≤ 2*a+2 ∧ r%2 = 1) := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r =>
              change (qp a)[r]? = some Q ↔ _
              rw [qp_get_Q]
              omega

@[simp] theorem read_pqqp_P (a r : Nat) :
    readRow (P :: Q :: qp a) r = some P ↔
      r = 1 ∨ (3 ≤ r ∧ r ≤ 2*a+2 ∧ r%2 = 0) := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r =>
              change (qp a)[r]? = some P ↔ _
              rw [qp_get_P]
              omega

/-- The shape has no triple Q string, including the exceptional QQ at rows 2,3. -/
theorem v_noThree (a b e d : Nat) : NoThreeQ (vBoard a b e d) := by
  intro c r hs
  cases c <;>
    simp [stoneAt_readRow, vBoard, board, read_pqqp_Q, read_qp_Q,
      read_pqp_Q] at hs <;> omega

theorem w_noThree (a d : Nat) : NoThreeQ (wBoard a d) := by
  intro c r hs
  cases c <;>
    simp [stoneAt_readRow, wBoard, board] at hs <;> omega

/-- Adjacent middle columns have Q only on odd rows, while the right column
has Q only on even rows. This excludes every nonvertical Q four. -/
theorem no_nonvertical_of_Q_parities {H : Nat} {z : Board}
    (two : ∀ r, stoneAt z ⟨c2,r⟩ = some Q → r%2 = 1)
    (three : ∀ r, stoneAt z ⟨c3,r⟩ = some Q → r%2 = 1)
    (four : ∀ r, stoneAt z ⟨c4,r⟩ = some Q → r%2 = 0)
    {L : Line} (hn : L.Nonvertical) (hv : ValidLine H L) :
    ¬ (∀ x ∈ L.cells, stoneAt z x = some Q) := by
  intro hall
  cases L with
  | vertical c r => exact False.elim hn
  | horizontal r =>
      have h2 := two r (hall _ (by simp [Line.cells]))
      have h4 := four r (hall _ (by simp [Line.cells]))
      omega
  | rising r =>
      have h2 := two (r+1) (hall _ (by simp [Line.cells]))
      have h3 := three (r+2) (hall _ (by simp [Line.cells]))
      omega
  | falling r =>
      have pos := (hv ⟨c4,r-3⟩ (by simp [Line.cells])).1
      have h2 := two (r-1) (hall _ (by simp [Line.cells]))
      have h3 := three (r-2) (hall _ (by simp [Line.cells]))
      omega

theorem v_Q_parities (a b e d : Nat) :
    (∀ r, stoneAt (vBoard a b e d) ⟨c2,r⟩ = some Q → r%2 = 1) ∧
    (∀ r, stoneAt (vBoard a b e d) ⟨c3,r⟩ = some Q → r%2 = 1) ∧
    (∀ r, stoneAt (vBoard a b e d) ⟨c4,r⟩ = some Q → r%2 = 0) := by
  constructor
  · intro r h
    have := (read_qp_Q b r).mp (show readRow (qp b) r = some Q from h)
    exact this.2.2
  constructor
  · intro r h
    have := (read_qp_Q e r).mp (show readRow (qp e) r = some Q from h)
    exact this.2.2
  · intro r h
    have := (read_pqp_Q d r).mp (show readRow ([P] ++ qp d) r = some Q from h)
    exact this.2.2

theorem v_noQ (H a b e d : Nat) : ¬ Wins H (vBoard a b e d) Q := by
  have par := v_Q_parities a b e d
  apply noQ_of_noThree_and_nonvertical (v_noThree a b e d)
  intro L hn hv
  exact no_nonvertical_of_Q_parities par.1 par.2.1 par.2.2 hn hv

/-- Q's newly dropped middle stone is still odd, and its new c4 stone even. -/
theorem v_after_Q_parities (a b e d : Nat) (q : Col) :
    (∀ r, stoneAt (drop (vBoard a b e d) q Q) ⟨c2,r⟩ = some Q → r%2 = 1) ∧
    (∀ r, stoneAt (drop (vBoard a b e d) q Q) ⟨c3,r⟩ = some Q → r%2 = 1) ∧
    (∀ r, stoneAt (drop (vBoard a b e d) q Q) ⟨c4,r⟩ = some Q → r%2 = 0) := by
  have old := v_Q_parities a b e d
  constructor
  · intro r h
    rcases stoneAt_drop_cases q h with h | ⟨hc,hr,_⟩
    · exact old.1 r h
    · change c2 = q at hc
      subst q
      simp only [v_height_two] at hr
      try dsimp at hr
      omega
  constructor
  · intro r h
    rcases stoneAt_drop_cases q h with h | ⟨hc,hr,_⟩
    · exact old.2.1 r h
    · change c3 = q at hc
      subst q
      simp only [v_height_three] at hr
      try dsimp at hr
      omega
  · intro r h
    rcases stoneAt_drop_cases q h with h | ⟨hc,hr,_⟩
    · exact old.2.2 r h
    · change c4 = q at hc
      subst q
      simp only [v_height_four] at hr
      try dsimp at hr
      omega

/-- Strict first-win safety is established BEFORE selecting the P response. -/
theorem v_Q_move_safe {H a b e d : Nat} {q : Col}
    (hq : Legal H (vBoard a b e d) q) :
    ¬ Wins H (drop (vBoard a b e d) q Q) Q := by
  rintro ⟨L,hv,hall⟩
  have par := v_after_Q_parities a b e d q
  cases L with
  | vertical c r =>
      exact vertical_Q_after_move_impossible hq (v_noQ H a b e d)
        (noThree_topRun (v_noThree a b e d)) c r hv hall
  | horizontal r =>
      exact no_nonvertical_of_Q_parities par.1 par.2.1 par.2.2 (L := .horizontal r) trivial hv hall
  | rising r =>
      exact no_nonvertical_of_Q_parities par.1 par.2.1 par.2.2 (L := .rising r) trivial hv hall
  | falling r =>
      exact no_nonvertical_of_Q_parities par.1 par.2.1 par.2.2 (L := .falling r) trivial hv hall

theorem no_nonvertical_of_empty_column {z : Board} {c : Col}
    (he : z c = []) {L : Line} (hn : L.Nonvertical) :
    ¬ (∀ x ∈ L.cells, stoneAt z x = some Q) := by
  intro hall
  cases L with
  | vertical d r => exact False.elim hn
  | horizontal r =>
      have h := hall ⟨c,r⟩ (by cases c <;> simp [Line.cells])
      simp [stoneAt, he] at h
  | rising r =>
      cases c with
      | c1 =>
          have h := hall ⟨c1,r⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c2 =>
          have h := hall ⟨c2,r+1⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c3 =>
          have h := hall ⟨c3,r+2⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c4 =>
          have h := hall ⟨c4,r+3⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
  | falling r =>
      cases c with
      | c1 =>
          have h := hall ⟨c1,r⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c2 =>
          have h := hall ⟨c2,r-1⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c3 =>
          have h := hall ⟨c3,r-2⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h
      | c4 =>
          have h := hall ⟨c4,r-3⟩ (by simp [Line.cells])
          simp [stoneAt,he] at h

theorem w_noQ (H a d : Nat) : ¬ Wins H (wBoard a d) Q := by
  apply noQ_of_noThree_and_nonvertical (w_noThree a d)
  intro L hn hv
  exact no_nonvertical_of_empty_column (c := c2) rfl hn

theorem w_Q_move_safe {H a d : Nat} {q : Col} (hq : Legal H (wBoard a d) q) :
    ¬ Wins H (drop (wBoard a d) q Q) Q := by
  rintro ⟨L,hv,hall⟩
  have emptyMiddle : ∃ c, drop (wBoard a d) q Q c = [] := by
    cases q
    · exact ⟨c2,rfl⟩
    · exact ⟨c3,rfl⟩
    · exact ⟨c2,rfl⟩
    · exact ⟨c2,rfl⟩
  rcases emptyMiddle with ⟨c,empty⟩
  cases L with
  | vertical c r =>
      exact vertical_Q_after_move_impossible hq (w_noQ H a d)
        (noThree_topRun (w_noThree a d)) c r hv hall
  | horizontal r => exact no_nonvertical_of_empty_column empty (L := .horizontal r) trivial hall
  | rising r => exact no_nonvertical_of_empty_column empty (L := .rising r) trivial hall
  | falling r => exact no_nonvertical_of_empty_column empty (L := .falling r) trivial hall

/-- Both bottom corners belong to P throughout V. -/
theorem v_corners (a b e d : Nat) :
    stoneAt (vBoard a b e d) ⟨c1,1⟩ = some P ∧
    stoneAt (vBoard a b e d) ⟨c4,1⟩ = some P := by
  constructor <;> simp [stoneAt, vBoard, board]

theorem w_cover_one (a d : Nat) :
    afterRound (wBoard a d) c1 c1 = wBoard (a+1) d := by
  funext c; cases c <;> simp [afterRound, drop, wBoard, board, qp, List.append_assoc]
theorem w_cover_four (a d : Nat) :
    afterRound (wBoard a d) c4 c4 = wBoard a (d+1) := by
  funext c; cases c <;> simp [afterRound, drop, wBoard, board, qp, List.append_assoc]
theorem w_root_switch : afterRound (wBoard 0 0) c1 c4 = vBoard 0 0 0 0 := by
  funext c; cases c <;> rfl

theorem v_cover_one (a b e d : Nat) :
    afterRound (vBoard a b e d) c1 c1 = vBoard (a+1) b e d := by
  funext c; cases c <;> simp [afterRound, drop, vBoard, board, qp, List.append_assoc]
theorem v_cover_two (a b e d : Nat) :
    afterRound (vBoard a b e d) c2 c2 = vBoard a (b+1) e d := by
  funext c; cases c <;> simp [afterRound, drop, vBoard, board, qp, List.append_assoc]
theorem v_cover_three (a b e d : Nat) :
    afterRound (vBoard a b e d) c3 c3 = vBoard a b (e+1) d := by
  funext c; cases c <;> simp [afterRound, drop, vBoard, board, qp, List.append_assoc]
theorem v_cover_four (a b e d : Nat) :
    afterRound (vBoard a b e d) c4 c4 = vBoard a b e (d+1) := by
  funext c; cases c <;> simp [afterRound, drop, vBoard, board, qp, List.append_assoc]

/-- Every actual exception, including the potential one when a=0, is (c1,3). -/
theorem v_exception_complete (H a b e d : Nat) :
    ExceptionComplete H (vBoard a b e d) firstException := by
  intro x hx
  rcases x with ⟨c,r⟩
  rcases hx with ⟨hr,ht,hbelow⟩ | ⟨hpos,hlt,hr,ht⟩
  · cases c <;>
      simp [stoneAt_readRow, vBoard, board, read_pqqp_Q,
        read_qp_Q, read_pqp_Q] at ht hbelow
    all_goals simp [firstException] <;> (try dsimp only at *) <;> omega
  · cases c <;>
      simp only [v_height_one, v_height_two, v_height_three, v_height_four] at *
    all_goals
      simp [stoneAt_readRow, vBoard, board, read_pqqp_Q,
        read_qp_Q, read_pqp_Q] at ht
    all_goals simp [firstException] <;> (try dsimp only at *) <;> omega

theorem v_structural {H a b e d : Nat} (bound : Bounded H (vBoard a b e d)) :
    Structural H (vBoard a b e d) firstException :=
  ⟨bound, v_noQ H a b e d, noThree_topRun (v_noThree a b e d),
    v_exception_complete H a b e d⟩

theorem w_exception_complete (H a d : Nat) :
    ExceptionComplete H (wBoard a d) (fun _ => False) := by
  intro x hx
  rcases x with ⟨c,r⟩
  rcases hx with ⟨hr,ht,hbelow⟩ | ⟨hpos,hlt,hr,ht⟩
  · cases c <;>
      simp [stoneAt_readRow, wBoard, board] at ht hbelow <;> omega
  · cases c <;>
      simp only [w_height_one, w_height_two, w_height_three, w_height_four] at *
    all_goals
      simp [stoneAt_readRow, wBoard, board] at ht
    all_goals omega

theorem w_structural {H a d : Nat} (bound : Bounded H (wBoard a d)) :
    Structural H (wBoard a d) (fun _ => False) :=
  ⟨bound, w_noQ H a d, noThree_topRun (w_noThree a d), w_exception_complete H a d⟩

/-- Exact five-line superset used by the V exits. -/
theorem firstException_check_lines {H : Nat} {L : Line}
    (h : ToCheck H firstException L) :
    L = .horizontal 1 ∨ L = rise ∨ L = down ∨ L = rowThree ∨ L = riseThree := by
  rcases h with ⟨hv,hn,x,hx,hbottom | hex⟩
  · rcases bottom_line_cases hv hn ⟨x,hx,hbottom⟩ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · have he : x = ⟨c1,3⟩ := hex
    subst x
    cases L with
    | vertical c r => exact False.elim hn
    | horizontal r =>
        have hr : r = 3 := by
          have rev : 3 = r := by simpa [Line.cells, Cell.mk.injEq] using hx
          exact rev.symm
        subst r
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | rising r =>
        have hr : r = 3 := by
          have rev : 3 = r := by simpa [Line.cells, Cell.mk.injEq] using hx
          exact rev.symm
        subst r
        exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    | falling r =>
        have hr : r = 3 := by
          have rev : 3 = r := by simpa [Line.cells, Cell.mk.injEq] using hx
          exact rev.symm
        subst r
        have bad : 1 ≤ 0 := (hv ⟨c4,0⟩ (by simp [Line.cells])).1
        omega

/-- On an even board, Q can fill only c4 in V. -/
theorem v_only_four_can_fill {H a b e d : Nat} (even : H%2 = 0) {q : Col}
    (full : height (drop (vBoard a b e d) q Q) q = H) : q = c4 := by
  rw [height_drop_same] at full
  cases q <;> simp only [v_height_one, v_height_two, v_height_three, v_height_four] at full
  all_goals first | rfl | omega

/-- Q cannot fill c4 in W on an even-height board. -/
theorem w_four_cover_legal {H a d : Nat} (even : H%2 = 0)
    (hq : Legal H (wBoard a d) c4) : Legal H (drop (wBoard a d) c4 Q) c4 := by
  unfold Legal at *
  simp only [w_height_four, height_drop_same] at *
  omega

/-- Same-column replies preserve V without any hidden phase variable. -/
theorem v_cover_shape {H : Nat} {z : Board} (shape : VShape H z)
    {q : Col} (hq : Legal H z q) (hp : Legal H (drop z q Q) q) :
    VShape H (afterRound z q q) := by
  rcases shape with ⟨a,b,e,d,rfl,bound⟩
  have finalBound := drop_bounded (drop_bounded bound hq Q) hp P
  cases q
  · exact ⟨a+1,b,e,d,v_cover_one a b e d,finalBound⟩
  · exact ⟨a,b+1,e,d,v_cover_two a b e d,finalBound⟩
  · exact ⟨a,b,e+1,d,v_cover_three a b e d,finalBound⟩
  · exact ⟨a,b,e,d+1,v_cover_four a b e d,finalBound⟩

#print axioms w_Q_move_safe
#print axioms v_Q_move_safe
#print axioms v_exception_complete
#print axioms v_cover_shape
end UniformFour.U2
