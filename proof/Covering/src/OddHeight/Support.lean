import OddHeight.MoveFacts
import OddHeight.Core

/-! Geometric support lowering. Reviewed local copy; see the validation records. -/
namespace OddHeight
open Player Col

private theorem get_some_lt_length {α : Type} (xs : List α) (n : Nat) (p : α)
    (h : xs[n]? = some p) : n < xs.length := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          have ht := ih n (by simpa using h)
          simpa using Nat.succ_lt_succ ht

private theorem get_append_single_cases {α : Type} (xs : List α)
    (n : Nat) (p s : α) (h : (xs ++ [s])[n]? = some p) :
    xs[n]? = some p ∨ (n = xs.length ∧ p = s) := by
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero =>
          right
          constructor
          · rfl
          · simpa using h.symm
      | succ n => simp at h
  | cons a xs ih =>
      cases n with
      | zero => exact Or.inl (by simpa using h)
      | succ n =>
          rcases ih n (by simpa using h) with ho | ⟨hl, he⟩
          · exact Or.inl (by simpa using ho)
          · exact Or.inr ⟨by simp [hl], he⟩

theorem stoneAt_row_le {b : Board} {x : Cell} {p : Player}
    (h : stoneAt b x = some p) : 1 ≤ x.row ∧ x.row ≤ height b x.col := by
  have hz : x.row ≠ 0 := by intro hz; simp [stoneAt, hz] at h
  simp only [stoneAt, if_neg hz] at h
  have hi := get_some_lt_length (b x.col) (x.row - 1) p h
  unfold height
  omega

/-- Every observed stone after a move was present before, or is the one new stone. -/
theorem stoneAt_drop_cases {b : Board} {x : Cell} {p s : Player} (c : Col)
    (h : stoneAt (drop b c s) x = some p) :
    stoneAt b x = some p ∨ (x.col = c ∧ x.row = height b c + 1 ∧ p = s) := by
  have hz : x.row ≠ 0 := by intro hz; simp [stoneAt, hz] at h
  by_cases hc : x.col = c
  · have hh : (b x.col ++ [s])[x.row - 1]? = some p := by
      simpa [stoneAt, hz, drop, hc] using h
    rcases get_append_single_cases (b x.col) (x.row - 1) p s hh with ho | ⟨hl, he⟩
    · exact Or.inl (by simpa [stoneAt, hz] using ho)
    · right
      refine ⟨hc, ?_, he⟩
      have hh : x.row - 1 = height b c := by simpa [height, hc] using hl
      omega
  · exact Or.inl (by simpa [stoneAt, drop, hc] using h)

theorem stoneAt_drop_old_of_le {b : Board} {x : Cell} {p s : Player} (c : Col)
    (hr : x.row ≤ height b x.col)
    (h : stoneAt (drop b c s) x = some p) : stoneAt b x = some p := by
  rcases stoneAt_drop_cases c h with ho | ⟨hc, hn, _⟩
  · exact ho
  · rw [hc] at hr
    omega

/-- A new vertical four would require a pre-existing nonfull three-Q top run. -/
theorem vertical_Q_after_move_impossible {H : Nat} {b : Board} {q : Col}
    (hq : Legal H b q) (hnoQ : ¬ Wins H b Q) (htop : TopRunAtMostTwo H b)
    (c : Col) (r : Nat) (hv : ValidLine H (.vertical c r)) :
    ¬ (∀ x ∈ (Line.vertical c r).cells, stoneAt (drop b q Q) x = some Q) := by
  intro hall
  have h0 := hall ⟨c,r⟩ (by simp [Line.cells])
  have h1 := hall ⟨c,r+1⟩ (by simp [Line.cells])
  have h2 := hall ⟨c,r+2⟩ (by simp [Line.cells])
  have h3 := hall ⟨c,r+3⟩ (by simp [Line.cells])
  have hr : 1 ≤ r := (hv ⟨c,r⟩ (by simp [Line.cells])).1
  rcases stoneAt_drop_cases q h3 with ho | ⟨hc, hn, _⟩
  · have hb : r+3 ≤ height b c := (stoneAt_row_le ho).2
    apply hnoQ
    refine ⟨.vertical c r, hv, ?_⟩
    intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact stoneAt_drop_old_of_le q (by change r ≤ height b c; omega) h0
    · exact stoneAt_drop_old_of_le q (by change r+1 ≤ height b c; omega) h1
    · exact stoneAt_drop_old_of_le q (by change r+2 ≤ height b c; omega) h2
    · exact ho
  · change c = q at hc
    change r + 3 = height b q + 1 at hn
    subst c
    have hh : height b q = r + 2 := by omega
    have old0 := stoneAt_drop_old_of_le q (by change r ≤ height b q; omega) h0
    have old1 := stoneAt_drop_old_of_le q (by change r+1 ≤ height b q; omega) h1
    have old2 := stoneAt_drop_old_of_le q (by change r+2 ≤ height b q; omega) h2
    apply htop q hq (by omega)
    have he1 : height b q - 1 = r + 1 := by omega
    have he2 : height b q - 2 = r := by omega
    exact ⟨by simpa only [hh] using old2,
      by simpa only [he1] using old1, by simpa only [he2] using old0⟩

/-- Existing exceptions after Q were either existing or potential before Q. -/
theorem existing_exception_after_Q {H : Nat} {b : Board} {q : Col}
    (hq : Legal H b q) {x : Cell} (hx : existingException (drop b q Q) x) :
    exceptionSet H b x := by
  rcases hx with ⟨hr, ht, hb⟩
  rcases stoneAt_drop_cases q ht with ho | ⟨hc, hrow, _⟩
  · rcases stoneAt_drop_cases q hb with hlo | ⟨hc, hrow, _⟩
    · exact Or.inl ⟨hr, ho, hlo⟩
    · have hbound := (stoneAt_row_le ho).2
      change x.col = q at hc
      change x.row - 1 = height b q + 1 at hrow
      rw [hc] at hbound
      omega
  · rcases stoneAt_drop_cases q hb with hlo | ⟨_, hbad, _⟩
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hc]; omega
      · simpa [Legal, hc] using hq
      · simpa [hc] using hrow
      · have he : x.row - 1 = height b x.col := by rw [hc]; omega
        simpa [he] using hlo
    · change x.row - 1 = height b q + 1 at hbad
      omega

/-- Only the existing-exception part is needed at the Q half-turn. -/
theorem existing_exception_after_Q_in_E {H : Nat} {b : Board} {E : Cell → Prop}
    (complete : ExceptionComplete H b E) {q : Col} (hq : Legal H b q) :
    ∀ x, existingException (drop b q Q) x → E x := by
  intro x hx
  exact complete x (existing_exception_after_Q hq hx)

def lowerCell (x : Cell) : Cell := ⟨x.col, x.row - 1⟩

def lowerLine : Line → Line
  | .horizontal r => .horizontal (r - 1)
  | .vertical c r => .vertical c (r - 1)
  | .rising r => .rising (r - 1)
  | .falling r => .falling (r - 1)

/-- The positivity premise prevents truncated subtraction at the bottom edge. -/
theorem lowerLine_cells {L : Line} (hn : L.Nonvertical)
    (hr : ∀ x ∈ L.cells, 2 ≤ x.row) :
    (lowerLine L).cells = L.cells.map lowerCell := by
  cases L with
  | horizontal r => rfl
  | vertical c r => exact False.elim hn
  | rising r =>
      have h : 2 ≤ r := hr ⟨c1,r⟩ (by simp [Line.cells])
      have h1 : r - 1 + 1 = r + 1 - 1 := by omega
      have h2 : r - 1 + 2 = r + 2 - 1 := by omega
      have h3 : r - 1 + 3 = r + 3 - 1 := by omega
      simp [lowerLine, Line.cells, lowerCell, h1, h2, h3]
  | falling r =>
      have h1 : r - 1 - 1 = r - 1 - 1 := rfl
      have h2 : r - 1 - 2 = r - 2 - 1 := by omega
      have h3 : r - 1 - 3 = r - 3 - 1 := by omega
      simp [lowerLine, Line.cells, lowerCell, h2, h3]

/-- L3, spatial part: supports of a nonbottom nonvertical line form a valid P four. -/
theorem supported_line_gives_P_win {H : Nat} {b : Board} {L : Line}
    (hv : ValidLine H L) (hn : L.Nonvertical)
    (hr : ∀ x ∈ L.cells, 2 ≤ x.row)
    (hp : ∀ x ∈ L.cells, stoneAt b (lowerCell x) = some P) : Wins H b P := by
  refine ⟨lowerLine L, ?_, ?_⟩
  · intro y hy
    rw [lowerLine_cells hn hr] at hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxv := hv x hx
    unfold InBoard at hxv
    have hxr := hr x hx
    simp only [InBoard, lowerCell]
    omega
  · intro y hy
    rw [lowerLine_cells hn hr] at hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hp x hx

/-- L3, temporal part: all four P supports existed BEFORE the Q move.
    No legal-move or alternating-history premise is needed for this implication. -/
theorem supported_Q_move_implies_previous_P_win
    {H : Nat} {b : Board} {L : Line} (q : Col)
    (hv : ValidLine H L) (hn : L.Nonvertical)
    (hr : ∀ x ∈ L.cells, 2 ≤ x.row)
    (hp : ∀ x ∈ L.cells, stoneAt (drop b q Q) (lowerCell x) = some P) :
    Wins H b P := by
  apply supported_line_gives_P_win hv hn hr
  intro x hx
  exact stoneAt_drop_other_colour (by decide : P ≠ Q) q (hp x hx)

private theorem predecessor_exists {α : Type} (xs : List α) (n : Nat) (v : α)
    (h : xs[n + 1]? = some v) : ∃ w, xs[n]? = some w := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a xs ih =>
      cases n with
      | zero => exact ⟨a, rfl⟩
      | succ n => exact ih n (by simpa using h)

/-- Gravity: every occupied nonbottom cell has an occupied cell below it. -/
theorem stone_below_exists {b : Board} {x : Cell} {p : Player}
    (hr : 2 ≤ x.row) (hs : stoneAt b x = some p) :
    ∃ s, stoneAt b (lowerCell x) = some s := by
  have hz : x.row ≠ 0 := by omega
  have hz' : x.row - 1 ≠ 0 := by omega
  have he : x.row - 1 = (x.row - 2) + 1 := by omega
  have he' : x.row - 1 - 1 = x.row - 2 := by omega
  simp only [stoneAt, if_neg hz, he] at hs
  rcases predecessor_exists (b x.col) (x.row - 2) p hs with ⟨s, hs⟩
  exact ⟨s, by simpa [stoneAt, lowerCell, hz', he'] using hs⟩

/-- Away from existing exceptions every nonbottom Q has a P support. -/
theorem Q_supported_of_not_exception {b : Board} {x : Cell}
    (hr : 2 ≤ x.row) (hq : stoneAt b x = some Q)
    (hn : ¬ existingException b x) : stoneAt b (lowerCell x) = some P := by
  rcases stone_below_exists hr hq with ⟨p, hp⟩
  cases p with
  | P => exact hp
  | Q => exact False.elim (hn ⟨hr, hq, hp⟩)

/-- Generic nonvertical safety after Q, once completeness of the exception set
    at that intermediate board has been established. This does not assume safety. -/
theorem blocked_exceptions_exclude_nonvertical_Q_after_move
    {H : Nat} {b : Board} {E : Cell → Prop} (q : Col)
    (hnoP : ¬ Wins H b P)
    (complete : ∀ x, existingException (drop b q Q) x → E x)
    (blocked : ∀ L, ToCheck H E L → HasP b L)
    {L : Line} (hv : ValidLine H L) (hn : L.Nonvertical) :
    ¬ (∀ x ∈ L.cells, stoneAt (drop b q Q) x = some Q) := by
  intro hall
  by_cases hc : ∃ x ∈ L.cells, x.row = 1 ∨ E x
  · exact blocked_line_not_allQ
      (hasP_drop_preserves (blocked L ⟨hv, hn, hc⟩) q Q) hall
  · have hr : ∀ x ∈ L.cells, 2 ≤ x.row := by
      intro x hx
      have hp := (hv x hx).1
      have hne : x.row ≠ 1 := fun he => hc ⟨x, hx, Or.inl he⟩
      omega
    apply hnoP
    apply supported_Q_move_implies_previous_P_win q hv hn hr
    intro x hx
    apply Q_supported_of_not_exception (hr x hx) (hall x hx)
    intro he
    exact hc ⟨x, hx, Or.inr (complete x he)⟩

#print axioms supported_Q_move_implies_previous_P_win
end OddHeight
