import OddHeight.Core

/-! Geometric support lowering. Reviewed local copy; see the validation records. -/
namespace OddHeight
open Player Col

private theorem get_append_preserves {α : Type} (xs : List α) (ys : List α)
    (n : Nat) (v : α) (h : xs[n]? = some v) :
    (xs ++ ys)[n]? = some v := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a xs ih =>
      cases n with
      | zero => simpa using h
      | succ n => exact ih n (by simpa using h)

private theorem get_append_single_other {α : Type} (xs : List α)
    (n : Nat) (v w : α) (hne : v ≠ w)
    (h : (xs ++ [w])[n]? = some v) : xs[n]? = some v := by
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero => simp only [List.nil_append, List.getElem?_cons_zero,
          Option.some.injEq] at h; exact False.elim (hne h.symm)
      | succ n => simp at h
  | cons a xs ih =>
      cases n with
      | zero => simpa using h
      | succ n => exact ih n (by simpa using h)

/-- An occupied cell survives every append-only move. -/
theorem stoneAt_drop_preserves {b : Board} {x : Cell} {p : Player}
    (h : stoneAt b x = some p) (c : Col) (s : Player) :
    stoneAt (drop b c s) x = some p := by
  have hr : x.row ≠ 0 := by intro hz; simp [stoneAt, hz] at h
  simp only [stoneAt, if_neg hr] at h ⊢
  by_cases hc : x.col = c
  · simp only [drop, if_pos hc]
    exact get_append_preserves _ _ _ _ h
  · simpa [drop, hc] using h

/-- A move of the other colour cannot create a stone of this colour. -/
theorem stoneAt_drop_other_colour {b : Board} {x : Cell} {p s : Player}
    (hne : p ≠ s) (c : Col)
    (h : stoneAt (drop b c s) x = some p) : stoneAt b x = some p := by
  have hr : x.row ≠ 0 := by intro hz; simp [stoneAt, hz] at h
  simp only [stoneAt, if_neg hr] at h ⊢
  by_cases hc : x.col = c
  · simp only [drop, if_pos hc] at h
    exact get_append_single_other _ _ _ _ hne h
  · simpa [drop, hc] using h

theorem hasP_drop_preserves {b : Board} {L : Line}
    (h : HasP b L) (c : Col) (s : Player) : HasP (drop b c s) L := by
  rcases h with ⟨x, hx, hp⟩
  exact ⟨x, hx, stoneAt_drop_preserves hp c s⟩

theorem wins_drop_preserves {H : Nat} {b : Board} {p : Player}
    (h : Wins H b p) (c : Col) (s : Player) : Wins H (drop b c s) p := by
  rcases h with ⟨L, hv, hs⟩
  exact ⟨L, hv, fun x hx => stoneAt_drop_preserves (hs x hx) c s⟩

theorem wins_drop_other_colour {H : Nat} {b : Board} {p s : Player}
    (hne : p ≠ s) (c : Col) (h : Wins H (drop b c s) p) : Wins H b p := by
  rcases h with ⟨L, hv, hs⟩
  exact ⟨L, hv, fun x hx => stoneAt_drop_other_colour hne c (hs x hx)⟩


end OddHeight
