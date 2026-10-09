import experiments.FourColumns
import Mathlib.Tactic.FinCases

namespace Connect4.FourColumns

/-- Above the first three rows, every opposing stone has a defender below. -/
def HighSupported (p : Player) (b : Board 4) : Prop :=
  ∀ c i, 3 ≤ i → stone (b c) i = some (opponent p) →
    stone (b c) (i - 1) = some p

theorem cellAtInt_of_stone' {h : Nat} {b : Board 4} {p : Player}
    {x y : Int} {c : Fin 4} (hx : x = (c : Int))
    (hy : 0 ≤ y) (hyh : y < h) (hs : stone (b c) y.toNat = some p) :
    cellAtInt h b x y = some p := by
  subst x
  simpa [cellAtInt, hy, hyh] using hs

theorem four_dir_low_or_down {h : Nat} {b : Board 4} {p : Player}
    {x y dx dy : Int} (hs : HighSupported p b)
    (hdy : dy = -1 ∨ dy = 0 ∨ dy = 1)
    (hf : HasFourDir h b (opponent p) x y dx dy) :
    HasFourDir 6 b (opponent p) x y dx dy ∨
      HasFourDir h b p x (y - 1) dx dy := by
  classical
  by_cases hlo : ∀ i : Fin 4, y + (i : Int) * dy < 6
  · left
    intro i
    obtain ⟨c, hx, hy, _, ht⟩ := cellAtInt_some (hf i)
    exact cellAtInt_of_stone' hx hy (hlo i) ht
  · right
    push_neg at hlo
    obtain ⟨j, hj⟩ := hlo
    intro i
    obtain ⟨c, hx, hy, hyh, ht⟩ := cellAtInt_some (hf i)
    have hlow : 3 ≤ y + (i : Int) * dy := by
      have hi := i.isLt
      have hj' := j.isLt
      rcases hdy with rfl | rfl | rfl <;> simp only [Int.mul_neg_one, Int.mul_zero,
        Int.mul_one] at * <;> omega
    have hrow : (y - 1 + (i : Int) * dy).toNat =
        (y + (i : Int) * dy).toNat - 1 := by omega
    apply cellAtInt_of_stone' hx (by omega) (by omega)
    rw [hrow]
    exact hs c _ (by omega) ht

/-- A first opposing win cannot occur above the six-row scoring region. -/
theorem high_supported_no_four {h : Nat} {b : Board 4} {p : Player}
    (hs : HighSupported p b) (hl : ¬ HasFour 6 b (opponent p))
    (hp : ¬ HasFour h b p) : ¬ HasFour h b (opponent p) := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · rcases four_dir_low_or_down hs (Or.inr (Or.inr rfl)) hd with h | h
    · exact hl (Or.inl ⟨x, y, h⟩)
    · exact hp (Or.inl ⟨x, y-1, h⟩)
  · rcases four_dir_low_or_down hs (Or.inr (Or.inl rfl)) hd with h | h
    · exact hl (Or.inr (Or.inl ⟨x, y, h⟩))
    · exact hp (Or.inr (Or.inl ⟨x, y-1, h⟩))
  · rcases four_dir_low_or_down hs (Or.inr (Or.inr rfl)) hd with h | h
    · exact hl (Or.inr (Or.inr (Or.inl ⟨x, y, h⟩)))
    · exact hp (Or.inr (Or.inr (Or.inl ⟨x, y-1, h⟩)))
  · rcases four_dir_low_or_down hs (Or.inl rfl) hd with h | h
    · exact hl (Or.inr (Or.inr (Or.inr ⟨x, y, h⟩)))
    · exact hp (Or.inr (Or.inr (Or.inr ⟨x, y-1, h⟩)))

/-- A nonfull high column is capped at the start of the opponent's turn. -/
def HighTop (h : Nat) (p : Player) (b : Board 4) : Prop :=
  ∀ c, Legal h b c → 3 ≤ (b c).length →
    stone (b c) ((b c).length - 1) = some p

theorem supported_defender {b : Board 4} {p : Player} (hs : HighSupported p b)
    (c : Fin 4) : HighSupported p (play b c p) := by
  intro d i hi ht
  have hold : stone (b d) i = some (opponent p) := by
    by_cases hd : d = c
    · subst d
      rw [play_eq] at ht
      exact stone_append_other (player_ne_opponent p) ht
    · simpa only [play_ne b c d p hd] using ht
  have hb := hs d i hi hold
  rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hb)]
  exact hb

theorem supported_opponent {h : Nat} {b : Board 4} {p : Player}
    (hs : HighSupported p b) (ht : HighTop h p b) {c : Fin 4}
    (hc : Legal h b c) : HighSupported p (play b c (opponent p)) := by
  intro d i hi hw
  by_cases hd : d = c
  · subst d
    rw [play_eq, stone_append] at hw
    split at hw
    · have hb := hs c i hi hw
      rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hb)]
      exact hb
    · split at hw
      · rename_i he
        subst i
        rw [stone_old_play _ _ _ _ _ (by omega)]
        exact ht c hc hi
      · cases hw
  · rw [play_ne b c d _ hd] at hw ⊢
    exact hs d i hi hw

theorem four_map_cells {h k : Nat} {a b : Board 4} {p : Player}
    (hm : ∀ x y, cellAtInt h a x y = some p → cellAtInt k b x y = some p)
    (hf : HasFour h a p) : HasFour k b p := by
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · exact Or.inl ⟨x, y, fun i => hm _ _ (hd i)⟩
  · exact Or.inr (Or.inl ⟨x, y, fun i => hm _ _ (hd i)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, fun i => hm _ _ (hd i)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, fun i => hm _ _ (hd i)⟩))

theorem four_height_mono {h k : Nat} {b : Board 4} {p : Player}
    (hk : h ≤ k) : HasFour h b p → HasFour k b p := by
  apply four_map_cells
  intro x y ht
  obtain ⟨c, hx, hy, hyh, hs⟩ := cellAtInt_some ht
  exact cellAtInt_of_stone' hx hy (by omega) hs

def LowEq (a b : Board 4) : Prop :=
  ∀ c i, i < 6 → stone (a c) i = stone (b c) i

theorem lowEq_symm {a b : Board 4} (he : LowEq a b) : LowEq b a :=
  fun c i hi => (he c i hi).symm

theorem lowEq_four {a b : Board 4} {p : Player} (he : LowEq a b) :
    HasFour 6 a p → HasFour 6 b p := by
  apply four_map_cells
  intro x y ht
  obtain ⟨c, hx, hy, hyh, hs⟩ := cellAtInt_some ht
  apply cellAtInt_of_stone' hx hy hyh
  rw [← he c _ (by omega)]
  exact hs

theorem lowEq_high_play {a : Board 4} {c : Fin 4} {p : Player}
    (hc : 6 ≤ (a c).length) : LowEq (play a c p) a := by
  intro d i hi
  by_cases hd : d = c
  · subst d
    rw [stone_old_play _ _ _ _ _ (by omega)]
  · rw [play_ne a c d p hd]

theorem lowEq_play {a b : Board 4} {c : Fin 4} {p : Player}
    (he : LowEq a b) (hlen : (a c).length = (b c).length ∨
      (6 ≤ (a c).length ∧ 6 ≤ (b c).length)) :
    LowEq (play a c p) (play b c p) := by
  intro d i hi
  by_cases hd : d = c
  · subst d
    rw [play_eq, play_eq, stone_append, stone_append]
    rcases hlen with hl | ⟨ha, hb⟩
    · rw [hl, he c i hi]
    · rw [if_pos (by omega), if_pos (by omega), he c i hi]
  · simpa only [play_ne a c d p hd, play_ne b c d p hd] using he d i hi

theorem top_append_player (l : List Player) (p : Player) :
    stone (l ++ [p]) ((l ++ [p]).length - 1) = some p := by
  simp [stone_append]

theorem high_top_reply {h : Nat} {b : Board 4} {p : Player} {c d : Fin 4}
    (ht : HighTop h p b) (hc : Legal h b c)
    (hd : Legal h (play b c (opponent p)) d)
    (hcap : d = c ∨ (play b c (opponent p) c).length ≤ 2 ∨
      ¬ Legal h (play b c (opponent p)) c) :
    HighTop h p (play (play b c (opponent p)) d p) := by
  intro e he hei
  by_cases hed : e = d
  · subst e
    rw [play_eq]
    exact top_append_player _ _
  · unfold Legal at he
    rw [play_ne _ d e p hed] at he hei ⊢
    by_cases hec : e = c
    · subst e
      rcases hcap with rfl | hsmall | hfull
      · exact False.elim (hed rfl)
      · omega
      · exact False.elim (hfull he)
    · rw [play_ne b c e _ hec] at hei ⊢
      apply ht e
      · simpa only [Legal, play_ne b c e _ hec] using he
      · exact hei

#print axioms high_supported_no_four

end Connect4.FourColumns
