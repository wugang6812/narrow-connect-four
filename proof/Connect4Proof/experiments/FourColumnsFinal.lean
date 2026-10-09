import experiments.FourColumnsRightFamilies

namespace Connect4.FourColumns

structure Start3 (h : Nat) (b : Board 4) : Prop where
  core : Core13 h b
  b0 : b 0 = [.black, .black]
  b1 : b 1 = []
  b2 : b 2 = []
  odd3 : (b 3).length % 2 = 1
  nw34 : stone (b 3) 4 ≠ some .white

theorem start3_safe {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hp : Start3 h b) : CanAvoidLoss h .black b := by
  have step : ∀ k b, Start3 h b → SafeFor h .black k b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro b hp
      cases k with
      | zero => exact hp.core.hnw
      | succ k =>
        refine ⟨hp.core.hnw, ?_⟩
        by_cases hb : HasFour h b .black
        · exact Or.inl hb
        · right; right
          rw [if_neg (by rw [hp.core.htm]; decide), hp.core.htm]
          intro c hc
          have hw := core13_white hp.core hc hb
            ⟨1, empty_target_after_white c 1 2 (by rw [hp.b1]; decide)⟩
            ⟨2, empty_target_after_white c 2 2 (by rw [hp.b2]; decide)⟩
          have hn34 := not_white_append_miss (c := c) hp.nw34 (by have := hp.odd3; omega)
          fin_cases c
          · change OpenCore13 h (play b 0 .white) 0 at hw
            have he : Legal h (play b 0 .white) 0 := by simp [Legal, play, hp.b0]; omega
            have hx : XState h (play (play b 0 .white) 0 .black) := by
              refine ⟨core13_black hw he (Or.inl rfl), ⟨0, Or.inl ?_⟩, ?_, ?_, ?_, not_white_black hn34⟩
              · simp [play, hp.b0, stone]
              · intro d
                fin_cases d <;> simp [play, hp.b0, hp.b1, hp.b2, xParity]
                exact hp.odd3
              · simp [play, hp.b1, stone]
              · simp [play, hp.b2, stone]
            exact black_step_safe hw.htm hw.hnw he (x_state_safe hh hx) k
          · change OpenCore13 h (play b 1 .white) 1 at hw
            have ht : Top13 (play b 1 .white) 1 := by
              right; exact ⟨Or.inl rfl, by simp [play, hp.b1]⟩
            have he : Legal h (play b 1 .white) 2 := by simp [Legal, play, hp.b2]; omega
            have hy : YState h (play (play b 1 .white) 2 .black) := by
              refine ⟨core13_black (core13_retarget hw ht 2) he (Or.inl rfl), ?_, ?_, ?_, ?_, ?_⟩
              · simp [play, hp.b1]
              · simp [play, hp.b2]
              · simp [play, hp.b0]
              · simpa [play] using hp.odd3
              · simp [play, hp.b0, stone]
            exact black_step_safe hw.htm hw.hnw he (y_state_safe hh h4 hy) k
          · change OpenCore13 h (play b 2 .white) 2 at hw
            have he : Legal h (play b 2 .white) 2 := by simp [Legal, play, hp.b2]; omega
            have hx : XState h (play (play b 2 .white) 2 .black) := by
              refine ⟨core13_black hw he (Or.inl rfl), ⟨2, Or.inl ?_⟩, ?_, ?_, ?_, not_white_black hn34⟩
              · simp [play, hp.b2, stone]
              · intro d
                fin_cases d <;> simp [play, hp.b0, hp.b1, hp.b2, xParity]
                exact hp.odd3
              · simp [play, hp.b1, stone]
              · simp [play, hp.b2, stone]
            exact black_step_safe hw.htm hw.hnw he (x_state_safe hh hx) k
          · change OpenCore13 h (play b 3 .white) 3 at hw
            change SafeFor h .black k (play b 3 .white)
            by_cases hcov : Legal h (play b 3 .white) 3
            · cases k with
              | zero => exact hw.hnw
              | succ k =>
                refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
                rw [if_pos hw.htm, hw.htm]
                refine ⟨3, hcov, ih k (by omega) _ ?_⟩
                refine ⟨core13_black hw hcov (Or.inl rfl), ?_, ?_, ?_, ?_, not_white_black hn34⟩
                · simpa [play] using hp.b0
                · simpa [play] using hp.b1
                · simpa [play] using hp.b2
                · simp only [play_eq, List.length_append, List.length_singleton]
                  have := hp.odd3; omega
            · exact full_right_empty_safe hh h4 hw hcov
                (by simpa [play] using hp.b0) (by simpa [play] using hp.b1)
                (by simpa [play] using hp.b2) k
  exact fun k => step k b hp

def opening13 (r : Fin 4) : Board 4 :=
  play (play (play (emptyBoard 4) 0 .black) r .white) 0 .black

theorem opening13_core {h : Nat} (h2 : 2 ≤ h) (r : Fin 4) (hr : r = 1 ∨ r = 3) :
    Core13 h (opening13 r) := by
  have ht : totalStones (opening13 r) = 3 := by simp [opening13, totalStones_play', totalStones_empty]
  have hnone : ¬ HasFour h (opening13 r) .white := by
    intro hf; have := hasFour_minStones hf; rw [ht] at this; omega
  rcases hr with hr | hr <;> subst r
  all_goals
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, hnone⟩
    · intro d
      fin_cases d <;> simp [opening13, play, emptyBoard] <;> omega
    · simp [toMove, ht]
    · intro d i hs hi
      have hl := stone_bound _ _ _ hs
      fin_cases d <;> simp [opening13, play, emptyBoard] at hl
      · have he : i = 1 := by omega
        subst i; simp [opening13, play, emptyBoard, stone] at hs
      all_goals omega
    · intro d _
      fin_cases d <;> simp [Top13, TopBlack, opening13, play, emptyBoard, stone]

theorem opening3_safe {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .black (opening13 3) := by
  have hc := opening13_core h2 3 (Or.inr rfl)
  by_cases h4 : 4 ≤ h
  · apply start3_safe hh h4
    exact ⟨hc, rfl, rfl, rfl, by decide, by decide⟩
  · have he : h = 2 := by omega
    exact permanent13_safe hc ⟨0, Or.inr (by omega)⟩ ⟨0, Or.inr (by omega)⟩

theorem opening1_safe {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .black (opening13 1) := by
  by_cases h4 : 4 ≤ h
  · exact pd1_state_safe hh h4 (black_second_w1 h2)
  · have he : h = 2 := by omega
    exact permanent13_safe (opening13_core h2 1 (Or.inl rfl))
      ⟨0, Or.inr (by omega)⟩ ⟨0, Or.inr (by omega)⟩

theorem few_stones_safe_zero {h : Nat} {b : Board 4} (hn : totalStones b < 4) :
    SafeFor h .black 0 b := by
  intro hf; have := hasFour_minStones hf; omega

/-- Paper Theorem 5.8: all four replies after Black's edge opening are covered. -/
theorem black_nonloss_four_columns {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .black (emptyBoard 4) := by
  have empty_nw : ¬ HasFour h (emptyBoard 4) .white :=
    few_stones_safe_zero (by rw [totalStones_empty]; decide)
  have one_nw : ¬ HasFour h (play (emptyBoard 4) 0 .black) .white :=
    few_stones_safe_zero (by rw [totalStones_play', totalStones_empty]; decide)
  have first : Legal h (emptyBoard 4) 0 := by simp [Legal, emptyBoard]; omega
  intro k
  cases k with
  | zero => exact empty_nw
  | succ k =>
    refine ⟨empty_nw, Or.inr (Or.inr ?_)⟩
    rw [if_pos (toMove_empty 4), toMove_empty]
    refine ⟨0, first, ?_⟩
    cases k with
    | zero => exact one_nw
    | succ k =>
      refine ⟨one_nw, Or.inr (Or.inr ?_)⟩
      have ht : toMove (play (emptyBoard 4) 0 .black) = .white := by rw [toMove_play', toMove_empty]; rfl
      rw [if_neg (by rw [ht]; decide), ht]
      intro c _
      have htwo : ¬ HasFour h (play (play (emptyBoard 4) 0 .black) c .white) .white :=
        few_stones_safe_zero (by rw [totalStones_play', totalStones_play', totalStones_empty]; decide)
      have ht2 : toMove (play (play (emptyBoard 4) 0 .black) c .white) = .black := by
        rw [toMove_play', ht]; rfl
      have response : CanAvoidLoss h .black (play (play (emptyBoard 4) 0 .black) c .white) := by
        fin_cases c
        · apply black_step_safe ht2 htwo (e := 3)
          · simp [Legal, play, emptyBoard]; omega
          · exact opening0_safe h2 hh
        · apply black_step_safe ht2 htwo (e := 0)
          · simp [Legal, play, emptyBoard]; omega
          · exact opening1_safe h2 hh
        · apply black_step_safe ht2 htwo (e := 2)
          · simp [Legal, play, emptyBoard]; omega
          · exact pd_state_safe (black_second_w2 h2)
        · apply black_step_safe ht2 htwo (e := 0)
          · simp [Legal, play, emptyBoard]; omega
          · exact opening3_safe h2 hh
      exact response k

/-- Paper Corollary 5.9, with the board height literally equal to 2*n. -/
theorem four_columns_even_draw (n : Nat) (hn : 1 ≤ n) : IsDraw (2 * n) (emptyBoard 4) :=
  ⟨black_nonloss_four_columns (by omega) (by omega),
    white_nonloss_four_columns (by omega) (by omega)⟩

theorem four_columns_even_no_forced_win (n : Nat) (hn : 1 ≤ n) :
    (¬ ∃ k, WinFor (2 * n) .black k (emptyBoard 4)) ∧
    (¬ ∃ k, WinFor (2 * n) .white k (emptyBoard 4)) :=
  draw_excludes_forced_wins (four_columns_even_draw n hn)

#print axioms start3_safe
#print axioms opening3_safe
#print axioms black_nonloss_four_columns
#print axioms four_columns_even_draw
#print axioms four_columns_even_no_forced_win
end Connect4.FourColumns
