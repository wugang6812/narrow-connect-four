import experiments.FourColumnsRight

namespace Connect4.FourColumns

theorem black_step_safe {h : Nat} {b : Board 4} {e : Fin 4}
    (ht : toMove b = .black) (hn : ¬ HasFour h b .white) (he : Legal h b e)
    (hs : CanAvoidLoss h .black (play b e .black)) : CanAvoidLoss h .black b := by
  intro k; cases k with
  | zero => exact hn
  | succ k =>
    refine ⟨hn, Or.inr (Or.inr ?_)⟩
    rw [if_pos ht, ht]
    exact ⟨e, he, hs k⟩

theorem core13_retarget {h : Nat} {b : Board 4} {c : Fin 4}
    (hw : OpenCore13 h b c) (ht : Top13 b c) (e : Fin 4) : OpenCore13 h b e := by
  refine ⟨hw.hv, hw.htm, hw.hsup, ?_, hw.fb0, hw.fb01, hw.hnw⟩
  intro d _ hl
  by_cases hd : d = c
  · subst d; exact ht
  · exact hw.htop d hd hl

theorem length_play_le (b : Board 4) (c d : Fin 4) (p : Player) :
    (play b c p d).length ≤ (b d).length + 1 := by
  by_cases hd : d = c
  · subst d; simp [play_eq]
  · rw [play_ne b c d p hd]; omega

theorem empty_target_after_white {b : Board 4} (c d : Fin 4) (i : Nat)
    (hl : (b d).length + 1 ≤ i) : stone (play b c .white d) i ≠ some .white := by
  rw [stone_none _ _ (le_trans (length_play_le b c d .white) hl)]; simp

theorem even_cover_legal {h : Nat} {b : Board 4} {c : Fin 4}
    (hh : h % 2 = 0) (hp : (b c).length % 2 = 0) (hc : Legal h b c) :
    Legal h (play b c .white) c := by
  unfold Legal at hc ⊢
  rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega

theorem pair_parity {b : Board 4} (c : Fin 4) (f : Fin 4 → Nat)
    (hp : ∀ d, (b d).length % 2 = f d) :
    ∀ d, (play (play b c .white) c .black d).length % 2 = f d := by
  intro d
  by_cases hd : d = c
  · subst d
    rw [play_eq, play_eq]; simp only [List.length_append, List.length_singleton]
    have := hp c; omega
  · simpa only [play_ne _ c d .black hd, play_ne _ c d .white hd] using hp d

def xParity (d : Fin 4) : Nat := if d = 3 then 1 else 0

structure XState (h : Nat) (b : Board 4) : Prop where
  core : Core13 h b
  diagonal : FixedLine h b 3
  parity : ∀ d, (b d).length % 2 = xParity d
  nw13 : stone (b 1) 3 ≠ some .white
  nw23 : stone (b 2) 3 ≠ some .white
  nw34 : stone (b 3) 4 ≠ some .white

theorem x_endgame {h : Nat} (hh : h % 2 = 0) {b : Board 4}
    (hw : OpenCore13 h b 3) (hf : ¬ Legal h b 3) (hd : FixedLine h b 3)
    (hp1 : (b 1).length % 2 = 0) (hp2 : (b 2).length % 2 = 0)
    (hn13 : stone (b 1) 3 ≠ some .white) (hn23 : stone (b 2) 3 ≠ some .white)
    (hn34 : stone (b 3) 4 ≠ some .white) : CanAvoidLoss h .black b := by
  by_cases hsmall : h ≤ 4
  · exact permanent13_open_safe hw hd ⟨0, Or.inr hsmall⟩
  have h5 : 5 ≤ h := by omega
  by_cases hb1 : 3 < (b 1).length
  · exact permanent13_open_safe hw hd ⟨1, Or.inl (occupied_not_white hb1 hn13)⟩
  have hl1 : (b 1).length ≤ 2 := by omega
  by_cases hb2 : (b 2).length ≤ 2
  · have he : Legal h b 2 := by unfold Legal; omega
    have hp := core13_black hw he (Or.inr hf)
    have hr : (play b 2 .black 2).length % 2 = 1 := by
      rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
    have hn : stone (play b 2 .black 2) 2 ≠ some .white := by
      apply not_white_black; rw [stone_none _ _ hb2]; simp
    exact black_step_safe hw.htm hw.hnw he (reserve13_U hh (by omega) hp (fixed_line_move hd) hr hn)
  · have hb23 := occupied_not_white (by omega : 3 < (b 2).length) hn23
    have hb34 : stone (b 3) 4 = some .black := by
      apply occupied_not_white _ hn34
      unfold Legal at hf; omega
    have he : Legal h b 1 := by unfold Legal; omega
    have hp := core13_black hw he (Or.inr hf)
    have hr : (play b 1 .black 1).length % 2 = 1 := by
      rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
    have hn : stone (play b 1 .black 1) 2 ≠ some .white := by
      apply not_white_black; rw [stone_none _ _ hl1]; simp
    exact black_step_safe hw.htm hw.hnw he (reserve13_win hh h5 hp (fixed_line_move hd) hr hn
      (old_stone_preserved hb23) (old_stone_preserved hb34))

/-- Paper Lemma 5.4: waiting in the X family and all its full-column exits. -/
theorem x_state_safe {h : Nat} (hh : h % 2 = 0) {b : Board 4} (hp : XState h b) :
    CanAvoidLoss h .black b := by
  have step : ∀ k b, XState h b → SafeFor h .black k b := by
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
          have hp1 : (b 1).length % 2 = 0 := by simpa [xParity] using hp.parity 1
          have hp2 : (b 2).length % 2 = 0 := by simpa [xParity] using hp.parity 2
          have hp3 : (b 3).length % 2 = 1 := by simpa [xParity] using hp.parity 3
          have hn13 := not_white_append_miss (c := c) hp.nw13 (by omega)
          have hn23 := not_white_append_miss (c := c) hp.nw23 (by omega)
          have hn34 := not_white_append_miss (c := c) hp.nw34 (by omega)
          have hd := fixed_line_move (c := c) (p := Player.white) hp.diagonal
          have hw := core13_white hp.core hc hb
            (fixed_line_guard (play_valid hp.core.hv hc) hd) ⟨1, hn13⟩
          cases k with
          | zero => exact hw.hnw
          | succ k =>
            by_cases hcov : Legal h (play b c .white) c
            · refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
              rw [if_pos hw.htm, hw.htm]
              refine ⟨c, hcov, ih k (by omega) _ ?_⟩
              exact ⟨core13_black hw hcov (Or.inl rfl), fixed_line_move hd,
                pair_parity c xParity hp.parity, not_white_black hn13,
                not_white_black hn23, not_white_black hn34⟩
            · have he : c = 3 := by
                by_contra hn
                have hc0 : (b c).length % 2 = 0 := by simpa [xParity, hn] using hp.parity c
                exact hcov (even_cover_legal hh hc0 hc)
              subst c
              apply x_endgame hh hw hcov hd _ _ hn13 hn23 hn34 (k + 1)
              · simpa only [play_ne b 3 1 .white (by decide)] using hp1
              · simpa only [play_ne b 3 2 .white (by decide)] using hp2
  exact fun k => step k b hp

#print axioms x_state_safe

theorem black_vertical_four {h : Nat} {b : Board 4} (h4 : 4 ≤ h)
    (hb : b 0 = [.black, .black, .black, .black]) : HasFour h b .black := by
  have hh1 : (1 : Int) < h := by omega
  have hh2 : (2 : Int) < h := by omega
  have hh3 : (3 : Int) < h := by omega
  left; refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> simp [cellAtInt, hh1, hh2, hh3, hb, stone] <;> omega

theorem vertical_threat_safe {h : Nat} (h4 : 4 ≤ h) {b : Board 4}
    (hp : Core13 h b) (hb0 : b 0 = [.black, .black, .black])
    (hl1 : (b 1).length ≤ 1) (hl2 : (b 2).length ≤ 1)
    (finish : OpenCore13 h (play b 0 .white) 0 → CanAvoidLoss h .black (play b 0 .white)) :
    CanAvoidLoss h .black b := by
  intro k; cases k with
  | zero => exact hp.hnw
  | succ k =>
    refine ⟨hp.hnw, ?_⟩
    by_cases hb : HasFour h b .black
    · exact Or.inl hb
    · right; right
      rw [if_neg (by rw [hp.htm]; decide), hp.htm]
      intro c hc
      have hw := core13_white hp hc hb
        ⟨1, empty_target_after_white c 1 2 (by omega)⟩
        ⟨2, empty_target_after_white c 2 2 (by omega)⟩
      by_cases hc0 : c = 0
      · subst c; exact finish hw k
      · have he : Legal h (play b c .white) 0 := by
          unfold Legal
          rw [play_ne _ c 0 .white (Ne.symm hc0), hb0]
          simp; omega
        have hwin : HasFour h (play (play b c .white) 0 .black) .black := by
          apply black_vertical_four h4
          rw [play_eq, play_ne _ c 0 .white (Ne.symm hc0), hb0]
          rfl
        exact black_step_safe hw.htm hw.hnw he
          (black_won_safe (hasFour_play_other (by decide) hw.hnw) hwin) k

structure ZState (h : Nat) (b : Board 4) : Prop where
  core : Core13 h b
  upper : FixedLine h b 4
  b1 : b 1 = []
  b2 : b 2 = []
  full3 : ¬ Legal h b 3
  odd0 : (b 0).length % 2 = 1

theorem z_state_safe {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hp : ZState h b) : CanAvoidLoss h .black b := by
  have step : ∀ k b, ZState h b → SafeFor h .black k b := by
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
          have hu := fixed_line_move (c := c) (p := Player.white) hp.upper
          have hw := core13_white hp.core hc hb
            ⟨1, empty_target_after_white c 1 2 (by rw [hp.b1]; decide)⟩
            (fixed_line_guard (play_valid hp.core.hv hc) hu)
          fin_cases c
          · change Legal h b 0 at hc
            change SafeFor h .black k (play b 0 .white)
            change OpenCore13 h (play b 0 .white) 0 at hw
            change FixedLine h (play b 0 .white) 4 at hu
            by_cases hcov : Legal h (play b 0 .white) 0
            · cases k with
              | zero => exact hw.hnw
              | succ k =>
                refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
                rw [if_pos hw.htm, hw.htm]
                refine ⟨0, hcov, ih k (by omega) _ ?_⟩
                refine ⟨core13_black hw hcov (Or.inl rfl), fixed_line_move hu, ?_, ?_, ?_, ?_⟩
                · simpa [play] using hp.b1
                · simpa [play] using hp.b2
                · simpa [Legal, play] using hp.full3
                · simp only [play_eq, List.length_append, List.length_singleton]
                  have := hp.odd0; omega
            · have he : Legal h (play b 0 .white) 1 := by simp [Legal, play, hp.b1]; omega
              have hn : stone (play (play b 0 .white) 1 .black 1) 2 ≠ some .white := by
                simp [play, hp.b1, stone]
              have hr : (play (play b 0 .white) 1 .black 1).length % 2 = 1 := by simp [play, hp.b1]
              exact black_step_safe hw.htm hw.hnw he
                (reserve13_D hh (by omega) (core13_black hw he (Or.inr hcov)) (fixed_line_move hu) hr hn) k
          · change OpenCore13 h (play b 1 .white) 1 at hw
            change FixedLine h (play b 1 .white) 4 at hu
            have ht : Top13 (play b 1 .white) 1 := by right; exact ⟨Or.inl rfl, by simp [play, hp.b1]⟩
            have he : Legal h (play b 1 .white) 2 := by simp [Legal, play, hp.b2]; omega
            have hr : (play (play b 1 .white) 2 .black 1).length % 2 = 1 := by simp [play, hp.b1]
            have hn : stone (play (play b 1 .white) 2 .black 1) 2 ≠ some .white := by simp [play, hp.b1, stone]
            exact black_step_safe hw.htm hw.hnw he
              (reserve13_D hh (by omega) (core13_black (core13_retarget hw ht 2) he (Or.inl rfl))
                (fixed_line_move hu) hr hn) k
          · change OpenCore13 h (play b 2 .white) 2 at hw
            change FixedLine h (play b 2 .white) 4 at hu
            have he : Legal h (play b 2 .white) 2 := by simp [Legal, play, hp.b2]; omega
            have hd : FixedLine h (play (play b 2 .white) 2 .black) 3 := by
              refine ⟨2, Or.inl ?_⟩
              simp [play, hp.b2, stone]
            exact black_step_safe hw.htm hw.hnw he
              (permanent13_safe (core13_black hw he (Or.inl rfl)) hd (fixed_line_move hu)) k
          · exact False.elim (hp.full3 hc)
  exact fun k => step k b hp

#print axioms z_state_safe

theorem full_right_empty_safe {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hw : OpenCore13 h b 3) (hf : ¬ Legal h b 3)
    (hb0 : b 0 = [.black, .black]) (hb1 : b 1 = []) (hb2 : b 2 = []) :
    CanAvoidLoss h .black b := by
  have he : Legal h b 0 := by simp [Legal, hb0]; omega
  have hp := core13_black hw he (Or.inr hf)
  apply black_step_safe hw.htm hw.hnw he
  apply vertical_threat_safe h4 hp (by simp [play, hb0])
    (by simp [play, hb1]) (by simp [play, hb2])
  intro hw'
  by_cases hs : h ≤ 4
  · have hf0 : ¬ Legal h (play (play b 0 .black) 0 .white) 0 := by
      simp [Legal, play, hb0]; omega
    have he1 : Legal h (play (play b 0 .black) 0 .white) 1 := by simp [Legal, play, hb1]; omega
    have hp1 := core13_black hw' he1 (Or.inr hf0)
    apply black_step_safe hw'.htm hw'.hnw he1
    apply reserve13_D hh (by omega) hp1 ⟨0, Or.inr hs⟩
    · simp [play, hb1]
    · simp [play, hb1, stone]
  · have he0 : Legal h (play (play b 0 .black) 0 .white) 0 := by simp [Legal, play, hb0]; omega
    have hp0 := core13_black hw' he0 (Or.inl rfl)
    apply black_step_safe hw'.htm hw'.hnw he0
    apply z_state_safe hh h4
    refine ⟨hp0, ⟨0, Or.inl ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp [play, hb0, stone]
    · simpa [play] using hb1
    · simpa [play] using hb2
    · simpa [Legal, play] using hf
    · simp [play, hb0]

theorem full_right_y_threat {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hw : OpenCore13 h b 3) (hf : ¬ Legal h b 3)
    (hb0 : b 0 = [.black, .black]) (hb1 : b 1 = [.white]) (hb2 : b 2 = [.black]) :
    CanAvoidLoss h .black b := by
  have he : Legal h b 0 := by simp [Legal, hb0]; omega
  have hp := core13_black hw he (Or.inr hf)
  apply black_step_safe hw.htm hw.hnw he
  apply vertical_threat_safe h4 hp (by simp [play, hb0])
    (by simp [play, hb1]) (by simp [play, hb2])
  intro hw'
  by_cases hs : h ≤ 4
  · have hf0 : ¬ Legal h (play (play b 0 .black) 0 .white) 0 := by
      simp [Legal, play, hb0]; omega
    have he2 : Legal h (play (play b 0 .black) 0 .white) 2 := by simp [Legal, play, hb2]; omega
    have hp2 := core13_black hw' he2 (Or.inr hf0)
    apply black_step_safe hw'.htm hw'.hnw he2
    apply permanent13_safe hp2 _ ⟨0, Or.inr hs⟩
    refine ⟨2, Or.inl ?_⟩
    simp [play, hb2, stone]
  · have he0 : Legal h (play (play b 0 .black) 0 .white) 0 := by simp [Legal, play, hb0]; omega
    have hp0 := core13_black hw' he0 (Or.inl rfl)
    apply black_step_safe hw'.htm hw'.hnw he0
    apply reserve13_D hh (by omega) hp0 ⟨0, Or.inl (by simp [play, hb0, stone])⟩
    · simp [play, hb1]
    · simp [play, hb1, stone]

theorem list_two_black (l : List Player) (hl : l.length = 2)
    (h0 : stone l 0 = some .black) (h1 : stone l 1 = some .black) : l = [.black, .black] := by
  cases l with
  | nil => simp at hl
  | cons a l =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      have hl0 : l.length = 0 := by simp only [List.length_cons] at hl; omega
      have he : l = [] := by cases l <;> simp_all
      subst l
      simp [stone] at h0 h1
      subst a; subst b; rfl

structure YState (h : Nat) (b : Board 4) : Prop where
  core : Core13 h b
  b1 : b 1 = [.white]
  b2 : b 2 = [.black]
  even0 : (b 0).length % 2 = 0
  odd3 : (b 3).length % 2 = 1
  nw03 : stone (b 0) 3 ≠ some .white

theorem y_endgame {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hw : OpenCore13 h b 3) (hf : ¬ Legal h b 3)
    (hb1 : b 1 = [.white]) (hb2 : b 2 = [.black])
    (hp0 : (b 0).length % 2 = 0) (hn03 : stone (b 0) 3 ≠ some .white) :
    CanAvoidLoss h .black b := by
  by_cases hl : 3 < (b 0).length
  · have hd : FixedLine h b 3 := ⟨0, Or.inl (occupied_not_white hl hn03)⟩
    have he : Legal h b 1 := by simp [Legal, hb1]; omega
    have hp := core13_black hw he (Or.inr hf)
    apply black_step_safe hw.htm hw.hnw he
    apply reserve13_U hh (by omega) hp (fixed_line_move hd)
    · simp [play, hb2]
    · simp [play, hb2, stone]
  · have hl0 := stone_bound _ _ _ hw.fb01
    have he : (b 0).length = 2 := by omega
    exact full_right_y_threat hh h4 hw hf (list_two_black _ he hw.fb0 hw.fb01) hb1 hb2

theorem y_state_safe {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hp : YState h b) : CanAvoidLoss h .black b := by
  have step : ∀ k b, YState h b → SafeFor h .black k b := by
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
          have hn03 := not_white_append_miss (c := c) hp.nw03 (by have := hp.even0; omega)
          by_cases hext : c = 0 ∨ c = 3
          · by_cases hcov : Legal h (play b c .white) c
            · cases k with
              | zero => exact hw.hnw
              | succ k =>
                refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
                rw [if_pos hw.htm, hw.htm]
                refine ⟨c, hcov, ih k (by omega) _ ?_⟩
                refine ⟨core13_black hw hcov (Or.inl rfl), ?_, ?_, ?_, ?_, not_white_black hn03⟩
                · rcases hext with he | he <;> subst c <;> simpa [play] using hp.b1
                · rcases hext with he | he <;> subst c <;> simpa [play] using hp.b2
                · rcases hext with he | he <;> subst c
                  · simp only [play_eq, List.length_append, List.length_singleton]
                    have := hp.even0; omega
                  · simpa [play] using hp.even0
                · rcases hext with he | he <;> subst c
                  · simpa [play] using hp.odd3
                  · simp only [play_eq, List.length_append, List.length_singleton]
                    have := hp.odd3; omega
            · have he3 : c = 3 := by
                rcases hext with he0 | he3
                · subst c; exact False.elim (hcov (even_cover_legal hh hp.even0 hc))
                · exact he3
              subst c
              exact y_endgame hh h4 hw hcov (by simpa [play] using hp.b1)
                (by simpa [play] using hp.b2) (by simpa [play] using hp.even0) hn03 k
          · have hc12 : c = 1 ∨ c = 2 := by
              have := c.isLt
              have hn0 : c.val ≠ 0 := fun he => hext (Or.inl (Fin.ext he))
              have hn3 : c.val ≠ 3 := fun he => hext (Or.inr (Fin.ext he))
              by_cases he1 : c.val = 1
              · exact Or.inl (Fin.ext he1)
              · exact Or.inr (Fin.ext (by omega))
            rcases hc12 with he1 | he2
            · subst c
              have he : Legal h (play b 1 .white) 1 := by simp [Legal, play, hp.b1]; omega
              have hc0 := core13_black hw he (Or.inl rfl)
              have hd : FixedLine h (play (play b 1 .white) 1 .black) 3 := by
                refine ⟨1, Or.inl ?_⟩; simp [play, hp.b1, stone]
              exact black_step_safe hw.htm hw.hnw he
                (reserve13_U hh (by omega) hc0 hd (by simp [play, hp.b2]) (by simp [play, hp.b2, stone])) k
            · subst c
              have he : Legal h (play b 2 .white) 2 := by simp [Legal, play, hp.b2]; omega
              have hc0 := core13_black hw he (Or.inl rfl)
              have hu : FixedLine h (play (play b 2 .white) 2 .black) 4 := by
                refine ⟨2, Or.inl ?_⟩; simp [play, hp.b2, stone]
              exact black_step_safe hw.htm hw.hnw he
                (reserve13_D hh (by omega) hc0 hu (by simp [play, hp.b1]) (by simp [play, hp.b1, stone])) k
  exact fun k => step k b hp

#print axioms y_state_safe
#print axioms full_right_empty_safe
end Connect4.FourColumns
