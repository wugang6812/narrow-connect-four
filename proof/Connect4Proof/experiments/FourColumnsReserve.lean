import experiments.FourColumnsContinuation

namespace Connect4.FourColumns

/-! Shared support state for the two reserve-column exits of Proposition 5.3. -/
structure Core0 (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup : Support0 b
  h0pat : Legal h b 0 → TopBlack (b 0) ∨ b 0 = [.black, .white]
  htop : ∀ d, d ≠ 0 → Legal h b d → TopBlack (b d)
  fb0 : stone (b 0) 0 = some .black
  fb30 : stone (b 3) 0 = some .black
  horizontal : Locked h b 3 2
  hnw : ¬ HasFour h b .white

structure OpenCore0 (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup : Support0 b
  h0pat : c ≠ 0 → Legal h b 0 → TopBlack (b 0) ∨ b 0 = [.black, .white]
  htop : ∀ d, d ≠ c → d ≠ 0 → Legal h b d → TopBlack (b d)
  fb0 : stone (b 0) 0 = some .black
  fb30 : stone (b 3) 0 = some .black
  horizontal : Locked h b 3 2
  hnw : ¬ HasFour h b .white

theorem core0_white {h : Nat} {b : Board 4} {c : Fin 4}
    (hp : Core0 h b) (hc : Legal h b c) (hnb : ¬ HasFour h b .black)
    (guard : stone (play b c .white 1) 3 ≠ some .white ∨
      stone (play b c .white 2) 4 ≠ some .white) : OpenCore0 h (play b c .white) c := by
  have hc0 : c = (0 : Fin 4) → TopBlack (b 0) ∨ b 0 = [.black, .white] := by
    intro he; apply hp.h0pat; simpa only [he] using hc
  have hct : c ≠ (0 : Fin 4) → TopBlack (b c) := fun he => hp.htop c he hc
  have hv := play_valid hp.hv (p := Player.white) hc
  have hh := locked_play hp.horizontal (p := Player.white) hc
  refine ⟨hv, ?_, hsup0_play hp.hsup hc0 hct, ?_, ?_, ?_, ?_, hh, ?_⟩
  · rw [toMove_play', hp.htm]; rfl
  · intro hn hl
    rw [play_ne b c 0 .white (Ne.symm hn)]
    apply hp.h0pat
    simpa only [Legal, play_ne b c 0 .white (Ne.symm hn)] using hl
  · intro d hdc hd0 hl
    rw [play_ne b c d .white hdc]
    apply hp.htop d hd0
    simpa only [Legal, play_ne b c d .white hdc] using hl
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hp.fb0)]; exact hp.fb0
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hp.fb30)]; exact hp.fb30
  · exact noWhiteFour_descent0 hp.hsup hc0 hct hp.fb0 hp.fb30 guard
      (locked_not_white hv hh) hp.hnw hnb

theorem core0_black {h : Nat} {b : Board 4} {c e : Fin 4}
    (hw : OpenCore0 h b c) (he : Legal h b e) (hce : e = c ∨ ¬ Legal h b c) :
    Core0 h (play b e .black) := by
  refine ⟨play_valid hw.hv he, ?_, support0_black hw.hsup, ?_, ?_, ?_, ?_,
    locked_play hw.horizontal he, hasFour_play_other (by decide) hw.hnw⟩
  · rw [toMove_play', hw.htm]; rfl
  · intro hl
    by_cases he0 : e = (0 : Fin 4)
    · rw [← he0, play_eq]; exact Or.inl (topBlack_append_black _)
    · rw [play_ne b e 0 .black (Ne.symm he0)]
      have hl0 : Legal h b 0 := by
        simpa only [Legal, play_ne b e 0 .black (Ne.symm he0)] using hl
      apply hw.h0pat _ hl0
      intro hc0
      rcases hce with hec | hnc
      · exact he0 (hec.trans hc0)
      · exact hnc (by simpa only [hc0] using hl0)
  · intro d hd0 hl
    by_cases hde : d = e
    · rw [hde, play_eq]; exact topBlack_append_black _
    · rw [play_ne b e d .black hde]
      have hl0 : Legal h b d := by
        simpa only [Legal, play_ne b e d .black hde] using hl
      apply hw.htop d _ hd0 hl0
      intro hdc
      rcases hce with hec | hnc
      · exact hde (hdc.trans hec.symm)
      · exact hnc (by simpa only [hdc] using hl0)
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hw.fb0)]; exact hw.fb0
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hw.fb30)]; exact hw.fb30

theorem old_stone_preserved {b : Board 4} {c d : Fin 4} {p q : Player} {i : Nat}
    (hs : stone (b d) i = some q) : stone (play b c p d) i = some q := by
  rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hs)]; exact hs

theorem not_white_black {b : Board 4} {c d : Fin 4} {i : Nat}
    (hs : stone (b d) i ≠ some .white) : stone (play b c .black d) i ≠ some .white := by
  intro hw
  by_cases hd : d = c
  · subst d; rw [play_eq] at hw
    exact hs (stone_append_other (by decide) hw)
  · exact hs (by simpa only [play_ne b c d .black hd] using hw)

theorem not_white_append_miss {b : Board 4} {c d : Fin 4} {i : Nat}
    (hs : stone (b d) i ≠ some .white) (hi : i ≠ (b d).length) :
    stone (play b c .white d) i ≠ some .white := by
  by_cases hd : d = c
  · subst d; rw [play_eq, stone_append]
    split
    · exact hs
    · simp
  · simpa only [play_ne b c d .white hd] using hs

/-- The reserve target is even-indexed, hence White cannot fill it while the
    reserve has odd length. Once occupied by Black the caller's exit applies. -/
theorem reserve0_safe (h : Nat) (hh : h % 2 = 0) (r : Fin 4) (t : Nat)
    (ht : t % 2 = 0) (htop : t < h) (extra : Board 4 → Prop)
    (extra_move : ∀ b c p, extra b → extra (play b c p))
    (guard : ∀ b c, Core0 h b → extra b → (b r).length ≤ t →
      stone (play b c .white r) t ≠ some .white →
      stone (play b c .white 1) 3 ≠ some .white ∨
        stone (play b c .white 2) 4 ≠ some .white)
    (finish : ∀ b, Core0 h b → extra b → stone (b r) t = some .black → CanAvoidLoss h .black b)
    {b : Board 4} (hp : Core0 h b) (hx : extra b)
    (hr : (b r).length % 2 = 1) (hn : stone (b r) t ≠ some .white) :
    CanAvoidLoss h .black b := by
  have induction_step : ∀ k b, Core0 h b → extra b → (b r).length % 2 = 1 →
      stone (b r) t ≠ some .white → SafeFor h .black k b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro b hp hx hr hn
      by_cases htarget : stone (b r) t = some .black
      · exact finish b hp hx htarget k
      have hlen : (b r).length ≤ t := by
        by_contra hl
        exact htarget (occupied_not_white (by omega) hn)
      cases k with
      | zero => exact hp.hnw
      | succ k =>
        refine ⟨hp.hnw, ?_⟩
        by_cases hbf : HasFour h b .black
        · exact Or.inl hbf
        · right; right
          rw [if_neg (by rw [hp.htm]; decide), hp.htm]
          intro c hc
          have hn' : stone (play b c .white r) t ≠ some .white :=
            not_white_append_miss hn (by omega)
          have hw := core0_white hp hc hbf (guard b c hp hx hlen hn')
          have hx' := extra_move b c .white hx
          cases k with
          | zero => exact hw.hnw
          | succ k =>
            refine ⟨hw.hnw, ?_⟩
            by_cases hf : BoardFull h (play b c .white)
            · exact Or.inr (Or.inl hf)
            · right; right
              rw [if_pos hw.htm, hw.htm]
              by_cases hcr : c = r
              · subst c
                by_cases hcov : Legal h (play b r .white) r
                · refine ⟨r, hcov, ?_⟩
                  apply ih k (by omega) _ (core0_black hw hcov (Or.inl rfl))
                    (extra_move _ r .black hx') _ (not_white_black hn')
                  simp only [play_eq, List.length_append, List.length_singleton]
                  omega
                · have hfull : h ≤ (play b r .white r).length := by
                    unfold Legal at hcov; omega
                  obtain ⟨e, he⟩ := exists_legal hw.hv hf
                  refine ⟨e, he, ?_⟩
                  have hc0 := core0_black hw he (Or.inr hcov)
                  have hx0 := extra_move _ e .black hx'
                  have hl : t < (play b r .white r).length := by
                    omega
                  exact finish _ hc0 hx0 (old_stone_preserved (occupied_not_white hl hn')) k
              · have hr' : (play b c .white r).length % 2 = 1 := by
                  simpa only [play_ne b c r .white (Ne.symm hcr)] using hr
                by_cases hcov : Legal h (play b c .white) c
                · refine ⟨c, hcov, ?_⟩
                  apply ih k (by omega) _ (core0_black hw hcov (Or.inl rfl))
                    (extra_move _ c .black hx') _ (not_white_black hn')
                  simpa only [play_ne _ c r .black (Ne.symm hcr)] using hr'
                · obtain ⟨e, her, he⟩ := reserve_reply_exists r hw.hv hh hw.htm hr'
                  refine ⟨e, he, ?_⟩
                  apply ih k (by omega) _ (core0_black hw he (Or.inr hcov))
                    (extra_move _ e .black hx') _ (not_white_black hn')
                  simpa only [play_ne _ e r .black (Ne.symm her)] using hr'
  exact fun k => induction_step k b hp hx hr hn

theorem reserve0_blocker {h : Nat} (hh : h % 2 = 0) (h5 : 5 ≤ h) {b : Board 4}
    (hp : Core0 h b) (hr : (b 2).length % 2 = 1) (hn : stone (b 2) 4 ≠ some .white) :
    CanAvoidLoss h .black b := by
  apply reserve0_safe h hh 2 4 (by decide) (by omega) (fun _ => True)
    (fun _ _ _ _ => True.intro) _ _ hp True.intro hr hn
  · intro b c _ _ _ hn'; exact Or.inr hn'
  · intro b hp _ ht
    exact pd0b_safe ⟨hp.hv, hp.htm, hp.hsup, hp.h0pat, hp.htop, hp.fb0, hp.fb30,
      hp.horizontal, Or.inr (Or.inl ht), hp.hnw⟩

#print axioms reserve0_blocker

theorem black_descending_four {h : Nat} {b : Board 4} (h4 : 4 ≤ h)
    (h0 : stone (b 0) 3 = some .black) (h1 : stone (b 1) 2 = some .black)
    (h2 : stone (b 2) 1 = some .black) (h3 : stone (b 3) 0 = some .black) :
    HasFour h b .black := by
  have hh0 : (0 : Int) < h := by omega
  have hh1 : (1 : Int) < h := by omega
  have hh2 : (2 : Int) < h := by omega
  have hh3 : (3 : Int) < h := by omega
  right; right; right
  refine ⟨0, 3, ?_⟩
  intro i
  fin_cases i <;> simp [cellAtInt, hh0, hh1, hh2, hh3, h0, h1, h2, h3] <;> omega

theorem black_won_safe {h : Nat} {b : Board 4} (hn : ¬ HasFour h b .white)
    (hb : HasFour h b .black) : CanAvoidLoss h .black b := by
  intro k; cases k with
  | zero => exact hn
  | succ k => exact ⟨hn, Or.inl hb⟩

theorem reserve0_winner {h : Nat} (hh : h % 2 = 0) (h4 : 4 ≤ h) {b : Board 4}
    (hp : Core0 h b) (hr : (b 1).length % 2 = 1) (hn : stone (b 1) 2 ≠ some .white)
    (h0 : stone (b 0) 3 = some .black) (h2 : stone (b 2) 1 = some .black) :
    CanAvoidLoss h .black b := by
  apply reserve0_safe h hh 1 2 (by decide) (by omega)
    (fun b => stone (b 0) 3 = some .black ∧ stone (b 2) 1 = some .black)
    _ _ _ hp ⟨h0, h2⟩ hr hn
  · intro b c p hx
    exact ⟨old_stone_preserved hx.1, old_stone_preserved hx.2⟩
  · intro b c _ _ hl _
    left
    have hs : stone (play b c .white 1) 3 = none := by
      apply stone_none
      by_cases hc : c = (1 : Fin 4)
      · subst c; rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
      · rw [play_ne _ c 1 .white (Ne.symm hc)]; omega
    rw [hs]; simp
  · intro b hp hx ht
    exact black_won_safe hp.hnw (black_descending_four h4 hx.1 ht hx.2 hp.fb30)

theorem w0a_open_core {h : Nat} {b : Board 4} (hw : W0A h b 3)
    (hf : ¬ Legal h b 3) : OpenCore0 h b 3 := by
  refine ⟨hw.hv, hw.htm, hw.hsup0, ?_, ?_, hw.fb0, hw.fb30,
    Or.inr (Or.inl ⟨hf, hw.fb32⟩), hw.hnw⟩
  · intro hn _
    rcases hw.h0tf with ht | hb | he
    · exact Or.inl ht
    · exact Or.inr hb
    · exact False.elim (hn he)
  · intro d hdc hd0 hl
    exact hw.htopO d hdc hl hd0

structure Waiting0Extra (b : Board 4) : Prop where
  fb01 : stone (b 0) 1 = some .white
  nw03 : stone (b 0) 3 ≠ some .white
  nw21 : stone (b 2) 1 ≠ some .white

theorem waiting0_extra_white {h : Nat} {b : Board 4} (hp : PD0A h b)
    (hx : Waiting0Extra b) (c : Fin 4) : Waiting0Extra (play b c .white) := by
  refine ⟨old_stone_preserved hx.fb01, not_white_append_miss hx.nw03 ?_,
    not_white_append_miss hx.nw21 ?_⟩
  · have hp0 : (b 0).length % 2 = 0 := hp.hc0; omega
  · have hp2 : (b 2).length % 2 = 0 := hp.hc2; omega

theorem waiting0_extra_black {b : Board 4} (hx : Waiting0Extra b) (c : Fin 4) :
    Waiting0Extra (play b c .black) :=
  ⟨old_stone_preserved hx.fb01, not_white_black hx.nw03, not_white_black hx.nw21⟩

/-- All four cases of paper Proposition 5.3, including the immediate/forced
    descending win rather than the erroneous old third-column blocker. -/
theorem w0a_endgame {h : Nat} (hh : h % 2 = 0) {b : Board 4}
    (hw : W0A h b 3) (hx : Waiting0Extra b) (hf : ¬ Legal h b 3) :
    CanAvoidLoss h .black b := by
  by_cases hsmall : h ≤ 4
  · exact w0a_endgame_blocked hw hf (Or.inl hsmall)
  have h5 : 5 ≤ h := by omega
  by_cases hb0 : b 0 = [.black, .white]
  · exact w0a_clear_exception hw hf hb0 (by omega)
  by_cases hb1 : 3 < (b 1).length
  · exact w0a_endgame_blocked hw hf (Or.inr hb1)
  have hp1 : (b 1).length % 2 = 0 := hw.hc1W (by decide)
  have hp2 : (b 2).length % 2 = 0 := hw.hc2W (by decide)
  have hlen1 : (b 1).length ≤ 2 := by omega
  have hc := w0a_open_core hw hf
  have hlen0 : 4 ≤ (b 0).length := by
    have hl := stone_bound _ _ _ hx.fb01
    have hp0 : (b 0).length % 2 = 0 := hw.hc0W (by decide)
    by_contra hn
    have he : (b 0).length = 2 := by omega
    rcases hw.h0tf with ht | hb | he0
    · rcases ht with hempty | htop
      · change (b 0).length = 0 at hempty; omega
      · change stone (b 0) ((b 0).length - 1) = some .black at htop
        have hs : stone (b 0) 1 = some .black := by simpa [he] using htop
        rw [hx.fb01] at hs; cases hs
    · exact hb0 hb
    · exact (by decide : (3 : Fin 4) ≠ 0) he0
  have hb03 := occupied_not_white (by omega : 3 < (b 0).length) hx.nw03
  by_cases hb2 : (b 2).length ≤ 4
  · have he : Legal h b 2 := by unfold Legal; omega
    have hp := core0_black hc he (Or.inr hf)
    have hr : (play b 2 .black 2).length % 2 = 1 := by
      rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
    have hn : stone (play b 2 .black 2) 4 ≠ some .white := by
      apply not_white_black
      rw [stone_none _ _ hb2]; simp
    have hs := reserve0_blocker hh h5 hp hr hn
    intro k; cases k with
    | zero => exact hw.hnw
    | succ k =>
      refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
      rw [if_pos hw.htm, hw.htm]
      exact ⟨2, he, hs k⟩
  · have he : Legal h b 1 := by unfold Legal; omega
    have hp := core0_black hc he (Or.inr hf)
    have hr : (play b 1 .black 1).length % 2 = 1 := by
      rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
    have hn : stone (play b 1 .black 1) 2 ≠ some .white := by
      apply not_white_black
      rw [stone_none _ _ hlen1]; simp
    have hb21 := occupied_not_white (by omega : 1 < (b 2).length) hx.nw21
    have hs := reserve0_winner hh (by omega) hp hr hn
      (old_stone_preserved hb03) (old_stone_preserved hb21)
    intro k; cases k with
    | zero => exact hw.hnw
    | succ k =>
      refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
      rw [if_pos hw.htm, hw.htm]
      exact ⟨1, he, hs k⟩

theorem pd0a_pairing (h : Nat) (hh : h % 2 = 0) (k : Nat) :
    (∀ b, PD0A h b → Waiting0Extra b → SafeFor h .black k b) ∧
    (∀ b c, W0A h b c → Waiting0Extra b → SafeFor h .black k b) := by
  induction k with
  | zero => exact ⟨fun _ hp _ => hp.hnw, fun _ _ hw _ => hw.hnw⟩
  | succ k ih =>
    constructor
    · intro b hp hx
      refine ⟨hp.hnw, ?_⟩
      by_cases hb : HasFour h b .black
      · exact Or.inl hb
      · right; right
        rw [if_neg (by rw [hp.htm]; decide), hp.htm]
        exact fun c hc => ih.2 _ c (pd0a_to_w0a hp hc hb) (waiting0_extra_white hp hx c)
    · intro b c hw hx
      by_cases hc : Legal h b c
      · refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
        rw [if_pos hw.htm, hw.htm]
        exact ⟨c, hc, ih.1 _ (w0a_reply hw hc) (waiting0_extra_black hx c)⟩
      · have he := w0a_only_fourth_can_fill hh hw hc
        subst c
        exact w0a_endgame hh hw hx hc (k + 1)

/-- Paper Proposition 5.3 for EVERY positive even height, not just H=2/4. -/
theorem opening0_safe {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .black opening0 :=
  fun k => (pd0a_pairing h hh k).1 _ (opening0_state h2) ⟨rfl, by decide, by decide⟩

#print axioms opening0_safe
end Connect4.FourColumns
