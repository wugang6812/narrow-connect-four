import experiments.FourColumnsReserve

namespace Connect4.FourColumns

/-! The right-opening families have exceptional white pairs only at (1,1)
and (3,1), in zero-based coordinates. Their remaining dangerous lines are
the descending lines starting at rows 3 and 4. -/
def Support13 (b : Board 4) : Prop :=
  ∀ d i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (i = 1 ∧ (d = 1 ∨ d = 3))

def Top13 (b : Board 4) (d : Fin 4) : Prop :=
  TopBlack (b d) ∨ ((d = 1 ∨ d = 3) ∧ b d = [.white])

def LineGuard (b : Board 4) (y : Nat) : Prop :=
  ∃ d : Fin 4, stone (b d) (y - d.val) ≠ some .white

def FixedLine (h : Nat) (b : Board 4) (y : Nat) : Prop :=
  ∃ d : Fin 4, stone (b d) (y - d.val) = some .black ∨ h ≤ y - d.val

theorem fixed_line_guard {h y : Nat} {b : Board 4} (hv : Valid h b)
    (hf : FixedLine h b y) : LineGuard b y := by
  obtain ⟨d, hb | hi⟩ := hf
  · exact ⟨d, by rw [hb]; decide⟩
  · exact ⟨d, by rw [stone_none _ _ (le_trans (hv d) hi)]; simp⟩

theorem fixed_line_move {h y : Nat} {b : Board 4} {c : Fin 4} {p : Player}
    (hf : FixedLine h b y) : FixedLine h (play b c p) y := by
  obtain ⟨d, hb | hi⟩ := hf
  · exact ⟨d, Or.inl (old_stone_preserved hb)⟩
  · exact ⟨d, Or.inr hi⟩

theorem line_data {h : Nat} {b : Board 4} {p : Player} {x y dy : Int}
    (hd : HasFourDir h b p x y 1 dy) (d : Fin 4) :
    0 ≤ y + (d : Int) * dy ∧ y + (d : Int) * dy < (h : Int) ∧
      stone (b d) (y + (d : Int) * dy).toNat = some p := by
  have hs0 : cellAtInt h b x y = some p := by simpa using hd 0
  have hs3 : cellAtInt h b (x + 3) (y + 3 * dy) = some p := by simpa using hd 3
  obtain ⟨c0, hx0, _, _, _⟩ := cellAtInt_some hs0
  obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some hs3
  have h0 := c0.isLt
  have h3 := c3.isLt
  have hx : x = 0 := by omega
  have hs : cellAtInt h b (d : Int) (y + (d : Int) * dy) = some p := by
    simpa only [hx, Int.zero_add, Int.mul_one] using hd d
  obtain ⟨c, hc, hy, htop, ht⟩ := cellAtInt_some hs
  have he : c = d := Fin.ext (by omega)
  exact ⟨hy, htop, by simpa only [he] using ht⟩

theorem cell_from_stone {h : Nat} {b : Board 4} {X Y : Int} (col : Fin 4)
    (hcol : (col : Int) = X) (hX1 : 0 ≤ X) (hX2 : X < (4 : Int))
    (hY1 : 0 ≤ Y) (hY2 : Y < (h : Int)) :
    cellAtInt h b X Y = stone (b col) Y.toNat := by
  have hval : X.toNat = col.val := by omega
  simp only [cellAtInt]
  split
  · split
    · exact congrArg (fun cc : Fin 4 => stone (b cc) Y.toNat) (Fin.ext hval)
    · rename_i hy; exact absurd ⟨hY1, hY2⟩ hy
  · rename_i hx; exact absurd ⟨hX1, hX2⟩ hx

theorem line_shift_black {h : Nat} {b : Board 4} {x y dy : Int}
    (hd : HasFourDir h b .white x y 1 dy)
    (hs : ∀ d : Fin 4, 0 < y + (d : Int) * dy ∧
      stone (b d) ((y + (d : Int) * dy).toNat - 1) = some .black) :
    HasFourDir h b .black 0 (y - 1) 1 dy := by
  intro d
  have hl := line_data hd d
  have hd' := hs d
  have hdc := d.isLt
  simp only [Int.zero_add, Int.mul_one]
  rw [cell_from_stone d rfl (by omega) (by omega) (by omega) (by omega)]
  have he : (y - 1 + (d : Int) * dy).toNat = (y + (d : Int) * dy).toNat - 1 := by omega
  rw [he]; exact hd'.2

theorem descending_index (y : Nat) (d : Fin 4) :
    ((y : Int) + (d : Int) * (-1)).toNat = y - d.val := by omega

theorem no_white_support13 {h : Nat} {b : Board 4} (hs : Support13 b)
    (fb0 : stone (b 0) 0 = some .black) (fb01 : stone (b 0) 1 = some .black)
    (gd : LineGuard b 3) (gu : LineGuard b 4) (hnb : ¬ HasFour h b .black) :
    ¬ HasFour h b .white := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · have ht2 : cellAtInt h b x (y + 2) = some .white := by simpa using hd 2
    have ht3 : cellAtInt h b x (y + 3) = some .white := by simpa using hd 3
    have ht0 : cellAtInt h b x y = some .white := by simpa using hd 0
    obtain ⟨_, _, hy, _, _⟩ := cellAtInt_some ht0
    obtain ⟨c2, hx2, hy2, _, hc2⟩ := cellAtInt_some ht2
    obtain ⟨c3, hx3, hy3, _, hc3⟩ := cellAtInt_some ht3
    have he : c3 = c2 := Fin.ext (by omega)
    rw [he] at hc3
    rcases hs c2 _ hc3 (by omega) with hb | ⟨hi, _⟩
    · have hi : (y + 3).toNat - 1 = (y + 2).toNat := by omega
      rw [hi, hc2] at hb; cases hb
    · omega
  · have hl0 := line_data hd 0
    simp only [Int.mul_zero, Int.add_zero] at hl0
    by_cases hy0 : y = 0
    · subst y; have ht : stone (b 0) 0 = some .white := hl0.2.2
      rw [fb0] at ht; cases ht
    by_cases hy1 : y = 1
    · subst y; have ht : stone (b 0) 1 = some .white := hl0.2.2
      rw [fb01] at ht; cases ht
    apply hnb
    right; left
    refine ⟨0, y - 1, line_shift_black hd ?_⟩
    intro d
    have hl := line_data hd d
    simp only [Int.mul_zero, Int.add_zero] at hl ⊢
    refine ⟨by omega, ?_⟩
    rcases hs d _ hl.2.2 (by omega) with hb | ⟨hi, _⟩
    · exact hb
    · omega
  · have hl0 := line_data hd 0
    norm_num at hl0
    by_cases hy0 : y = 0
    · subst y; have ht : stone (b 0) 0 = some .white := hl0.2.2
      rw [fb0] at ht; cases ht
    apply hnb
    right; right; left
    refine ⟨0, y - 1, line_shift_black hd ?_⟩
    intro d
    have hl := line_data hd d
    have hd0 : 0 ≤ (d : Int) := by omega
    refine ⟨by omega, ?_⟩
    rcases hs d _ hl.2.2 (by omega) with hb | ⟨hi, he | he⟩
    · exact hb
    · subst d; norm_num at hi; omega
    · subst d; norm_num at hi; omega
  · have hl3 := line_data hd 3
    norm_num at hl3
    by_cases hy3 : y = 3
    · obtain ⟨d, hn⟩ := gd
      have hl := (line_data hd d).2.2
      rw [hy3] at hl
      have hi : (3 + (d : Int) * (-1)).toNat = 3 - d.val := by omega
      rw [hi] at hl
      exact hn hl
    by_cases hy4 : y = 4
    · obtain ⟨d, hn⟩ := gu
      have hl := (line_data hd d).2.2
      rw [hy4] at hl
      have hi : (4 + (d : Int) * (-1)).toNat = 4 - d.val := by omega
      rw [hi] at hl
      exact hn hl
    apply hnb
    right; right; right
    refine ⟨0, y - 1, line_shift_black hd ?_⟩
    intro d
    have hl := line_data hd d
    have hd4 := d.isLt
    refine ⟨by omega, ?_⟩
    rcases hs d _ hl.2.2 (by omega) with hb | ⟨hi, _⟩
    · exact hb
    · omega

theorem support13_white {b : Board 4} {c : Fin 4} (hs : Support13 b) (ht : Top13 b c) :
    Support13 (play b c .white) := by
  intro d i hw hi
  by_cases hd : d = c
  · subst d
    rw [play_eq] at hw
    have hb := stone_bound _ _ _ hw
    simp only [List.length_append, List.length_singleton] at hb
    by_cases hlt : i < (b c).length
    · have hold : stone (b c) i = some .white := by simpa [stone_append, hlt] using hw
      rcases hs c i hold hi with hbelow | he
      · left; exact old_stone_preserved hbelow
      · exact Or.inr he
    · have he : i = (b c).length := by omega
      rcases ht with htop | ⟨hc, hlist⟩
      · rcases htop with hempty | hblack
        · omega
        · left
          have hs' : stone (b c) (i - 1) = some .black := by simpa only [he] using hblack
          exact old_stone_preserved hs'
      · have hi1 : i = 1 := by rw [hlist] at he; simpa using he
        exact Or.inr ⟨hi1, hc⟩
  · rw [play_ne b c d .white hd] at hw ⊢
    exact hs d i hw hi

theorem support13_black {b : Board 4} {c : Fin 4} (hs : Support13 b) :
    Support13 (play b c .black) := by
  intro d i hw hi
  have hold : stone (b d) i = some .white := by
    by_cases hd : d = c
    · subst d; rw [play_eq] at hw; exact stone_append_other (by decide) hw
    · simpa only [play_ne b c d .black hd] using hw
  rcases hs d i hold hi with hb | he
  · exact Or.inl (old_stone_preserved hb)
  · exact Or.inr he

structure Core13 (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup : Support13 b
  htop : ∀ d, Legal h b d → Top13 b d
  fb0 : stone (b 0) 0 = some .black
  fb01 : stone (b 0) 1 = some .black
  hnw : ¬ HasFour h b .white

structure OpenCore13 (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup : Support13 b
  htop : ∀ d, d ≠ c → Legal h b d → Top13 b d
  fb0 : stone (b 0) 0 = some .black
  fb01 : stone (b 0) 1 = some .black
  hnw : ¬ HasFour h b .white

theorem core13_white {h : Nat} {b : Board 4} {c : Fin 4} (hp : Core13 h b)
    (hc : Legal h b c) (hnb : ¬ HasFour h b .black)
    (gd : LineGuard (play b c .white) 3) (gu : LineGuard (play b c .white) 4) :
    OpenCore13 h (play b c .white) c := by
  have hs := support13_white hp.hsup (hp.htop c hc)
  have hb0 := old_stone_preserved (c := c) (p := Player.white) hp.fb0
  have hb01 := old_stone_preserved (c := c) (p := Player.white) hp.fb01
  refine ⟨play_valid hp.hv hc, ?_, hs, ?_, hb0, hb01,
    no_white_support13 hs hb0 hb01 gd gu (hasFour_play_other (by decide) hnb)⟩
  · rw [toMove_play', hp.htm]; rfl
  · intro d hd hl
    have hlegal : Legal h b d := by simpa only [Legal, play_ne b c d .white hd] using hl
    have ht := hp.htop d hlegal
    simpa only [Top13, play_ne b c d .white hd] using ht

theorem core13_black {h : Nat} {b : Board 4} {c e : Fin 4} (hw : OpenCore13 h b c)
    (he : Legal h b e) (hce : e = c ∨ ¬ Legal h b c) : Core13 h (play b e .black) := by
  refine ⟨play_valid hw.hv he, ?_, support13_black hw.hsup, ?_, old_stone_preserved hw.fb0,
    old_stone_preserved hw.fb01, hasFour_play_other (by decide) hw.hnw⟩
  · rw [toMove_play', hw.htm]; rfl
  · intro d hl
    by_cases hd : d = e
    · subst d; left; rw [play_eq]; exact topBlack_append_black _
    · have hl0 : Legal h b d := by simpa only [Legal, play_ne b e d .black hd] using hl
      have hdc : d ≠ c := by
        intro hdc
        rcases hce with hec | hnc
        · exact hd (hdc.trans hec.symm)
        · exact hnc (by simpa only [hdc] using hl0)
      have ht := hw.htop d hdc hl0
      simpa only [Top13, play_ne b e d .black hd] using ht

#print axioms core13_white
theorem reserve13_safe (h : Nat) (hh : h % 2 = 0) (r : Fin 4) (t : Nat)
    (ht : t % 2 = 0) (htop : t < h) (extra : Board 4 → Prop)
    (extra_move : ∀ b c p, extra b → extra (play b c p))
    (guard : ∀ b c, Core13 h b → Legal h b c → extra b → (b r).length ≤ t →
      stone (play b c .white r) t ≠ some .white →
      LineGuard (play b c .white) 3 ∧ LineGuard (play b c .white) 4)
    (finish : ∀ b, Core13 h b → extra b → stone (b r) t = some .black → CanAvoidLoss h .black b)
    {b : Board 4} (hp : Core13 h b) (hx : extra b)
    (hr : (b r).length % 2 = 1) (hn : stone (b r) t ≠ some .white) :
    CanAvoidLoss h .black b := by
  have induction_step : ∀ k b, Core13 h b → extra b → (b r).length % 2 = 1 →
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
          have hw := core13_white hp hc hbf (guard b c hp hc hx hlen hn').1 (guard b c hp hc hx hlen hn').2
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
                  apply ih k (by omega) _ (core13_black hw hcov (Or.inl rfl))
                    (extra_move _ r .black hx') _ (not_white_black hn')
                  simp only [play_eq, List.length_append, List.length_singleton]
                  omega
                · have hfull : h ≤ (play b r .white r).length := by
                    unfold Legal at hcov; omega
                  obtain ⟨e, he⟩ := exists_legal hw.hv hf
                  refine ⟨e, he, ?_⟩
                  have hc0 := core13_black hw he (Or.inr hcov)
                  have hx0 := extra_move _ e .black hx'
                  have hl : t < (play b r .white r).length := by
                    omega
                  exact finish _ hc0 hx0 (old_stone_preserved (occupied_not_white hl hn')) k
              · have hr' : (play b c .white r).length % 2 = 1 := by
                  simpa only [play_ne b c r .white (Ne.symm hcr)] using hr
                by_cases hcov : Legal h (play b c .white) c
                · refine ⟨c, hcov, ?_⟩
                  apply ih k (by omega) _ (core13_black hw hcov (Or.inl rfl))
                    (extra_move _ c .black hx') _ (not_white_black hn')
                  simpa only [play_ne _ c r .black (Ne.symm hcr)] using hr'
                · obtain ⟨e, her, he⟩ := reserve_reply_exists r hw.hv hh hw.htm hr'
                  refine ⟨e, he, ?_⟩
                  apply ih k (by omega) _ (core13_black hw he (Or.inr hcov))
                    (extra_move _ e .black hx') _ (not_white_black hn')
                  simpa only [play_ne _ e r .black (Ne.symm her)] using hr'
  exact fun k => induction_step k b hp hx hr hn

theorem permanent13_pairing (h k : Nat) :
    (∀ b, Core13 h b → FixedLine h b 3 → FixedLine h b 4 → SafeFor h .black k b) ∧
    (∀ b c, OpenCore13 h b c → FixedLine h b 3 → FixedLine h b 4 → SafeFor h .black k b) := by
  induction k with
  | zero => exact ⟨fun _ hp _ _ => hp.hnw, fun _ _ hw _ _ => hw.hnw⟩
  | succ k ih =>
    constructor
    · intro b hp hd hu
      refine ⟨hp.hnw, ?_⟩
      by_cases hb : HasFour h b .black
      · exact Or.inl hb
      · right; right
        rw [if_neg (by rw [hp.htm]; decide), hp.htm]
        intro c hc
        have hd' := fixed_line_move (c := c) (p := Player.white) hd
        have hu' := fixed_line_move (c := c) (p := Player.white) hu
        have hv := play_valid hp.hv (p := Player.white) hc
        exact ih.2 _ c (core13_white hp hc hb (fixed_line_guard hv hd') (fixed_line_guard hv hu')) hd' hu'
    · intro b c hw hd hu
      refine ⟨hw.hnw, ?_⟩
      by_cases hf : BoardFull h b
      · exact Or.inr (Or.inl hf)
      · right; right
        rw [if_pos hw.htm, hw.htm]
        by_cases hc : Legal h b c
        · exact ⟨c, hc, ih.1 _ (core13_black hw hc (Or.inl rfl)) (fixed_line_move hd) (fixed_line_move hu)⟩
        · obtain ⟨e, he⟩ := exists_legal hw.hv hf
          exact ⟨e, he, ih.1 _ (core13_black hw he (Or.inr hc)) (fixed_line_move hd) (fixed_line_move hu)⟩

theorem permanent13_safe {h : Nat} {b : Board 4} (hp : Core13 h b)
    (hd : FixedLine h b 3) (hu : FixedLine h b 4) : CanAvoidLoss h .black b :=
  fun k => (permanent13_pairing h k).1 b hp hd hu

theorem permanent13_open_safe {h : Nat} {b : Board 4} {c : Fin 4} (hp : OpenCore13 h b c)
    (hd : FixedLine h b 3) (hu : FixedLine h b 4) : CanAvoidLoss h .black b :=
  fun k => (permanent13_pairing h k).2 b c hp hd hu

theorem reserve13_D {h : Nat} (hh : h % 2 = 0) (h3 : 3 ≤ h) {b : Board 4}
    (hp : Core13 h b) (hu : FixedLine h b 4)
    (hr : (b 1).length % 2 = 1) (hn : stone (b 1) 2 ≠ some .white) : CanAvoidLoss h .black b := by
  apply reserve13_safe h hh 1 2 (by decide) (by omega) (fun b => FixedLine h b 4)
    (fun _ _ _ hf => fixed_line_move hf) _ _ hp hu hr hn
  · intro b c hp hc hu _ hn'
    exact ⟨⟨1, hn'⟩, fixed_line_guard (play_valid hp.hv hc) (fixed_line_move hu)⟩
  · intro b hp hu hb
    exact permanent13_safe hp ⟨1, Or.inl hb⟩ hu

theorem reserve13_U {h : Nat} (hh : h % 2 = 0) (h3 : 3 ≤ h) {b : Board 4}
    (hp : Core13 h b) (hd : FixedLine h b 3)
    (hr : (b 2).length % 2 = 1) (hn : stone (b 2) 2 ≠ some .white) : CanAvoidLoss h .black b := by
  apply reserve13_safe h hh 2 2 (by decide) (by omega) (fun b => FixedLine h b 3)
    (fun _ _ _ hf => fixed_line_move hf) _ _ hp hd hr hn
  · intro b c hp hc hd _ hn'
    exact ⟨fixed_line_guard (play_valid hp.hv hc) (fixed_line_move hd), ⟨2, hn'⟩⟩
  · intro b hp hd hb
    exact permanent13_safe hp hd ⟨2, Or.inl hb⟩

theorem black_rising_four {h : Nat} {b : Board 4} (h5 : 5 ≤ h)
    (h0 : stone (b 0) 1 = some .black) (h1 : stone (b 1) 2 = some .black)
    (h2 : stone (b 2) 3 = some .black) (h3 : stone (b 3) 4 = some .black) :
    HasFour h b .black := by
  have hh1 : (1 : Int) < h := by omega
  have hh2 : (2 : Int) < h := by omega
  have hh3 : (3 : Int) < h := by omega
  have hh4 : (4 : Int) < h := by omega
  right; right; left
  refine ⟨0, 1, ?_⟩
  intro i
  fin_cases i <;> simp [cellAtInt, hh1, hh2, hh3, hh4, h0, h1, h2, h3]

theorem reserve13_win {h : Nat} (hh : h % 2 = 0) (h5 : 5 ≤ h) {b : Board 4}
    (hp : Core13 h b) (hd : FixedLine h b 3)
    (hr : (b 1).length % 2 = 1) (hn : stone (b 1) 2 ≠ some .white)
    (hb2 : stone (b 2) 3 = some .black) (hb3 : stone (b 3) 4 = some .black) :
    CanAvoidLoss h .black b := by
  apply reserve13_safe h hh 1 2 (by decide) (by omega)
    (fun b => FixedLine h b 3 ∧ stone (b 2) 3 = some .black ∧ stone (b 3) 4 = some .black)
    _ _ _ hp ⟨hd, hb2, hb3⟩ hr hn
  · intro b c p hx
    exact ⟨fixed_line_move hx.1, old_stone_preserved hx.2.1, old_stone_preserved hx.2.2⟩
  · intro b c hp hc hx hl _
    refine ⟨fixed_line_guard (play_valid hp.hv hc) (fixed_line_move hx.1), 1, ?_⟩
    have hs : stone (play b c .white 1) 3 = none := by
      apply stone_none
      by_cases he : c = (1 : Fin 4)
      · subst c; rw [play_eq]; simp only [List.length_append, List.length_singleton]; omega
      · rw [play_ne _ c 1 .white (Ne.symm he)]; omega
    change stone (play b c .white 1) 3 ≠ some .white
    rw [hs]; simp
  · intro b hp hx ht
    exact black_won_safe hp.hnw (black_rising_four h5 hp.fb01 ht hx.2.1 hx.2.2)

#print axioms reserve13_D
#print axioms reserve13_U
#print axioms reserve13_win
end Connect4.FourColumns
