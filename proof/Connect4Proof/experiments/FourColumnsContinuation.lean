import experiments.FourColumns
import Mathlib.Tactic.FinCases

/-!
Permanent defense for the exceptional cell (column 0, row 2).
Coordinates in this file are zero based. A locked cell is either occupied by
Black, outside the board, or in a full column and not White. In particular,
being merely empty now does NOT make a cell permanently safe.
-/
namespace Connect4.FourColumns

/-- A cell which no future legal move can turn white. -/
def Locked (h : Nat) (b : Board 4) (d : Fin 4) (i : Nat) : Prop :=
  stone (b d) i = some .black ∨
  (¬ Legal h b d ∧ stone (b d) i ≠ some .white) ∨ h ≤ i

theorem locked_not_white {h : Nat} {b : Board 4} {d : Fin 4} {i : Nat}
    (hv : Valid h b) (hl : Locked h b d i) : stone (b d) i ≠ some .white := by
  rcases hl with hb | ⟨_, hn⟩ | hi
  · rw [hb]; decide
  · exact hn
  · rw [stone_none _ _ (le_trans (hv d) hi)]; simp

theorem locked_play {h : Nat} {b : Board 4} {d c : Fin 4} {i : Nat} {p : Player}
    (hl : Locked h b d i) (hc : Legal h b c) : Locked h (play b c p) d i := by
  rcases hl with hb | ⟨hn, hw⟩ | hi
  · left
    rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hb)]
    exact hb
  · have hdc : d ≠ c := fun e => hn (e.symm ▸ hc)
    right; left
    simpa only [Legal, play_ne b c d p hdc] using And.intro hn hw
  · exact Or.inr (Or.inr hi)

/-- The support invariant retains the identity of the exceptional column. -/
def Support0 (b : Board 4) : Prop :=
  ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (d = 0 ∧ i = 2)

theorem support0_black {b : Board 4} {c : Fin 4} (hs : Support0 b) :
    Support0 (play b c .black) := by
  intro d i hw hi
  have hold : stone (b d) i = some .white := by
    by_cases hd : d = c
    · subst d
      rw [play_eq] at hw
      exact stone_append_other (by decide) hw
    · simpa only [play_ne b c d .black hd] using hw
  rcases hs d i hold hi with hb | he
  · left
    rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hb)]
    exact hb
  · exact Or.inr he

structure PD0B (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup : Support0 b
  h0pat : Legal h b 0 → TopBlack (b 0) ∨ b 0 = [.black, .white]
  htop : ∀ d, d ≠ 0 → Legal h b d → TopBlack (b d)
  fb0 : stone (b 0) 0 = some .black
  fb30 : stone (b 3) 0 = some .black
  horizontal : Locked h b 3 2
  diagonal : Locked h b 1 3 ∨ Locked h b 2 4
  hnw : ¬ HasFour h b .white

structure W0B (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup : Support0 b
  h0pat : c ≠ 0 → Legal h b 0 → TopBlack (b 0) ∨ b 0 = [.black, .white]
  htop : ∀ d, d ≠ c → d ≠ 0 → Legal h b d → TopBlack (b d)
  fb0 : stone (b 0) 0 = some .black
  fb30 : stone (b 3) 0 = some .black
  horizontal : Locked h b 3 2
  diagonal : Locked h b 1 3 ∨ Locked h b 2 4
  hnw : ¬ HasFour h b .white

theorem pd0b_to_w0b {h : Nat} {b : Board 4} {c : Fin 4}
    (hp : PD0B h b) (hc : Legal h b c) (hnb : ¬ HasFour h b .black) :
    W0B h (play b c .white) c := by
  have hc0 : c = (0 : Fin 4) → TopBlack (b 0) ∨ b 0 = [.black, .white] := by
    intro he; apply hp.h0pat; simpa only [he] using hc
  have hct : c ≠ (0 : Fin 4) → TopBlack (b c) := fun he => hp.htop c he hc
  have hv := play_valid hp.hv (p := Player.white) hc
  have hd : Locked h (play b c .white) 1 3 ∨ Locked h (play b c .white) 2 4 :=
    hp.diagonal.elim (fun h => Or.inl (locked_play h hc))
      (fun h => Or.inr (locked_play h hc))
  have hh := locked_play hp.horizontal (p := Player.white) hc
  refine ⟨hv, ?_, hsup0_play hp.hsup hc0 hct, ?_, ?_, ?_, ?_, hh, hd, ?_⟩
  · rw [toMove_play', hp.htm]; rfl
  · intro hn hl
    have hn' : (0 : Fin 4) ≠ c := Ne.symm hn
    rw [play_ne b c 0 .white hn']
    apply hp.h0pat
    simpa only [Legal, play_ne b c 0 .white hn'] using hl
  · intro d hdc hd0 hl
    rw [play_ne b c d .white hdc]
    apply hp.htop d hd0
    simpa only [Legal, play_ne b c d .white hdc] using hl
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hp.fb0)]; exact hp.fb0
  · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hp.fb30)]; exact hp.fb30
  · apply noWhiteFour_descent0 hp.hsup hc0 hct hp.fb0 hp.fb30
    · exact hd.elim (fun h => Or.inl (locked_not_white hv h))
        (fun h => Or.inr (locked_not_white hv h))
    · exact locked_not_white hv hh
    · exact hp.hnw
    · exact hnb

theorem w0b_reply {h : Nat} {b : Board 4} {c e : Fin 4}
    (hw : W0B h b c) (he : Legal h b e) (hce : e = c ∨ ¬ Legal h b c) :
    PD0B h (play b e .black) := by
  refine ⟨play_valid hw.hv he, ?_, support0_black hw.hsup, ?_, ?_, ?_, ?_,
    locked_play hw.horizontal he, ?_, hasFour_play_other (by decide) hw.hnw⟩
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
  · exact hw.diagonal.elim (fun h => Or.inl (locked_play h he))
      (fun h => Or.inr (locked_play h he))

theorem pd0b_pairing_aux (h k : Nat) :
    (∀ b, PD0B h b → SafeFor h .black k b) ∧
    (∀ b c, W0B h b c → SafeFor h .black k b) := by
  induction k with
  | zero => exact ⟨fun _ hp => hp.hnw, fun _ _ hw => hw.hnw⟩
  | succ k ih =>
    constructor
    · intro b hp
      refine ⟨hp.hnw, ?_⟩
      by_cases hb : HasFour h b .black
      · exact Or.inl hb
      · right; right
        rw [if_neg (by rw [hp.htm]; decide), hp.htm]
        exact fun c hc => ih.2 _ c (pd0b_to_w0b hp hc hb)
    · intro b c hw
      refine ⟨hw.hnw, ?_⟩
      by_cases hf : BoardFull h b
      · exact Or.inr (Or.inl hf)
      · right; right
        rw [if_pos hw.htm, hw.htm]
        by_cases hc : Legal h b c
        · exact ⟨c, hc, ih.1 _ (w0b_reply hw hc (Or.inl rfl))⟩
        · obtain ⟨e, he⟩ := exists_legal hw.hv hf
          exact ⟨e, he, ih.1 _ (w0b_reply hw he (Or.inr hc))⟩

theorem pd0b_safe {h : Nat} {b : Board 4} (hp : PD0B h b) :
    CanAvoidLoss h .black b := fun k => (pd0b_pairing_aux h k).1 b hp

theorem w0b_safe {h : Nat} {b : Board 4} {c : Fin 4} (hw : W0B h b c) :
    CanAvoidLoss h .black b := fun k => (pd0b_pairing_aux h k).2 b c hw

/-- Waiting-phase exit once both exceptional lines have permanent protection. -/
theorem w0a_permanent {h : Nat} {b : Board 4} {c : Fin 4} (hw : W0A h b c)
    (hh : Locked h b 3 2) (hd : Locked h b 1 3 ∨ Locked h b 2 4) :
    CanAvoidLoss h .black b := by
  apply w0b_safe (c := c)
  refine ⟨hw.hv, hw.htm, hw.hsup0, ?_, ?_, hw.fb0, hw.fb30, hh, hd, hw.hnw⟩
  · intro hc _
    rcases hw.h0tf with ht | hb | he
    · exact Or.inl ht
    · exact Or.inr hb
    · exact False.elim (hc he)
  · intro d hdc hd0 hl
    exact hw.htopO d hdc hl hd0

#print axioms pd0b_safe
#print axioms w0a_permanent

theorem occupied_not_white {l : List Player} {i : Nat}
    (hi : i < l.length) (hn : stone l i ≠ some .white) : stone l i = some .black := by
  cases hs : stone l i with
  | none => have := stone_none_inv l i hs; omega
  | some p => cases p with
    | black => rfl
    | white => exact False.elim (hn hs)

/-- The completed fourth column permanently protects the exceptional horizontal.
    For H ≤ 4 the remaining diagonal is out of bounds; otherwise a sufficiently
    tall second column supplies its permanent black blocker. -/
theorem w0a_endgame_blocked {h : Nat} {b : Board 4} (hw : W0A h b 3)
    (hf : ¬ Legal h b 3) (hb : h ≤ 4 ∨ 3 < (b 1).length) :
    CanAvoidLoss h .black b := by
  apply w0a_permanent hw (Or.inr (Or.inl ⟨hf, hw.fb32⟩))
  rcases hb with hh | hl
  · exact Or.inr (Or.inr (Or.inr hh))
  · exact Or.inl (Or.inl (occupied_not_white hl hw.fb13))

/-- If column 0 is still BW, occupying its next cell eliminates the exception
    altogether and enters the already completed support-descent strategy. -/
theorem w0a_clear_exception {h : Nat} {b : Board 4} (hw : W0A h b 3)
    (hf : ¬ Legal h b 3) (hb : b 0 = [.black, .white]) (hh : 3 ≤ h) :
    CanAvoidLoss h .black b := by
  have he : Legal h b 0 := by simp [Legal, hb]; omega
  have hp : PDstate h (play b 0 .black) := by
    refine ⟨play_valid hw.hv he, ?_, ?_, ?_, ?_, ?_, hasFour_play_other (by decide) hw.hnw⟩
    · rw [toMove_play', hw.htm]; rfl
    · intro d i hs hi
      have hs' : stone (b d) i = some .white := by
        by_cases hd : d = 0
        · subst d
          rw [play_eq] at hs
          exact stone_append_other (by decide) hs
        · simpa only [play_ne b 0 d .black hd] using hs
      rcases hw.hsup0 d i hs' hi with hbelow | ⟨hd, hi2⟩
      · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hbelow)]
        exact hbelow
      · subst d; subst i
        simp [hb, stone] at hs'
    · intro d hd
      by_cases hd0 : d = 0
      · subst d; rw [play_eq]; exact topBlack_append_black _
      · rw [play_ne b 0 d .black hd0]
        have hl : Legal h b d := by simpa only [Legal, play_ne b 0 d .black hd0] using hd
        apply hw.htopO d _ hl hd0
        intro hd3
        exact hf (by simpa only [hd3] using hl)
    · rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hw.fb0)]; exact hw.fb0
    · right; right; right
      rw [stone_old_play _ _ _ _ _ (stone_bound _ _ _ hw.fb30)]; exact hw.fb30
  intro k
  cases k with
  | zero => exact hw.hnw
  | succ k =>
    refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
    rw [if_pos hw.htm, hw.htm]
    exact ⟨0, he, pd_state_safe hp k⟩

/-- Fixed-player winning semantics with both terminal guards. -/
def WinFor (h : Nat) (p : Player) : Nat → Board w → Prop
  | 0, b => HasFour h b p ∧ ¬ HasFour h b (opponent p)
  | k + 1, b =>
      ¬ HasFour h b (opponent p) ∧
      (HasFour h b p ∨
        (¬ BoardFull h b ∧
          (if toMove b = p then
            ∃ c, Legal h b c ∧ WinFor h p k (play b c (toMove b))
          else
            ∀ c, Legal h b c → WinFor h p k (play b c (toMove b)))))

theorem safe_excludes_opponent_win {h k : Nat} {p : Player} {b : Board w}
    (hs : SafeFor h p k b) : ¬ WinFor h (opponent p) k b := by
  induction k generalizing b with
  | zero => exact fun hw => hs hw.1
  | succ k ih =>
    intro hw
    rcases hw.2 with hwin | ⟨hnf, hwmove⟩
    · exact hs.1 hwin
    · rcases hs.2 with hwin | hfull | hsmove
      · exact hw.1 (by simpa only [opponent_involutive] using hwin)
      · exact hnf hfull
      · by_cases ht : toMove b = p
        · have hto : toMove b ≠ opponent p := by rw [ht]; exact player_ne_opponent p
          rw [if_pos ht] at hsmove
          rw [if_neg hto] at hwmove
          obtain ⟨c, hc, hchild⟩ := hsmove
          exact ih hchild (hwmove c hc)
        · have hto : toMove b = opponent p := eq_opponent_of_ne _ _ ht
          rw [if_neg ht] at hsmove
          rw [if_pos hto] at hwmove
          obtain ⟨c, hc, hchild⟩ := hwmove
          exact ih (hsmove c hc) hchild

theorem draw_excludes_forced_wins {h : Nat} {b : Board w} (hd : IsDraw h b) :
    (¬ ∃ k, WinFor h .black k b) ∧ (¬ ∃ k, WinFor h .white k b) := by
  constructor
  · rintro ⟨k, hk⟩; exact safe_excludes_opponent_win (hd.2 k) hk
  · rintro ⟨k, hk⟩; exact safe_excludes_opponent_win (hd.1 k) hk

#print axioms w0a_endgame_blocked
#print axioms w0a_clear_exception
#print axioms draw_excludes_forced_wins

/-- Exact reachable entry for B1,W1,B4 (paper numbering). -/
def opening0 : Board 4 := play (play (play (emptyBoard 4) 0 .black) 0 .white) 3 .black

theorem opening0_state {h : Nat} (h2 : 2 ≤ h) : PD0A h opening0 := by
  have ht : totalStones opening0 = 3 := by
    simp [opening0, totalStones_play', totalStones_empty]
  refine ⟨?_, ?_, ?_, Or.inr rfl, ?_, rfl, rfl, by decide,
    by decide, by decide, by decide, Or.inl (by decide), by decide, ?_⟩
  · intro d
    fin_cases d <;> simp [opening0, play, emptyBoard] <;> omega
  · simp [toMove, ht]
  · intro d i hs hi
    have hb := stone_bound (opening0 d) i .white hs
    fin_cases d <;> simp [opening0, play, emptyBoard] at hb
    · have he : i = 1 := by omega
      subst i; exact Or.inl rfl
    all_goals omega
  · intro d hd _
    fin_cases d
    · exact False.elim (hd rfl)
    all_goals unfold TopBlack; decide
  · intro hf
    have := hasFour_minStones hf
    rw [ht] at this
    omega

theorem w0a_only_fourth_can_fill {h : Nat} {b : Board 4} {c : Fin 4}
    (hh : h % 2 = 0) (hw : W0A h b c) (hf : ¬ Legal h b c) : c = 3 := by
  have hl : (b c).length = h := by have := hw.hv c; unfold Legal at hf; omega
  fin_cases c
  · have ho := hw.hc0o rfl
    change (b 0).length % 2 = 1 at ho
    change (b 0).length = h at hl
    omega
  · have ho := hw.hc1o rfl
    change (b 1).length % 2 = 1 at ho
    change (b 1).length = h at hl
    omega
  · have ho := hw.hc2o rfl
    change (b 2).length % 2 = 1 at ho
    change (b 2).length = h at hl
    omega
  · rfl

/-- Complete waiting/exit cycle for heights 2 and 4. Larger heights use the
    two reserve-column cases implemented in FourColumnsReserve. -/
theorem pd0a_small_pairing (h : Nat) (hh : h % 2 = 0) (h4 : h ≤ 4) (k : Nat) :
    (∀ b, PD0A h b → SafeFor h .black k b) ∧
    (∀ b c, W0A h b c → SafeFor h .black k b) := by
  induction k with
  | zero => exact ⟨fun _ hp => hp.hnw, fun _ _ hw => hw.hnw⟩
  | succ k ih =>
    constructor
    · intro b hp
      refine ⟨hp.hnw, ?_⟩
      by_cases hb : HasFour h b .black
      · exact Or.inl hb
      · right; right
        rw [if_neg (by rw [hp.htm]; decide), hp.htm]
        exact fun c hc => ih.2 _ c (pd0a_to_w0a hp hc hb)
    · intro b c hw
      by_cases hc : Legal h b c
      · refine ⟨hw.hnw, Or.inr (Or.inr ?_)⟩
        rw [if_pos hw.htm, hw.htm]
        exact ⟨c, hc, ih.1 _ (w0a_reply hw hc)⟩
      · have he := w0a_only_fourth_can_fill hh hw hc
        subst c
        exact w0a_endgame_blocked hw hc (Or.inl h4) (k + 1)

theorem opening0_small_safe {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) (h4 : h ≤ 4) :
    CanAvoidLoss h .black opening0 :=
  fun k => (pd0a_small_pairing h hh h4 k).1 _ (opening0_state h2)

theorem full_without_win_not_win {h : Nat} {b : Board w} {p : Player}
    (hf : BoardFull h b) (hn : ¬ HasFour h b p) (k : Nat) : ¬ WinFor h p k b := by
  cases k with
  | zero => exact fun hw => hn hw.1
  | succ k => exact fun hw => hw.2.elim hn (fun hc => hc.1 hf)

#print axioms opening0_small_safe

/-- Paper Lemma 2.3, the capacity argument after White moves outside a reserve.
    An odd reserve and an even total leave an odd number of occupied outside
    cells, so the three even-capacity outside columns cannot all be full. -/
theorem reserve_reply_exists {h : Nat} {b : Board 4} (r : Fin 4)
    (hv : Valid h b) (hh : h % 2 = 0) (ht : toMove b = .black)
    (hr : (b r).length % 2 = 1) : ∃ e, e ≠ r ∧ Legal h b e := by
  classical
  by_contra hn
  have full : ∀ d, d ≠ r → (b d).length = h := by
    intro d hd
    have hnl : ¬ Legal h b d := fun hl => hn ⟨d, hd, hl⟩
    have hb := hv d
    unfold Legal at hnl
    omega
  have hext : (∑ d ∈ Finset.univ.erase r, (b d).length) = 3 * h := by
    calc
      _ = ∑ _d ∈ (Finset.univ.erase r), h := by
        apply Finset.sum_congr rfl
        intro d hd
        exact full d (Finset.mem_erase.mp hd).1
      _ = 3 * h := by simp
  have hs : totalStones b = 3 * h + (b r).length := by
    unfold totalStones
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r), hext]
  have hp : totalStones b % 2 = 0 := by
    by_contra he
    simp [toMove, he] at ht
  rw [hs] at hp
  omega

#print axioms reserve_reply_exists

end Connect4.FourColumns
