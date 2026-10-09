import experiments.FourColumnsOddFinite

namespace Connect4.FourColumns

/-- Column lengths and the virtual top token at an opponent-turn boundary. -/
def LiftLengths (h : Nat) (p : Player) (a v : Board 4) : Prop :=
  ∀ c, (v c).length ≤ (a c).length ∧
    ((v c).length < 6 → (a c).length = (v c).length) ∧
    ((v c).length = 6 → (a c).length % 2 = 0) ∧
    ((v c).length = 7 →
      (stone (v c) 6 = some p ∧ (a c).length % 2 = 1) ∨
      (stone (v c) 6 = some (opponent p) ∧ (a c).length = h))

structure LiftRel (h : Nat) (p : Player) (a v : Board 4) : Prop where
  low : LowEq a v
  lengths : LiftLengths h p a v

theorem lift_play {h : Nat} {p q : Player} {a v : Board 4} {c : Fin 4}
    (hr : LiftRel h p a v) (hc : Legal 7 v c)
    (hs : (v c).length = 6 → q = p ∨ (a c).length + 1 = h) :
    LiftRel h p (play a c q) (play v c q) := by
  have hv : (v c).length < 7 := hc
  have hl := hr.lengths c
  constructor
  · apply lowEq_play hr.low
    by_cases hsmall : (v c).length < 6
    · exact Or.inl (hl.2.1 hsmall)
    · exact Or.inr ⟨by omega, by omega⟩
  · intro d
    by_cases hd : d = c
    · subst d
      simp only [play_eq, List.length_append, List.length_singleton]
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro hsmall
        have := hl.2.1 (by omega)
        omega
      · intro h6
        have := hl.2.1 (by omega)
        omega
      · intro h7
        have he : (v c).length = 6 := by omega
        by_cases hqp : q = p
        · subst q
          left
          constructor
          · simp [stone_append, he]
          · have := hl.2.2.1 he
            omega
        · right
          constructor
          · have hpq : q = opponent p := eq_opponent_of_ne q p hqp
            simp [stone_append, he, hpq]
          · exact (hs he).resolve_left hqp
    · simpa only [play_ne a c d q hd, play_ne v c d q hd] using hr.lengths d

theorem lift_pair {h : Nat} {p : Player} {a v : Board 4} {c : Fin 4}
    (hr : LiftRel h p a v) (hc : Legal h a c) (hv : 6 ≤ (v c).length) :
    LiftRel h p (play (play a c (opponent p)) c p) v := by
  have hl := hr.lengths c
  have ha : 6 ≤ (a c).length := by omega
  constructor
  · have h1 : LowEq (play a c (opponent p)) a := lowEq_high_play ha
    have h2 : LowEq (play (play a c (opponent p)) c p) (play a c (opponent p)) :=
      lowEq_high_play (by simp only [play_eq, List.length_append, List.length_singleton]; omega)
    exact fun d i hi => (h2 d i hi).trans ((h1 d i hi).trans (hr.low d i hi))
  · intro d
    by_cases hd : d = c
    · subst d
      simp only [play_eq, List.length_append, List.length_singleton]
      refine ⟨by omega, ?_, ?_, ?_⟩
      · omega
      · intro h6
        have := hl.2.2.1 h6
        omega
      · intro h7
        rcases hl.2.2.2 h7 with ⟨hs, hp⟩ | ⟨hs, hf⟩
        · exact Or.inl ⟨hs, by omega⟩
        · have hc' : (a c).length < h := hc
          omega
    · simpa only [play_ne _ c d p hd, play_ne _ c d (opponent p) hd] using hr.lengths d

theorem lift_legal {h : Nat} {p : Player} {a v : Board 4} {c : Fin 4}
    (h7 : 7 ≤ h) (hh : h % 2 = 1) (ha : Valid h a) (hr : LiftRel h p a v)
    (hc : Legal 7 v c) : Legal h a c := by
  have hl := hr.lengths c
  have hc' : (v c).length < 7 := hc
  have hb := ha c
  by_cases hs : (v c).length < 6
  · have := hl.2.1 hs
    show (a c).length < h
    omega
  · have := hl.2.2.1 (by omega)
    show (a c).length < h
    omega

theorem lift_buffer_legal {h : Nat} {p : Player} {a v : Board 4} {c : Fin 4}
    (hh : h % 2 = 1) (hv : Valid 7 v) (hr : LiftRel h p a v)
    (hc : Legal h a c) (hi : 6 ≤ (v c).length)
    (hn : ¬ ((v c).length = 6 ∧ (a c).length + 1 = h)) :
    Legal h (play a c (opponent p)) c := by
  have hl := hr.lengths c
  have hc' : (a c).length < h := hc
  have hv' := hv c
  show (play a c (opponent p) c).length < h
  simp only [play_eq, List.length_append, List.length_singleton]
  by_cases he : (v c).length = 6
  · have hne : (a c).length + 1 ≠ h := fun ht => hn ⟨he, ht⟩
    omega
  · have he7 : (v c).length = 7 := by omega
    rcases hl.2.2.2 he7 with ⟨_, ho⟩ | ⟨_, hf⟩ <;> omega

structure OddState (h : Nat) (p : Player) (b : Board 4) : Prop where
  valid : Valid h b
  turn : toMove b = opponent p
  safe : ¬ HasFour h b (opponent p)
  support : HighSupported p b
  top : HighTop h p b

theorem odd_opponent_safe {h : Nat} {p : Player} {b : Board 4} {c : Fin 4}
    (hb : OddState h p b) (hc : Legal h b c) (hn : ¬ HasFour h b p)
    (hl : ¬ HasFour 6 (play b c (opponent p)) (opponent p)) :
    ¬ HasFour h (play b c (opponent p)) (opponent p) :=
  high_supported_no_four (supported_opponent hb.support hb.top hc) hl
    (hasFour_play_other (Ne.symm (player_ne_opponent p)) hn)

theorem odd_reply_state {h : Nat} {p : Player} {b : Board 4} {c d : Fin 4}
    (hb : OddState h p b) (hc : Legal h b c)
    (hn : ¬ HasFour h (play b c (opponent p)) (opponent p))
    (hd : Legal h (play b c (opponent p)) d)
    (hcap : d = c ∨ (play b c (opponent p) c).length ≤ 2 ∨
      ¬ Legal h (play b c (opponent p)) c) :
    OddState h p (play (play b c (opponent p)) d p) :=
  ⟨play_valid (play_valid hb.valid hc) hd,
    by rw [toMove_play', toMove_play', hb.turn, opponent_involutive],
    hasFour_play_other (player_ne_opponent p) hn,
    supported_defender (supported_opponent hb.support hb.top hc) d,
    high_top_reply hb.top hc hd hcap⟩

/-- Pairwise closure implies the existing single-move, race-guarded semantics. -/
theorem pair_region_safe {h : Nat} {p : Player} (R : Board 4 → Prop)
    (state : ∀ b, R b → OddState h p b)
    (step : ∀ b, R b → ¬ HasFour h b p → ∀ c, Legal h b c →
      ¬ HasFour h (play b c (opponent p)) (opponent p) ∧
      (BoardFull h (play b c (opponent p)) ∨
        ∃ d, Legal h (play b c (opponent p)) d ∧
          R (play (play b c (opponent p)) d p)))
    {b : Board 4} (hb : R b) : CanAvoidLoss h p b := by
  intro k
  induction k using Nat.strong_induction_on generalizing b with
  | h k ih =>
    have hs := state b hb
    cases k with
    | zero => exact hs.safe
    | succ k =>
      by_cases hw : HasFour h b p
      · exact safeFor_terminal' hs.safe (Or.inl hw) (k+1)
      · refine ⟨hs.safe, Or.inr (Or.inr ?_)⟩
        rw [if_neg (by rw [hs.turn]; exact Ne.symm (player_ne_opponent p)), hs.turn]
        intro c hc
        obtain ⟨hn, hr⟩ := step b hb hw c hc
        cases k with
        | zero => exact hn
        | succ k =>
          rcases hr with hf | ⟨d, hd, hr⟩
          · exact safeFor_terminal' hn (Or.inr hf) (k+1)
          · refine ⟨hn, Or.inr (Or.inr ?_)⟩
            have ht : toMove (play b c (opponent p)) = p := by
              rw [toMove_play', hs.turn, opponent_involutive]
            rw [if_pos ht, ht]
            exact ⟨d, hd, ih k (by omega) hr⟩

def HighTail (b : Board 4) : Prop := ∀ c, 6 ≤ (b c).length

theorem highTail_play {b : Board 4} (ht : HighTail b) (c : Fin 4) (p : Player) :
    HighTail (play b c p) := by
  intro d
  by_cases hd : d = c
  · subst d
    simp only [play_eq, List.length_append, List.length_singleton]
    have := ht c
    omega
  · simpa only [play_ne b c d p hd] using ht d

theorem tail_round {h : Nat} {p : Player} {b : Board 4}
    (h6 : 6 ≤ h) (hb : OddState h p b) (ht : HighTail b)
    (hw : ¬ HasFour h b p) {c : Fin 4} (hc : Legal h b c) :
    ¬ HasFour h (play b c (opponent p)) (opponent p) ∧
    (BoardFull h (play b c (opponent p)) ∨
      ∃ d, Legal h (play b c (opponent p)) d ∧
        OddState h p (play (play b c (opponent p)) d p) ∧
        HighTail (play (play b c (opponent p)) d p)) := by
  have hn : ¬ HasFour h (play b c (opponent p)) (opponent p) := by
    apply odd_opponent_safe hb hc hw
    intro hf
    exact hb.safe (four_height_mono h6 (lowEq_four (lowEq_high_play (ht c)) hf))
  refine ⟨hn, ?_⟩
  by_cases hf : BoardFull h (play b c (opponent p))
  · exact Or.inl hf
  · right
    have hchoose : ∃ d, Legal h (play b c (opponent p)) d ∧
        (d = c ∨ ¬ Legal h (play b c (opponent p)) c) := by
      by_cases hc' : Legal h (play b c (opponent p)) c
      · exact ⟨c, hc', Or.inl rfl⟩
      · obtain ⟨d, hd⟩ := exists_legal (play_valid hb.valid hc) hf
        exact ⟨d, hd, Or.inr hc'⟩
    obtain ⟨d, hd, hcap⟩ := hchoose
    exact ⟨d, hd, odd_reply_state hb hc hn hd
      (hcap.elim Or.inl (fun h => Or.inr (Or.inr h))),
      highTail_play (highTail_play ht c _) d _⟩

end Connect4.FourColumns
