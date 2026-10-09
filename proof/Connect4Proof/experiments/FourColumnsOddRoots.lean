import experiments.FourColumnsOddSound

namespace Connect4.FourColumns

theorem small_control_safe {h : Nat} {p : Player} {b : Board 4}
    (h7 : 7 ≤ h) (hh : h % 2 = 1)
    (hsmall : ∀ c, (b c).length < 3) (hcount : totalStones b < 4)
    (hturn : toMove b = opponent p) (htree : ControlTree 7 6 p b) :
    CanAvoidLoss h p b := by
  apply odd_control_lift h7 hh (v := b)
  · refine ⟨?_, hturn, ?_, ?_, ?_⟩
    · intro c
      have := hsmall c
      omega
    · intro hf
      have := hasFour_minStones hf
      omega
    · intro c i hi hs
      have := stone_bound _ _ _ hs
      have := hsmall c
      omega
    · intro c hc hi
      have := hsmall c
      omega
  · intro c
    have := hsmall c
    omega
  · exact htree
  · refine ⟨fun _ _ _ => rfl, ?_⟩
    intro c
    have := hsmall c
    exact ⟨le_refl _, fun _ => rfl, by omega, by omega⟩

theorem own_step_can_avoid {h : Nat} {p : Player} {b : Board 4} {c : Fin 4}
    (ht : toMove b = p) (hn : ¬ HasFour h b (opponent p)) (hc : Legal h b c)
    (hs : CanAvoidLoss h p (play b c p)) : CanAvoidLoss h p b := by
  intro k
  cases k with
  | zero => exact hn
  | succ k =>
    refine ⟨hn, Or.inr (Or.inr ?_)⟩
    rw [if_pos ht, ht]
    exact ⟨c, hc, hs k⟩

theorem opponent_step_can_avoid {h : Nat} {p : Player} {b : Board 4}
    (ht : toMove b = opponent p) (hn : ¬ HasFour h b (opponent p))
    (hs : ∀ c, Legal h b c → CanAvoidLoss h p (play b c (opponent p))) :
    CanAvoidLoss h p b := by
  intro k
  cases k with
  | zero => exact hn
  | succ k =>
    refine ⟨hn, Or.inr (Or.inr ?_)⟩
    rw [if_neg (by rw [ht]; exact Ne.symm (player_ne_opponent p)), ht]
    exact fun c hc => hs c hc k

theorem empty_no_four' (h : Nat) (p : Player) : ¬ HasFour h (emptyBoard 4) p := by
  intro hf
  have := hasFour_minStones hf
  rw [totalStones_empty] at this
  omega

theorem single_no_four (h : Nat) (q : Fin 4) (p : Player) :
    ¬ HasFour h (play (emptyBoard 4) q .black) p := by
  intro hf
  have := hasFour_minStones hf
  rw [totalStones_play', totalStones_empty] at this
  omega

theorem black_opening_eq :
    play (emptyBoard 4) 0 .black = fourTuple [.black] [] [] [] := by
  funext c
  fin_cases c <;> rfl

theorem black_empty_from_opening {h : Nat} (h1 : 1 ≤ h)
    (hs : CanAvoidLoss h .black (fourTuple [.black] [] [] [])) :
    CanAvoidLoss h .black (emptyBoard 4) := by
  apply own_step_can_avoid (c := 0) (toMove_empty 4) (empty_no_four' h _)
  · show 0 < h
    omega
  · simpa only [black_opening_eq] using hs

theorem white_reply_can {h : Nat} (h2 : 2 ≤ h) (q d : Fin 4)
    (hs : CanAvoidLoss h .white (play (play (emptyBoard 4) q .black) d .white)) :
    CanAvoidLoss h .white (play (emptyBoard 4) q .black) := by
  apply own_step_can_avoid (c := d)
  · rw [toMove_play', toMove_empty]
    rfl
  · exact single_no_four h q _
  · unfold Legal
    by_cases hd : d = q
    · subst d
      rw [play_eq]
      change 1 < h
      omega
    · rw [play_ne _ q d .black hd]
      change 0 < h
      omega
  · exact hs

theorem white_opening_eq0 :
    play (play (emptyBoard 4) 0 .black) 0 .white =
      fourTuple [.black, .white] [] [] [] := by
  funext c
  fin_cases c <;> rfl

theorem white_opening_eq1 :
    play (play (emptyBoard 4) 1 .black) 0 .white =
      fourTuple [.white] [.black] [] [] := by
  funext c
  fin_cases c <;> rfl

theorem white_opening_eq2 :
    play (play (emptyBoard 4) 2 .black) 3 .white =
      fourTuple [] [] [.black] [.white] := by
  funext c
  fin_cases c <;> rfl

theorem white_opening_eq3 :
    play (play (emptyBoard 4) 3 .black) 3 .white =
      fourTuple [] [] [] [.black, .white] := by
  funext c
  fin_cases c <;> rfl

theorem white_empty_from_openings {h : Nat} (h2 : 2 ≤ h)
    (h0 : CanAvoidLoss h .white (fourTuple [.black, .white] [] [] []))
    (h1 : CanAvoidLoss h .white (fourTuple [.white] [.black] [] []))
    (h2' : CanAvoidLoss h .white (fourTuple [] [] [.black] [.white]))
    (h3 : CanAvoidLoss h .white (fourTuple [] [] [] [.black, .white])) :
    CanAvoidLoss h .white (emptyBoard 4) := by
  apply opponent_step_can_avoid (p := .white) (toMove_empty 4) (empty_no_four' h _)
  intro q hq
  fin_cases q
  · apply white_reply_can h2 0 0
    simpa only [white_opening_eq0] using h0
  · apply white_reply_can h2 1 0
    simpa only [white_opening_eq1] using h1
  · apply white_reply_can h2 2 3
    simpa only [white_opening_eq2] using h2'
  · apply white_reply_can h2 3 3
    simpa only [white_opening_eq3] using h3

#print axioms small_control_safe

end Connect4.FourColumns
