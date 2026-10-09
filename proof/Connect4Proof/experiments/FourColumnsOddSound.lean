import experiments.FourColumnsOddLift

namespace Connect4.FourColumns

def LiftRegion (h : Nat) (p : Player) (a : Board 4) : Prop :=
  OddState h p a ∧ (HighTail a ∨
    ∃ v, Valid 7 v ∧ ControlTree 7 6 p v ∧ LiftRel h p a v)

theorem lift_region_round {h : Nat} {p : Player} {a : Board 4}
    (h7 : 7 ≤ h) (hh : h % 2 = 1) (ha : LiftRegion h p a)
    (hw : ¬ HasFour h a p) {c : Fin 4} (hc : Legal h a c) :
    ¬ HasFour h (play a c (opponent p)) (opponent p) ∧
    (BoardFull h (play a c (opponent p)) ∨
      ∃ d, Legal h (play a c (opponent p)) d ∧
        LiftRegion h p (play (play a c (opponent p)) d p)) := by
  have tail : HighTail a →
      ¬ HasFour h (play a c (opponent p)) (opponent p) ∧
      (BoardFull h (play a c (opponent p)) ∨
        ∃ d, Legal h (play a c (opponent p)) d ∧
          LiftRegion h p (play (play a c (opponent p)) d p)) := by
    intro ht
    obtain ⟨hn, hf | ⟨d, hd, hs, ht'⟩⟩ := tail_round (by omega) ha.1 ht hw hc
    · exact ⟨hn, Or.inl hf⟩
    · exact ⟨hn, Or.inr ⟨d, hd, hs, Or.inl ht'⟩⟩
  rcases ha.2 with ht | ⟨v, hv, htree, hr⟩
  · exact tail ht
  · have original := htree
    cases htree with
    | won hn hp =>
      exact False.elim (hw (four_height_mono (by omega)
        (lowEq_four (lowEq_symm hr.low) hp)))
    | full hn hf =>
      apply tail
      intro d
      have := hr.lengths d
      have := hf d
      omega
    | node reply hv' htm hn hchild hlegal hcap hnext =>
      have normal : Legal 7 v c →
          ((v c).length = 6 → (a c).length + 1 = h) →
          ¬ HasFour h (play a c (opponent p)) (opponent p) ∧
          (BoardFull h (play a c (opponent p)) ∨
            ∃ d, Legal h (play a c (opponent p)) d ∧
              LiftRegion h p (play (play a c (opponent p)) d p)) := by
        intro hvc hfill
        have hr' := lift_play hr hvc (fun he => Or.inr (hfill he))
          (q := opponent p)
        have hva := play_valid ha.1.valid (p := opponent p) hc
        have hvv := play_valid hv (p := opponent p) hvc
        have hsafe : ¬ HasFour h (play a c (opponent p)) (opponent p) :=
          odd_opponent_safe ha.1 hc hw (fun hfour => hchild c hvc (lowEq_four hr'.low hfour))
        have hboundary : ¬ Legal 7 (play v c (opponent p)) c →
            ¬ Legal h (play a c (opponent p)) c := by
          intro hnv hna
          have hvlt : (v c).length < 7 := hvc
          unfold Legal at hnv hna
          simp only [play_eq, List.length_append, List.length_singleton] at hnv hna
          have hf := hfill (by omega)
          omega
        refine ⟨hsafe, ?_⟩
        by_cases hfa : BoardFull h (play a c (opponent p))
        · exact Or.inl hfa
        · right
          by_cases hfv : BoardFull 7 (play v c (opponent p))
          · obtain ⟨d, hd⟩ := exists_legal hva hfa
            have hnf : ¬ Legal 7 (play v c (opponent p)) c := by
              unfold Legal
              rw [hfv c]
              omega
            refine ⟨d, hd, odd_reply_state ha.1 hc hsafe hd
              (Or.inr (Or.inr (hboundary hnf))), Or.inl ?_⟩
            apply highTail_play
            intro e
            have := hr'.lengths e
            have := hfv e
            omega
          · have hdv := hlegal c hvc hfv
            have hda := lift_legal h7 hh hva hr' hdv
            have hca : reply c = c ∨ (play a c (opponent p) c).length ≤ 2 ∨
                ¬ Legal h (play a c (opponent p)) c := by
              rcases hcap c hvc hfv with he | hs | hf
              · exact Or.inl he
              · right; left
                have := (hr'.lengths c).2.1 (by omega)
                omega
              · exact Or.inr (Or.inr (hboundary hf))
            refine ⟨reply c, hda, odd_reply_state ha.1 hc hsafe hda hca,
              Or.inr ⟨_, play_valid hvv hdv, hnext c hvc hfv, ?_⟩⟩
            exact lift_play hr' hdv (fun _ => Or.inl rfl)
      by_cases hsmall : (v c).length < 6
      · apply normal (show Legal 7 v c from by unfold Legal; omega)
        intro he
        omega
      · by_cases hlast : (v c).length = 6 ∧ (a c).length + 1 = h
        · apply normal (show Legal 7 v c from by unfold Legal; omega)
          exact fun _ => hlast.2
        · have hv6 : 6 ≤ (v c).length := by omega
          have hac : 6 ≤ (a c).length := by have := hr.lengths c; omega
          have hd := lift_buffer_legal hh hv hr hc hv6 hlast
          have hsafe : ¬ HasFour h (play a c (opponent p)) (opponent p) :=
            odd_opponent_safe ha.1 hc hw (fun hf =>
              hn (lowEq_four hr.low (lowEq_four (lowEq_high_play hac) hf)))
          exact ⟨hsafe, Or.inr ⟨c, hd, odd_reply_state ha.1 hc hsafe hd (Or.inl rfl),
            Or.inr ⟨v, hv, original, lift_pair hr hc hv6⟩⟩⟩

/-- The unbounded quantifier over odd finite heights is discharged here. -/
theorem odd_control_lift {h : Nat} {p : Player} {a v : Board 4}
    (h7 : 7 ≤ h) (hh : h % 2 = 1) (ha : OddState h p a)
    (hv : Valid 7 v) (ht : ControlTree 7 6 p v) (hr : LiftRel h p a v) :
    CanAvoidLoss h p a := by
  apply pair_region_safe (LiftRegion h p) (fun _ hb => hb.1)
    (fun _ hb hw _ hc => lift_region_round h7 hh hb hw hc)
  exact ⟨ha, Or.inr ⟨v, hv, ht, hr⟩⟩

#print axioms odd_control_lift

end Connect4.FourColumns
