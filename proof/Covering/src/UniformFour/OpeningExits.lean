import UniformFour.OpeningClosure
import UniformFour.Observations

/-! Concrete full-column exits of the first-player V shape. Reviewed copy.
Every witness is an actual single gravity move. The seven-case split proves
existence only; the executable selector is not replaced by this case table. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

theorem v_full_structure {H a b e d : Nat}
    (bound : Bounded H (vBoard a b e d))
    (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H)
    {p : Col} (hp : Legal H (drop (vBoard a b e d) c4 Q) p) :
    Structural H (afterRound (vBoard a b e d) c4 p) firstException := by
  exact structural_after_cover (v_structural bound) hq hp (v_Q_move_safe hq) (Or.inr full)

theorem v_bottom_blockers (a b e d : Nat) :
    HasP (vBoard a b e d) (.horizontal 1) ∧
    HasP (vBoard a b e d) rise ∧ HasP (vBoard a b e d) down := by
  have corners := v_corners a b e d
  exact ⟨⟨⟨c1,1⟩,by simp [Line.cells],corners.1⟩,
    ⟨⟨c1,1⟩,by simp [rise,Line.cells],corners.1⟩,
    ⟨⟨c4,1⟩,by simp [down,Line.cells],corners.2⟩⟩

/-- Filling c4 puts all exceptional horizontal lines permanently behind P. -/
theorem v_full_unresolved_eq {H a b e d : Nat} (h4 : 4 ≤ H)
    (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H)
    (p : Col) {L : Line}
    (hL : Unresolved H (afterRound (vBoard a b e d) c4 p) L) : L = riseThree := by
  have deq : 2*d+2 = H := by
    have hh := full
    simp only [height_drop_same,v_height_four] at hh
    omega
  have dp : 0 < d := by omega
  have row3 : HasP (vBoard a b e d) rowThree := by
    refine ⟨⟨c4,3⟩,by simp [rowThree,Line.cells],?_⟩
    change readRow (P :: qp d) 3 = some P
    rw [read_pqp_P]
    omega
  have complete := exceptionComplete_after_cover (v_exception_complete H a b e d)
    hq (p := p) (Or.inr full)
  have checked := toCheck_mono complete hL.1
  have blocks := v_bottom_blockers a b e d
  have keep : ∀ M, HasP (vBoard a b e d) M →
      HasP (afterRound (vBoard a b e d) c4 p) M := by
    intro M hm
    exact hasP_drop_preserves (hasP_drop_preserves hm c4 Q) p P
  rcases firstException_check_lines checked with he | he | he | he | he
  · exact False.elim (hL.2 (he.symm ▸ keep _ blocks.1))
  · exact False.elim (hL.2 (he.symm ▸ keep _ blocks.2.1))
  · exact False.elim (hL.2 (he.symm ▸ keep _ blocks.2.2))
  · exact False.elim (hL.2 (he.symm ▸ keep _ row3))
  · exact he

/-- A one-line unresolved set disappears as soon as its last line is blocked. -/
theorem a0_of_only_blocked {H : Nat} {z : Board} {M : Line}
    (only : ∀ L, Unresolved H z L → L = M) (blocked : HasP z M) : A0 H z := by
  intro L hL
  have eq := only L hL
  subst L
  exact hL.2 blocked

theorem v_full_good_of_blocks_rise {H a b e d : Nat} (h4 : 4 ≤ H)
    (bound : Bounded H (vBoard a b e d)) (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H)
    {p : Col} (hp : Legal H (drop (vBoard a b e d) c4 Q) p)
    (blocked : HasP (afterRound (vBoard a b e d) c4 p) riseThree) :
    Good H (afterRound (vBoard a b e d) c4 p) := by
  apply good_of_structural (v_full_structure bound hq full hp)
  intro noP notFull
  exact Or.inl (Or.inl (a0_of_only_blocked
    (fun L hL => v_full_unresolved_eq h4 hq full p hL) blocked))

/-- First row of U2's exit table: the only possible unresolved line is out of bounds. -/
theorem v_full_height_four_good {a b e d : Nat}
    (bound : Bounded 4 (vBoard a b e d)) (hq : Legal 4 (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = 4)
    {p : Col} (hp : Legal 4 (drop (vBoard a b e d) c4 Q) p) :
    Good 4 (afterRound (vBoard a b e d) c4 p) := by
  apply good_of_structural (v_full_structure bound hq full hp)
  intro noP notFull
  apply Or.inl; apply Or.inl
  intro L hL
  have eq := v_full_unresolved_eq (by decide) hq full p hL
  subst L
  have bad : 6 ≤ 4 := (hL.1.1 ⟨c4,6⟩ (by simp [riseThree,Line.cells])).2
  omega

/-- a=0: the gravity response at (c1,3) removes the last exception. -/
theorem v_full_zero_a_good {H b e d : Nat} (h6 : 6 ≤ H)
    (bound : Bounded H (vBoard 0 b e d)) (hq : Legal H (vBoard 0 b e d) c4)
    (full : height (drop (vBoard 0 b e d) c4 Q) c4 = H) :
    Qualified H (drop (vBoard 0 b e d) c4 Q) c1 := by
  have hp : Legal H (drop (vBoard 0 b e d) c4 Q) c1 := by
    simp [Legal,height,drop,vBoard,board,qp] <;> omega
  refine ⟨hp,v_full_good_of_blocks_rise (by omega) bound hq full hp ?_⟩
  exact ⟨⟨c1,3⟩,by simp [riseThree,Line.cells],rfl⟩

/-- b>=2: the fixed P at (c2,4) blocks the only possible unresolved line. -/
theorem v_full_large_b_good {H a b e d : Nat} (h4 : 4 ≤ H) (hb : 2 ≤ b)
    (bound : Bounded H (vBoard a b e d)) (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H)
    {p : Col} (hp : Legal H (drop (vBoard a b e d) c4 Q) p) :
    Good H (afterRound (vBoard a b e d) c4 p) := by
  apply v_full_good_of_blocks_rise h4 bound hq full hp
  have stone : stoneAt (vBoard a b e d) ⟨c2,4⟩ = some P := by
    change readRow (qp b) 4 = some P
    rw [read_qp_P]
    omega
  exact ⟨⟨c2,4⟩,by simp [riseThree,Line.cells],
    stoneAt_drop_preserves (stoneAt_drop_preserves stone c4 Q) p P⟩

/-- e=2: the response itself acquires (c3,5). -/
theorem v_full_e_two_good {H a b d : Nat} (h6 : 6 ≤ H)
    (bound : Bounded H (vBoard a b 2 d)) (hq : Legal H (vBoard a b 2 d) c4)
    (full : height (drop (vBoard a b 2 d) c4 Q) c4 = H) :
    Qualified H (drop (vBoard a b 2 d) c4 Q) c3 := by
  have hp : Legal H (drop (vBoard a b 2 d) c4 Q) c3 := by
    simp [Legal,height,drop,vBoard,board,qp] <;> omega
  refine ⟨hp,v_full_good_of_blocks_rise (by omega) bound hq full hp ?_⟩
  exact ⟨⟨c3,5⟩,by simp [riseThree,Line.cells],rfl⟩

/-- e<=1: (c3,5) remains at positive even distance after the response. -/
theorem v_full_small_e_target {H a b e d : Nat} (even : H%2 = 0)
    (h6 : 6 ≤ H) (he : e ≤ 1) (bound : Bounded H (vBoard a b e d))
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H) :
    TargetCondition H (afterRound (vBoard a b e d) c4 c3) ⟨c3,5⟩ := by
  have h1 := bound c1
  have h2 := bound c2
  have h4 : 2*d+2 = H := by
    have hh := full
    simp only [height_drop_same,v_height_four] at hh
    omega
  simp only [v_height_one,v_height_two] at h1 h2
  have hcol : height (afterRound (vBoard a b e d) c4 c3) c3 = 2*e+1 := by
    simp [afterRound,height,drop,vBoard,board]
  have pos : height (afterRound (vBoard a b e d) c4 c3) c3 < 5 := by omega
  refine ⟨⟨by decide,show 5 ≤ H from by omega⟩,cell_empty_above_height pos,pos,?_,?_⟩
  · change (5-height (afterRound (vBoard a b e d) c4 c3) c3)%2 = 0
    omega
  · simp [outsideTarget,outside,allCols,inJ,height,afterRound,drop,vBoard,board] <;> omega

theorem v_full_small_e_good {H a b e d : Nat} (even : H%2 = 0)
    (h6 : 6 ≤ H) (he : e ≤ 1) (bound : Bounded H (vBoard a b e d))
    (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H) :
    Qualified H (drop (vBoard a b e d) c4 Q) c3 := by
  have hp : Legal H (drop (vBoard a b e d) c4 Q) c3 := by
    simp [Legal,height,drop,vBoard,board] <;> omega
  refine ⟨hp,?_⟩
  apply good_of_structural (v_full_structure bound hq full hp)
  intro noP notFull
  apply Or.inl; apply Or.inr; apply Or.inl
  refine ⟨⟨c3,5⟩,v_full_small_e_target even h6 he bound full,?_⟩
  intro L hL
  have eq := v_full_unresolved_eq (by omega) hq full c3 hL
  subst L
  simp [targetCell,riseThree,Line.cells]

/-- Three real fixed stones used by BOTH last rows of the exit table. -/
theorem v_down_fixed {H a b e d : Nat} (h4 : 4 ≤ H) (ha : 1 ≤ a) (he : 1 ≤ e) :
    FixedWinningTarget H (vBoard a b e d) ⟨c2,3⟩ := by
  refine ⟨down,down_valid h4,by simp [targetCell,down,Line.cells],?_⟩
  intro x hx ne
  simp only [down,Line.cells,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · change readRow (P :: Q :: qp a) 4 = some P
    rw [read_pqqp_P] <;> omega
  · exact False.elim (ne rfl)
  · change readRow (qp e) 2 = some P
    rw [read_qp_P] <;> omega
  · exact (v_corners a b e d).2

theorem v_full_b_one_wins {H a e d : Nat} (h6 : 6 ≤ H) (ha : 1 ≤ a) (he : 3 ≤ e)
    (hq : Legal H (vBoard a 1 e d) c4) :
    Qualified H (drop (vBoard a 1 e d) c4 Q) c2 := by
  have hp : Legal H (drop (vBoard a 1 e d) c4 Q) c2 := by
    simp [Legal,height,drop,vBoard,board,qp] <;> omega
  have win : Wins H (afterRound (vBoard a 1 e d) c4 c2) P := by
    rcases v_down_fixed (H := H) (a := a) (b := 1) (e := e) (d := d) (by omega) ha (by omega) with ⟨L,hv,on,fixed⟩
    refine ⟨L,hv,?_⟩
    intro x hx
    by_cases eq : x = targetCell ⟨c2,3⟩
    · subst x
      rfl
    · exact stoneAt_drop_preserves (stoneAt_drop_preserves (fixed x hx eq) c4 Q) c2 P
  exact ⟨hp,Or.inl ⟨fun hw => v_Q_move_safe hq
    (wins_drop_other_colour (by decide) c2 hw),Or.inl win⟩⟩

/-- b=0: occupy the bottom first; (c2,3) is a genuine fixed-three A2 target. -/
theorem v_full_b_zero_good {H a e d : Nat} (even : H%2 = 0)
    (h6 : 6 ≤ H) (ha : 1 ≤ a) (he : 3 ≤ e)
    (bound : Bounded H (vBoard a 0 e d)) (hq : Legal H (vBoard a 0 e d) c4)
    (full : height (drop (vBoard a 0 e d) c4 Q) c4 = H) :
    Qualified H (drop (vBoard a 0 e d) c4 Q) c2 := by
  have hp : Legal H (drop (vBoard a 0 e d) c4 Q) c2 := by
    simp [Legal,height,drop,vBoard,board,qp] <;> omega
  have h1 := bound c1
  have h3 := bound c3
  have h4 : 2*d+2 = H := by
    have hh := full
    simp only [height_drop_same,v_height_four] at hh
    omega
  simp only [v_height_one,v_height_three] at h1 h3
  have colHeight : height (afterRound (vBoard a 0 e d) c4 c2) c2 = 1 := by
    simp [afterRound,height,drop,vBoard,board,qp]
  have pos : height (afterRound (vBoard a 0 e d) c4 c2) c2 < 3 := by omega
  refine ⟨hp,?_⟩
  apply good_of_structural (v_full_structure bound hq full hp)
  intro noP notFull
  apply Or.inl; apply Or.inr; apply Or.inr
  refine ⟨⟨c2,3⟩,?_,?_,?_⟩
  · refine ⟨⟨by decide,show 3 ≤ H from by omega⟩,cell_empty_above_height pos,pos,?_,?_⟩
    · change (3-height (afterRound (vBoard a 0 e d) c4 c2) c2)%2 = 0
      simp only [colHeight]
    · simp [outsideTarget,outside,allCols,inJ,height,afterRound,drop,vBoard,board,qp] <;> omega
  · exact fixedWinningTarget_preserved (v_down_fixed (by omega) ha (by omega)) c4 c2
  · intro L hL
    have eq := v_full_unresolved_eq (by omega) hq full c2 hL
    subst L
    exact ⟨⟨c2,4⟩,by simp [riseThree,Line.cells],rfl,by decide⟩

/-- Complete, mutually exhaustive existence proof for the V full-column event. -/
theorem v_full_reply_exists {H a b e d : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    (bound : Bounded H (vBoard a b e d)) (hq : Legal H (vBoard a b e d) c4)
    (full : height (drop (vBoard a b e d) c4 Q) c4 = H)
    (notFull : ¬ Full H (drop (vBoard a b e d) c4 Q)) :
    ∃ p, Qualified H (drop (vBoard a b e d) c4 Q) p := by
  by_cases hH : H = 4
  · rcases hH with rfl
    rcases bounded_notFull_exists_legal (drop_bounded bound hq Q) notFull with ⟨p,hp⟩
    exact ⟨p,hp,v_full_height_four_good bound hq full hp⟩
  have h6 : 6 ≤ H := by omega
  by_cases ha : a = 0
  · subst a
    exact ⟨c1,v_full_zero_a_good h6 bound hq full⟩
  by_cases hb : 2 ≤ b
  · rcases bounded_notFull_exists_legal (drop_bounded bound hq Q) notFull with ⟨p,hp⟩
    exact ⟨p,hp,v_full_large_b_good h4 hb bound hq full hp⟩
  by_cases he : e = 2
  · subst e
    exact ⟨c3,v_full_e_two_good h6 bound hq full⟩
  by_cases hesmall : e ≤ 1
  · exact ⟨c3,v_full_small_e_good even h6 hesmall bound hq full⟩
  have he3 : 3 ≤ e := by omega
  have ha1 : 1 ≤ a := by omega
  have bc : b = 0 ∨ b = 1 := by omega
  rcases bc with rfl | rfl
  · exact ⟨c2,v_full_b_zero_good even h6 ha1 he3 bound hq full⟩
  · exact ⟨c2,v_full_b_one_wins h6 ha1 he3 hq⟩

/-- V either remains V under the actual selector or reaches a checked exit.
The double-corner override is explicitly honored, even if another move wins. -/
theorem v_select_closed {H : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    {z : Board} (shape : VShape H z) {q p : Col} (hq : Legal H z q)
    (notFull : ¬ Full H (drop z q Q)) {o : Observation}
    (obs : Observes H (drop z q Q) o) (chosen : select H (drop z q Q) q o = some p) :
    ¬ Wins H (drop z q Q) Q ∧
      (Good H (afterRound z q p) ∨ VShape H (afterRound z q p)) := by
  rcases shape with ⟨a,b,e,d,rfl,bound⟩
  refine ⟨v_Q_move_safe hq,?_⟩
  by_cases legalCover : Legal H (drop (vBoard a b e d) q Q) q
  · have corners := v_corners a b e d
    have cornersAfter : BothCorners (drop (vBoard a b e d) q Q) :=
      ⟨stoneAt_drop_preserves corners.1 q Q,stoneAt_drop_preserves corners.2 q Q⟩
    have eq := select_cover_of_corners obs legalCover cornersAfter
    have pp : p = q := (Option.some.inj (chosen.symm.trans eq))
    subst p
    exact Or.inr (v_cover_shape ⟨a,b,e,d,rfl,bound⟩ hq legalCover)
  · have boundQ := drop_bounded bound hq Q
    have full : height (drop (vBoard a b e d) q Q) q = H := by
      have le := boundQ q
      unfold Legal at legalCover
      omega
    have eq := v_only_four_can_fill even full
    subst q
    have existsGood := v_full_reply_exists even h4 bound hq full notFull
    rcases select_qualified_or_corner_cover obs existsGood chosen with good | ⟨peq,_⟩
    · exact Or.inl good.2
    · subst p
      exact False.elim (legalCover (select_legal chosen))

#print axioms v_full_reply_exists
#print axioms v_select_closed
end UniformFour.U2
