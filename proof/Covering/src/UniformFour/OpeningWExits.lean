import UniformFour.OpeningExits

/-! U2 W-shape event exits. Each witness is proved from the concrete board.
Reviewed local proof scripts; see audit.json and kernel_audit.json. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

@[simp] theorem read_append_P_Q (xs : List Player) (r : Nat) :
    readRow (xs ++ [P]) r = some Q ↔ readRow xs r = some Q := by
  constructor
  · intro h
    exact stoneAt_drop_other_colour (b := fun _ => xs) (x := ⟨c1,r⟩)
      (by decide : Q ≠ P) c1 h
  · intro h
    exact stoneAt_drop_preserves (b := fun _ => xs) (x := ⟨c1,r⟩) h c1 P

theorem w_first_legal {H a d : Nat} (even : H%2 = 0)
    (bound : Bounded H (wBoard a d)) : Legal H (wBoard a d) c1 := by
  have h := bound c1
  unfold Legal
  simp only [w_height_one] at *
  omega

theorem w_second_reply_legal {H a d : Nat} (even : H%2 = 0)
    (bound : Bounded H (wBoard a d)) : Legal H (drop (wBoard a d) c2 Q) c1 := by
  have h := w_first_legal even bound
  simpa [Legal,height,drop] using h

theorem w_second_elementary {H a d : Nat}
    (bound : Bounded H (afterRound (wBoard a d) c2 c1)) :
    ElementarySecond H (afterRound (wBoard a d) c2 c1) := by
  constructor
  · exact bound
  · intro c hc r hs
    rcases hc with rfl | rfl
    · change readRow ((P :: qp a) ++ [P]) r = some Q ∧
        readRow ((P :: qp a) ++ [P]) (r+1) = some Q at hs
      simp only [read_append_P_Q, read_pqp_Q] at hs
      omega
    · simp [afterRound,stoneAt_readRow,drop,wBoard,board] at hs <;> omega
  · intro c hc r hs
    rcases hc with rfl | rfl <;>
      simp [afterRound,stoneAt_readRow,drop,wBoard,board] at hs <;> omega
  · intro c hc hs
    rcases hc with rfl | rfl <;>
      simp [afterRound,stoneAt_readRow,drop,wBoard,board,height] at *
  · intro c hc hn hs
    rcases hc with rfl | rfl
    · exact no_Q_top_after_P (drop (wBoard a d) c2 Q) c1 hs
    · simp [afterRound,stoneAt_readRow,drop,wBoard,board,height] at hs <;> omega
  · intro r hs
    simp [afterRound,stoneAt_readRow,drop,wBoard,board] at hs

theorem w_bottom_blockers (a d : Nat) :
    HasP (wBoard a d) (.horizontal 1) ∧ HasP (wBoard a d) rise := by
  have stone : stoneAt (wBoard a d) ⟨c1,1⟩ = some P := by simp [stoneAt,wBoard,board]
  exact ⟨⟨⟨c1,1⟩,by simp [Line.cells],stone⟩,
    ⟨⟨c1,1⟩,by simp [rise,Line.cells],stone⟩⟩

/-- Every W event into c2 has an A1 witness in c1. The target is c2,row3;
the actual/potential exception's row2 is blocked using the W parameter condition. -/
theorem w_second_reply_good {H a d : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    (bound : Bounded H (wBoard a d)) (ad : 0 < a → 0 < d) :
    Qualified H (drop (wBoard a d) c2 Q) c1 := by
  have hq : Legal H (wBoard a d) c2 := by simp [Legal] <;> omega
  have hp := w_second_reply_legal even bound
  have finalBound := drop_bounded (drop_bounded bound hq Q) hp P
  have s := (w_second_elementary finalBound).structural
  have firstBound := bound c1
  have fourthBound := bound c4
  simp only [w_height_one,w_height_four] at firstBound fourthBound
  refine ⟨hp,?_⟩
  apply good_of_structural s
  intro noP notFull
  apply Or.inl; apply Or.inr; apply Or.inl
  refine ⟨⟨c2,3⟩,?_,?_⟩
  · have pos : height (afterRound (wBoard a d) c2 c1) c2 < 3 := by
      simp [height,afterRound,drop,wBoard,board]
    refine ⟨⟨by decide,show 3 ≤ H from by omega⟩,cell_empty_above_height pos,pos,?_,?_⟩
    · simp [height,afterRound,drop,wBoard,board]
    · simp [outsideTarget,outside,allCols,inJ,height,afterRound,drop,wBoard,board] <;> omega
  · intro L hL
    have checked := toCheck_mono s.complete hL.1
    have oldBlocks := w_bottom_blockers a d
    have keep : ∀ M, HasP (wBoard a d) M →
        HasP (afterRound (wBoard a d) c2 c1) M := by
      intro M hm
      exact hasP_drop_preserves (hasP_drop_preserves hm c2 Q) c1 P
    have row2 : HasP (afterRound (wBoard a d) c2 c1) rowTwo := by
      by_cases ha : a = 0
      · subst a
        exact ⟨⟨c1,2⟩,by simp [rowTwo,Line.cells],rfl⟩
      · have hd : 0 < d := ad (by omega)
        have stone : stoneAt (wBoard a d) ⟨c4,2⟩ = some P := by
          change readRow (qp d) 2 = some P
          rw [read_qp_P] <;> omega
        exact keep rowTwo ⟨⟨c4,2⟩,by simp [rowTwo,Line.cells],stone⟩
    rcases middle_check_lines checked with eq | eq | eq | eq
    · exact False.elim (hL.2 (eq.symm ▸ keep _ oldBlocks.1))
    · exact False.elim (hL.2 (eq.symm ▸ keep _ oldBlocks.2))
    · subst L
      exact down_target_on_down
    · exact False.elim (hL.2 (eq.symm ▸ row2))

/-- Entering c3 is met by a direct cover which blocks the last bottom diagonal. -/
theorem w_third_reply_good {H a d : Nat} (h4 : 4 ≤ H)
    (bound : Bounded H (wBoard a d)) : Qualified H (drop (wBoard a d) c3 Q) c3 := by
  have hq : Legal H (wBoard a d) c3 := by simp [Legal] <;> omega
  have hp : Legal H (drop (wBoard a d) c3 Q) c3 := by
    simp [Legal,height,drop,wBoard,board] <;> omega
  have s := structural_after_cover (w_structural bound) hq hp (w_Q_move_safe hq) (Or.inl rfl)
  refine ⟨hp,?_⟩
  apply good_of_structural s
  intro noP notFull
  apply Or.inl; apply Or.inl
  intro L hL
  have checked := toCheck_mono s.complete hL.1
  rcases checked with ⟨valid,nonvertical,x,hx,hbot | hfalse⟩
  · have old := w_bottom_blockers a d
    have keep : ∀ M, HasP (wBoard a d) M → HasP (afterRound (wBoard a d) c3 c3) M := by
      intro M hm
      exact hasP_drop_preserves (hasP_drop_preserves hm c3 Q) c3 P
    rcases bottom_line_cases valid nonvertical ⟨x,hx,hbot⟩ with eq | eq | eq
    · exact hL.2 (eq.symm ▸ keep _ old.1)
    · exact hL.2 (eq.symm ▸ keep _ old.2)
    · subst L
      exact hL.2 ⟨⟨c3,2⟩,by simp [down,Line.cells],rfl⟩
  · exact hfalse

/-- The W c1 full event always has the legal c2-bottom A1 exit. -/
theorem w_first_full_reply_good {H a d : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    (bound : Bounded H (wBoard a d)) (hq : Legal H (wBoard a d) c1)
    (full : height (drop (wBoard a d) c1 Q) c1 = H) :
    Qualified H (drop (wBoard a d) c1 Q) c2 := by
  have hp : Legal H (drop (wBoard a d) c1 Q) c2 := by
    simp [Legal,height,drop,wBoard,board] <;> omega
  have s := structural_after_cover (w_structural bound) hq hp (w_Q_move_safe hq) (Or.inr full)
  have h1 : 2*a+2 = H := by
    have hh := full
    simp only [height_drop_same,w_height_one] at hh
    omega
  have h4b := bound c4
  simp only [w_height_four] at h4b
  refine ⟨hp,?_⟩
  apply good_of_structural s
  intro noP notFull
  apply Or.inl; apply Or.inr; apply Or.inl
  refine ⟨⟨c2,3⟩,?_,?_⟩
  · have pos : height (afterRound (wBoard a d) c1 c2) c2 < 3 := by
      simp [height,afterRound,drop,wBoard,board]
    refine ⟨⟨by decide,show 3 ≤ H from by omega⟩,cell_empty_above_height pos,pos,?_,?_⟩
    · simp [height,afterRound,drop,wBoard,board]
    · simp [outsideTarget,outside,allCols,inJ,height,afterRound,drop,wBoard,board] <;> omega
  · intro L hL
    have checked := toCheck_mono s.complete hL.1
    rcases checked with ⟨valid,nonvertical,x,hx,hbot | hfalse⟩
    · have old := w_bottom_blockers a d
      have keep : ∀ M, HasP (wBoard a d) M → HasP (afterRound (wBoard a d) c1 c2) M := by
        intro M hm
        exact hasP_drop_preserves (hasP_drop_preserves hm c1 Q) c2 P
      rcases bottom_line_cases valid nonvertical ⟨x,hx,hbot⟩ with eq | eq | eq
      · exact False.elim (hL.2 (eq.symm ▸ keep _ old.1))
      · exact False.elim (hL.2 (eq.symm ▸ keep _ old.2))
      · subst L
        exact down_target_on_down
    · exact False.elim hfalse

/-- In W, the right bottom is Q or empty, never P, even after a Q move. -/
theorem w_after_Q_no_corners (a d : Nat) (q : Col) :
    ¬ BothCorners (drop (wBoard a d) q Q) := by
  intro h
  have old := stoneAt_drop_other_colour (by decide : P ≠ Q) q h.2
  have impossible : ¬ stoneAt (wBoard a d) ⟨c4,1⟩ = some P := by
    change ¬ readRow (qp d) 1 = some P
    rw [read_qp_P]
    omega
  exact impossible old

/-- If the exact checker accepts anything in W, the actual selected response
is accepted. There is no double-corner override in this shape. -/
theorem w_select_good_of_exists {H a d : Nat} {q p : Col} {o : Observation}
    (obs : Observes H (drop (wBoard a d) q Q) o)
    (existsGood : ∃ r, Qualified H (drop (wBoard a d) q Q) r)
    (chosen : select H (drop (wBoard a d) q Q) q o = some p) :
    Good H (afterRound (wBoard a d) q p) :=
  (select_qualified_of_no_corners obs existsGood (w_after_Q_no_corners a d q) chosen).2

#print axioms w_second_reply_good
#print axioms w_third_reply_good
#print axioms w_first_full_reply_good
end UniformFour.U2
