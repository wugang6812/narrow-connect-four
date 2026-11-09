import UniformFour.OpeningWExits

/-! Exact U2 low-row fallback and first-player pending invariant. Reviewed copy.
The fallback is the actual score selector, not a substitute safe controller. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- At the root after Q(c1,2), only the other bottom corner blocks all three lines. -/
theorem root_first_scores {H : Nat} (h4 : 4 ≤ H) (p : Col) :
    bottomScore H (drop (wBoard 0 0) c1 Q) p = if p = c4 then 3 else 2 := by
  cases p <;> simp [bottomScore,bottomLines,h4,hasPBool,Line.cells,
    stoneAt,drop,wBoard,board,qp]

/-- At the root after Q(c4,1), all four replies retain exactly two bottom blockers. -/
theorem root_fourth_scores {H : Nat} (h4 : 4 ≤ H) (p : Col) :
    bottomScore H (drop (wBoard 0 0) c4 Q) p = 2 := by
  cases p <;> simp [bottomScore,bottomLines,h4,hasPBool,Line.cells,
    stoneAt,drop,wBoard,board,qp]

/-- With a nonempty right column and a=0, no one-move reply can block D. -/
theorem low_first_scores {H d : Nat} (h4 : 4 ≤ H) (hd : 0 < d) (p : Col) :
    bottomScore H (drop (wBoard 0 d) c1 Q) p = 2 := by
  cases d with
  | zero => omega
  | succ d =>
      have qz : qp 0 = [] := rfl
      cases p <;> simp [qz,bottomScore,bottomLines,h4,hasPBool,Line.cells,
        stoneAt,drop,wBoard,board,qp_succ_front]

theorem fallback_root_first {H : Nat} (h4 : 4 ≤ H) :
    fallback H (drop (wBoard 0 0) c1 Q) c1
      (bottomScore H (drop (wBoard 0 0) c1 Q)) = some c4 := by
  have scores : bottomScore H (drop (wBoard 0 0) c1 Q) =
      (fun p => if p = c4 then 3 else 2) := funext (root_first_scores h4)
  rw [scores]
  have h0 : 0 < H := by omega
  have h1 : 1 < H := by omega
  have h2 : 2 < H := by omega
  simp [fallback,height,drop,wBoard,board,qp,allCols,bestFrom,List.filter,bne,BEq.beq,instBEqCol.beq,Col.ctorIdx,
    h0,h1,h2,root_first_scores h4]

theorem fallback_root_fourth {H : Nat} (h4 : 4 ≤ H) :
    fallback H (drop (wBoard 0 0) c4 Q) c4
      (bottomScore H (drop (wBoard 0 0) c4 Q)) = some c4 := by
  have scores : bottomScore H (drop (wBoard 0 0) c4 Q) = (fun _ => 2) :=
    funext (root_fourth_scores h4)
  rw [scores]
  have h0 : 0 < H := by omega
  have h1 : 1 < H := by omega
  simp [fallback,height,drop,wBoard,board,qp,allCols,bestFrom,List.filter,bne,BEq.beq,instBEqCol.beq,Col.ctorIdx,
    h0,h1,root_fourth_scores h4]

theorem fallback_low_first {H d : Nat} (h4 : 4 ≤ H) (hd : 0 < d) :
    fallback H (drop (wBoard 0 d) c1 Q) c1
      (bottomScore H (drop (wBoard 0 d) c1 Q)) = some c1 := by
  have scores : bottomScore H (drop (wBoard 0 d) c1 Q) = (fun _ => 2) :=
    funext (low_first_scores h4 hd)
  rw [scores]
  have h0 : 0 < H := by omega
  have h2 : 2 < H := by omega
  by_cases lastLegal : 2*d < H <;>
    simp [fallback,height,drop,wBoard,board,qp,allCols,bestFrom,List.filter,bne,BEq.beq,instBEqCol.beq,Col.ctorIdx,
      h0,h2,lastLegal,low_first_scores h4 hd]

/-- High-row fallback is literally same-column coverage. -/
theorem fallback_high {H : Nat} {z : Board} {q : Col} (score : Col → Nat)
    (legal : Legal H z q) (high : 3 ≤ height z q) : fallback H z q score = some q := by
  have legalHeight : height z q < H := legal
  simp [fallback,legalHeight,high]

theorem w_cover_one_shape {H a d : Nat} (bound : Bounded H (wBoard a d))
    (hd : 0 < d) (hq : Legal H (wBoard a d) c1)
    (hp : Legal H (drop (wBoard a d) c1 Q) c1) :
    WShape H (afterRound (wBoard a d) c1 c1) := by
  exact ⟨a+1,d,w_cover_one a d,drop_bounded (drop_bounded bound hq Q) hp P,fun _ => hd⟩

theorem w_cover_four_shape {H a d : Nat} (bound : Bounded H (wBoard a d))
    (hq : Legal H (wBoard a d) c4)
    (hp : Legal H (drop (wBoard a d) c4 Q) c4) :
    WShape H (afterRound (wBoard a d) c4 c4) := by
  exact ⟨a,d+1,w_cover_four a d,drop_bounded (drop_bounded bound hq Q) hp P,by omega⟩

/-- The only non-certificate active fallback is W(0,0) -> V(0,0,0,0).
The high cases and the two low-score ties all cover the opponent's column. -/
theorem w_no_qualified_selected_shape {H a d : Nat}
    (even : H%2 = 0) (h4 : 4 ≤ H) (bound : Bounded H (wBoard a d))
    (ad : 0 < a → 0 < d) {q p : Col} (hq : Legal H (wBoard a d) q)
    {o : Observation} (obs : Observes H (drop (wBoard a d) q Q) o)
    (none : ¬ ∃ c, Qualified H (drop (wBoard a d) q Q) c)
    (chosen : select H (drop (wBoard a d) q Q) q o = some p) :
    WShape H (afterRound (wBoard a d) q p) ∨
      VShape H (afterRound (wBoard a d) q p) := by
  have hp := select_legal chosen
  have fallbackChosen : fallback H (drop (wBoard a d) q Q) q
      (bottomScore H (drop (wBoard a d) q Q)) = some p := by
    rw [select_fallback_of_none obs none (w_after_Q_no_corners a d q)] at chosen
    have scores : o.bottomScore = bottomScore H (drop (wBoard a d) q Q) :=
      funext obs.bottomScore
    simpa only [scores] using chosen
  cases q with
  | c2 => exact False.elim (none ⟨c1,w_second_reply_good even h4 bound ad⟩)
  | c3 => exact False.elim (none ⟨c3,w_third_reply_good h4 bound⟩)
  | c1 =>
      have coverLegal : Legal H (drop (wBoard a d) c1 Q) c1 := by
        apply Classical.byContradiction
        intro hn
        have le := drop_bounded bound hq Q c1
        have full : height (drop (wBoard a d) c1 Q) c1 = H := by
          unfold Legal at hn
          omega
        exact none ⟨c2,w_first_full_reply_good even h4 bound hq full⟩
      by_cases high : 3 ≤ height (drop (wBoard a d) c1 Q) c1
      · have eq := fallback_high (bottomScore H (drop (wBoard a d) c1 Q)) coverLegal high
        have pp : p = c1 := Option.some.inj (fallbackChosen.symm.trans eq)
        subst p
        have apos : 0 < a := by
          simp only [height_drop_same,w_height_one] at high
          omega
        exact Or.inl (w_cover_one_shape bound (ad apos) hq coverLegal)
      · have az : a = 0 := by
          simp only [height_drop_same,w_height_one] at high
          omega
        subst a
        by_cases dz : d = 0
        · subst d
          have pp : p = c4 := Option.some.inj
            (fallbackChosen.symm.trans (fallback_root_first h4))
          subst p
          exact Or.inr ⟨0,0,0,0,w_root_switch,
            drop_bounded (drop_bounded bound hq Q) hp P⟩
        · have dp : 0 < d := by omega
          have pp : p = c1 := Option.some.inj
            (fallbackChosen.symm.trans (fallback_low_first h4 dp))
          subst p
          exact Or.inl (w_cover_one_shape bound dp hq coverLegal)
  | c4 =>
      have coverLegal := w_four_cover_legal even hq
      by_cases high : 3 ≤ height (drop (wBoard a d) c4 Q) c4
      · have eq := fallback_high (bottomScore H (drop (wBoard a d) c4 Q)) coverLegal high
        have pp : p = c4 := Option.some.inj (fallbackChosen.symm.trans eq)
        subst p
        exact Or.inl (w_cover_four_shape bound hq coverLegal)
      · have dz : d = 0 := by
          simp only [height_drop_same,w_height_four] at high
          omega
        subst d
        have az : a = 0 := by
          apply Classical.byContradiction
          intro h
          have := ad (by omega)
          omega
        subst a
        have pp : p = c4 := Option.some.inj
          (fallbackChosen.symm.trans (fallback_root_fourth h4))
        subst p
        exact Or.inl (w_cover_four_shape bound hq coverLegal)

/-- All W branches use the same exact selector; the case split only proves it. -/
theorem w_select_closed {H : Nat} (even : H%2 = 0) (h4 : 4 ≤ H)
    {z : Board} (shape : WShape H z) {q p : Col} (hq : Legal H z q)
    {o : Observation} (obs : Observes H (drop z q Q) o)
    (chosen : select H (drop z q Q) q o = some p) :
    ¬ Wins H (drop z q Q) Q ∧
      (Good H (afterRound z q p) ∨ WShape H (afterRound z q p) ∨
        VShape H (afterRound z q p)) := by
  rcases shape with ⟨a,d,rfl,bound,ad⟩
  refine ⟨w_Q_move_safe hq,?_⟩
  by_cases existsGood : ∃ c, Qualified H (drop (wBoard a d) q Q) c
  · exact Or.inl (w_select_good_of_exists obs existsGood chosen)
  · exact Or.inr (w_no_qualified_selected_shape even h4 bound ad hq obs existsGood chosen)

/-- This is a current-board invariant, NOT stored state in the response function. -/
def FirstPending (H : Nat) (z : Board) : Prop :=
  H%2 = 0 ∧ 4 ≤ H ∧ (WShape H z ∨ VShape H z)

theorem pending_state_safe {H : Nat} {z : Board} (h : FirstPending H z) :
    Bounded H z ∧ ¬ Wins H z Q := by
  rcases h.2.2 with ⟨a,d,rfl,bound,_⟩ | ⟨a,b,e,d,rfl,bound⟩
  · exact ⟨bound,w_noQ H a d⟩
  · exact ⟨bound,v_noQ H a b e d⟩

theorem firstBoard_pending_even {H : Nat} (even : H%2 = 0) (h4 : 4 ≤ H) :
    FirstPending H firstBoard := by
  refine ⟨even,h4,Or.inl ⟨0,0,?_,firstBoard_bounded (by omega),?_⟩⟩
  · funext c; cases c <;> rfl
  · omega

/-- Concrete pending closure for every exact observation and every selected move. -/
theorem pending_selected_closed {H : Nat} {z : Board} (pending : FirstPending H z)
    {q p : Col} (hq : Legal H z q) (notFull : ¬ Full H (drop z q Q))
    {o : Observation} (obs : Observes H (drop z q Q) o)
    (chosen : select H (drop z q Q) q o = some p) :
    ¬ Wins H (drop z q Q) Q ∧
      (Good H (afterRound z q p) ∨ FirstPending H (afterRound z q p)) := by
  rcases pending with ⟨even,h4,shape | shape⟩
  · rcases w_select_closed even h4 shape hq obs chosen with ⟨safe,good | shapes⟩
    · exact ⟨safe,Or.inl good⟩
    · exact ⟨safe,Or.inr ⟨even,h4,shapes⟩⟩
  · rcases v_select_closed even h4 shape hq notFull obs chosen with ⟨safe,good | shape⟩
    · exact ⟨safe,Or.inl good⟩
    · exact ⟨safe,Or.inr ⟨even,h4,Or.inr shape⟩⟩

/-- There is no unproved local-step assumption: Q safety, totality, legality and
successor classification are all obtained from the concrete W/V proofs above. -/
theorem pending_selected_step {H : Nat} {z : Board} (pending : FirstPending H z)
    {q : Col} (hq : Legal H z q) {o : Observation}
    (obs : Observes H (drop z q Q) o) :
    ¬ Wins H (drop z q Q) Q ∧
      (Full H (drop z q Q) ∨ ∃ p,
        select H (drop z q Q) q o = some p ∧ Legal H (drop z q Q) p ∧
          (Good H (afterRound z q p) ∨ FirstPending H (afterRound z q p))) := by
  have safe : ¬ Wins H (drop z q Q) Q := by
    rcases pending.2.2 with ⟨a,d,rfl,_,_⟩ | ⟨a,b,e,d,rfl,_⟩
    · exact w_Q_move_safe hq
    · exact v_Q_move_safe hq
  refine ⟨safe,?_⟩
  by_cases full : Full H (drop z q Q)
  · exact Or.inl full
  · rcases select_total_legal (o := o) (q := q)
        (drop_bounded (pending_state_safe pending).1 hq Q) full with ⟨p,chosen,legal⟩
    exact Or.inr ⟨p,chosen,legal,(pending_selected_closed pending hq full obs chosen).2⟩

#print axioms root_first_scores
#print axioms fallback_root_first
#print axioms w_select_closed
#print axioms pending_selected_step
end UniformFour.U2
