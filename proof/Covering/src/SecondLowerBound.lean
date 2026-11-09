import BudgetSemantics

/-!
Reviewed candidate, 2026-11-08. Place this file and BudgetSemantics.lean at
one Lean source root alongside the frozen OddHeight and UniformFour libraries.
No U2-specific choice, invariant, or upper-bound theorem is assumed.
-/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col

private def t0 : Board := board [] [] [] []
private def t1 : Board := board [Q,P] [] [] []
private def t2 : Board := board [Q,P] [Q,P] [] []
private def t3 : Board := board [Q,P] [Q,P] [Q,P] []

private theorem pair_P_row {b : Board}
    (pairs : ∀ c, b c = [] ∨ b c = [Q,P]) {c : Col} {r : Nat}
    (hp : stoneAt b ⟨c,r⟩ = some P) : r = 2 := by
  rcases pairs c with empty | pair
  · simp [stoneAt, empty] at hp
  · cases r with
    | zero => simp [stoneAt] at hp
    | succ r =>
      cases r with
      | zero => simp [stoneAt, pair] at hp
      | succ r =>
        cases r with
        | zero => rfl
        | succ r => simp [stoneAt, pair] at hp

/-- With an empty fourth column, only vertical wins require checking.
In each pair-column the defender has only its row-two stone. -/
private theorem pairs_no_P {H : Nat} {b : Board}
    (pairs : ∀ c, b c = [] ∨ b c = [Q,P]) (lastEmpty : b c4 = []) :
    ¬ Wins H b P := by
  rintro ⟨L, _, stones⟩
  cases L with
  | horizontal r =>
    have h := stones ⟨c4,r⟩ (by simp [Line.cells])
    simp [stoneAt, lastEmpty] at h
  | rising r =>
    have h := stones ⟨c4,r+3⟩ (by simp [Line.cells])
    simp [stoneAt, lastEmpty] at h
  | falling r =>
    have h := stones ⟨c4,r-3⟩ (by simp [Line.cells])
    simp [stoneAt, lastEmpty] at h
  | vertical c r =>
    have a := pair_P_row pairs (stones ⟨c,r⟩ (by simp [Line.cells]))
    have d := pair_P_row pairs (stones ⟨c,r+1⟩ (by simp [Line.cells]))
    omega

private theorem t0_no_P (H : Nat) : ¬ Wins H t0 P := by
  apply pairs_no_P
  · intro c; cases c <;> simp [t0, board]
  · rfl
private theorem t1_no_P (H : Nat) : ¬ Wins H t1 P := by
  apply pairs_no_P
  · intro c; cases c <;> simp [t1, board]
  · rfl
private theorem t2_no_P (H : Nat) : ¬ Wins H t2 P := by
  apply pairs_no_P
  · intro c; cases c <;> simp [t2, board]
  · rfl
private theorem t3_no_P (H : Nat) : ¬ Wins H t3 P := by
  apply pairs_no_P
  · intro c; cases c <;> simp [t3, board]
  · rfl

/-- At zero budget a nonfull last column forces the unique physical reply.
The control state remains completely arbitrary and may remember full history. -/
private theorem forced_cover_tail {S : Type} {H k : Nat} {f : Controller S}
    {b : Board} {s : S} {q : Col}
    (safe : BudgetRoundSafe H f (k+1) 0 b s)
    (noP : ¬ Wins H b P) (legalQ : Legal H b q)
    (canCover : Legal H (drop b q Q) q) :
    ∃ next, BudgetRoundSafe H f k 0 (drop (drop b q Q) q P) next := by
  have notFull : ¬ Full H b := by
    intro h
    have heq := h q
    unfold Legal at legalQ
    omega
  have notFullQ : ¬ Full H (drop b q Q) := by
    intro h
    have heq := h q
    unfold Legal at canCover
    omega
  rcases safe.2 with win | full | moves
  · exact False.elim (noP win)
  · exact False.elim (notFull full)
  · rcases (moves q legalQ).2 with full | ⟨c,next,_,_,cost,tail⟩
    · exact False.elim (notFullQ full)
    · have zero : activeCost H (drop b q Q) q c = 0 := by omega
      have eq := zero_cost_forces_cover canCover zero
      subst c
      exact ⟨next, by simpa using tail⟩

private theorem fourth_Q_win {H : Nat} (h : 2 ≤ H) :
    Wins H (drop t3 c4 Q) Q := by
  refine ⟨Line.horizontal 1, ?_, ?_⟩
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [InBoard] <;> omega
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [stoneAt, drop, t3, board]

/-- Four opponent moves suffice to refute EVERY zero-budget second-player
controller, including all history-dependent policies represented by arbitrary S.
This root has no safety/certificate/oracle assumptions. H=2 is included. -/
theorem second_zero_budget_four_rounds_impossible {S : Type} {H : Nat}
    (height : 2 ≤ H) (f : Controller S) (s : S) :
    ¬ BudgetRoundSafe H f 4 0 OddHeight.empty s := by
  intro safe
  have h0 : BudgetRoundSafe H f 4 0 t0 s := safe
  have l0 : Legal H t0 c1 := by simp [Legal, OddHeight.height, t0, board]; omega
  have c0 : Legal H (drop t0 c1 Q) c1 := by
    simp [Legal, OddHeight.height, drop, t0, board]; omega
  obtain ⟨s1,h1⟩ := forced_cover_tail h0 (t0_no_P H) l0 c0
  have eq1 : drop (drop t0 c1 Q) c1 P = t1 := by
    funext c; cases c <;> simp [drop, t0, t1, board]
  rw [eq1] at h1
  have l1 : Legal H t1 c2 := by simp [Legal, OddHeight.height, t1, board]; omega
  have c1' : Legal H (drop t1 c2 Q) c2 := by
    simp [Legal, OddHeight.height, drop, t1, board]; omega
  obtain ⟨s2,h2⟩ := forced_cover_tail h1 (t1_no_P H) l1 c1'
  have eq2 : drop (drop t1 c2 Q) c2 P = t2 := by
    funext c; cases c <;> simp [drop, t1, t2, board]
  rw [eq2] at h2
  have l2 : Legal H t2 c3 := by simp [Legal, OddHeight.height, t2, board]; omega
  have c2' : Legal H (drop t2 c3 Q) c3 := by
    simp [Legal, OddHeight.height, drop, t2, board]; omega
  obtain ⟨s3,h3⟩ := forced_cover_tail h2 (t2_no_P H) l2 c2'
  have eq3 : drop (drop t2 c3 Q) c3 P = t3 := by
    funext c; cases c <;> simp [drop, t2, t3, board]
  rw [eq3] at h3
  have l3 : Legal H t3 c4 := by simp [Legal, OddHeight.height, t3, board]; omega
  rcases h3.2 with win | full | moves
  · exact t3_no_P H win
  · have heq := full c4
    have hz : OddHeight.height t3 c4 = 0 := rfl
    omega
  · exact (moves c4 l3).1 (fourth_Q_win height)

theorem second_zero_budget_impossible {S : Type} {H : Nat}
    (height : 2 ≤ H) (f : Controller S) (s : S) :
    ¬ BudgetSafe H f 0 OddHeight.empty s := by
  intro safe
  exact second_zero_budget_four_rounds_impossible height f s (safe 4)

#print axioms second_zero_budget_four_rounds_impossible
#print axioms second_zero_budget_impossible
end UniformFour.U1
