import FirstTrapKernel

/-! Reviewed copy: complete outer-opening zero-budget counterstrategy candidate. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col

private theorem get_append_self (xs : List Player) (i : Nat) :
    (xs ++ [P])[i]? = some P ↔ xs[i]? = some P ∨ i = xs.length := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

@[simp] theorem read_append_P_P_U1 (xs : List Player) (r : Nat) :
    readRow (xs ++ [P]) r = some P ↔
      readRow xs r = some P ∨ r = xs.length+1 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
    change (xs ++ [P])[r]? = some P ↔ xs[r]? = some P ∨ r+1 = xs.length+1
    rw [get_append_self]
    constructor
    · rintro (old | new)
      · exact Or.inl old
      · exact Or.inr (by omega)
    · rintro (old | new)
      · exact Or.inl old
      · exact Or.inr (by omega)

@[simp] theorem read_append_Q_P_U1 (xs : List Player) (r : Nat) :
    readRow (xs ++ [Q]) r = some P ↔ readRow xs r = some P := by
  constructor
  · intro h
    exact stoneAt_drop_other_colour (b := fun _ => xs) (x := ⟨c1,r⟩)
      (by decide : P ≠ Q) c1 h
  · intro h
    exact stoneAt_drop_preserves (b := fun _ => xs) (x := ⟨c1,r⟩) h c1 Q

def outerWait (m : Nat) : Board := drop (outerEndpoint m) c4 P
def outerDelayed (m : Nat) : Board := drop (drop (outerWait m) c4 Q) c3 P

theorem outerDirect_no_P {m : Nat} (hm : 2 ≤ m) :
    ¬ Wins (2*m) (drop (outerEndpoint m) c3 P) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r-2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega

theorem outerWait_no_P {m : Nat} (hm : 2 ≤ m) :
    ¬ Wins (2*m) (outerWait m) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r-2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega

theorem outerDelayed_no_P {m : Nat} (hm : 2 ≤ m) :
    ¬ Wins (2*m) (outerDelayed m) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r-2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c
    all_goals simp_all [outerWait, outerDelayed, outerEndpoint, drop, board,
      ← List.append_assoc] <;> omega

/-- In the delayed branch the extra c4 moves leave the winning falling line
untouched: its c4 stone is at the already occupied bottom square. -/
theorem outerDelayed_win {m : Nat} (hm : 2 ≤ m) :
    Wins (2*m) (drop (outerDelayed m) c3 Q) Q := by
  have original := outerEndpoint_finish hm
  have extended := wins_drop_preserves
    (wins_drop_preserves original c4 P) c4 Q
  have eq : drop (drop (drop (drop (outerEndpoint m) c3 P) c3 Q) c4 P) c4 Q =
      drop (outerDelayed m) c3 Q := by
    funext c
    cases c <;> simp [outerDelayed, outerWait, drop]
  rw [eq] at extended
  exact extended

theorem outerWait_trap {m : Nat} (hm : 2 ≤ m) :
    ZeroTrap (2*m) 2 (outerWait m) := by
  apply ZeroTrap.branch c4 (outerWait_no_P hm)
  · simp [Legal, height, outerWait, outerEndpoint, drop, board]
    omega
  · intro full
    have eq := full c3
    simp [height, outerWait, outerEndpoint, drop, board] at eq
    omega
  · intro c hc _
    have only : c = c3 := by
      cases c <;> simp_all [Legal, height, outerWait, outerEndpoint, drop, board] <;> omega
    subst c
    apply ZeroTrap.hit c3 (outerDelayed_no_P hm)
    · simp [Legal, height, outerDelayed, outerWait, outerEndpoint, drop, board]
      omega
    · exact outerDelayed_win hm

theorem outerPrepared_trap {m : Nat} (hm : 2 ≤ m) :
    ZeroTrap (2*m) 3 (outerPrepared m) := by
  apply ZeroTrap.branch c1
  · intro win
    apply outerEndpoint_no_P hm
    rw [← outer_preparation_shape m]
    exact wins_drop_preserves win c1 Q
  · simp [Legal, height, outerPrepared, coverBlock_column, firstBoard, board]
    omega
  · rw [outer_preparation_shape]
    intro full
    have eq := full c3
    simp [height, outerEndpoint, board] at eq
    omega
  · rw [outer_preparation_shape]
    intro c hc _
    rcases (outerEndpoint_choices hm c).1 hc with rfl | rfl
    · apply ZeroTrap.hit c3 (outerDirect_no_P hm)
      · simp [Legal, height, drop, outerEndpoint, board]
        omega
      · exact outerEndpoint_finish hm
    · exact outerWait_trap hm

/-- All stateful zero-budget controllers lose from the c1 first-player opening
on every even height at least four. No safety oracle is accepted. -/
theorem first_outer_zero_budget_impossible {S : Type} {m : Nat}
    (hm : 2 ≤ m) (f : Controller S) (s : S) :
    ¬ BudgetSafe (2*m) f 0 firstBoard s := by
  obtain ⟨n,trap⟩ := outer_prepare_transport hm ⟨3,outerPrepared_trap hm⟩
  exact zeroTrap_not_budgetSafe trap f s

#print axioms first_outer_zero_budget_impossible
end UniformFour.U1
