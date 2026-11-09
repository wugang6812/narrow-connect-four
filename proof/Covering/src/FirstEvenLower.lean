import FirstInnerLower
import ReflectionKernel

/-! Reviewed copy. Reflects the actual-board finite counterstrategy, not the U2
implementation or its tie breaking. Covers all four first opening columns. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col
open Connect4.NarrowBoards.OddHeightDraft

abbrev mirrorBoard (b : OddHeight.Board) : OddHeight.Board := logicalBoard true b

theorem mirror_drop_U1 (b : OddHeight.Board) (c : Col) (p : OddHeight.Player) :
    mirrorBoard (drop b c p) = drop (mirrorBoard b) (mirror c) p := by
  funext d
  cases c <;> cases d <;> simp [mirrorBoard, logicalBoard, orient, mirror, drop]

@[simp] theorem mirror_legal_U1 (H : Nat) (b : OddHeight.Board) (c : Col) :
    OddHeight.Legal H (mirrorBoard b) (mirror c) ↔ OddHeight.Legal H b c := by
  simp [OddHeight.Legal, height, mirrorBoard, logicalBoard, orient]

theorem mirror_full_U1 (H : Nat) (b : OddHeight.Board) :
    Full H (mirrorBoard b) ↔ Full H b := by
  constructor
  · intro full c
    simpa [height, mirrorBoard, logicalBoard, orient] using full (mirror c)
  · intro full c
    simpa [height, mirrorBoard, logicalBoard, orient] using full (mirror c)

@[simp] theorem mirror_cost_U1 (H : Nat) (b : OddHeight.Board) (q c : Col) :
    activeCost H (mirrorBoard b) (mirror q) (mirror c) = activeCost H b q c := by
  have injective : mirror c = mirror q ↔ c = q := by
    constructor
    · intro eq
      simpa using congrArg mirror eq
    · exact congrArg mirror
  simp [activeCost, injective]

theorem ZeroTrap.reflected {H n : Nat} {b : OddHeight.Board}
    (trap : ZeroTrap H n b) : ZeroTrap H n (mirrorBoard b) := by
  induction trap with
  | @hit b n q noP legal win =>
    apply ZeroTrap.hit (mirror q)
    · intro mirroredWin
      exact noP ((wins_logicalBoard_iff H b P).1 mirroredWin)
    · exact (mirror_legal_U1 H b q).2 legal
    · rw [← mirror_drop_U1]
      exact wins_logicalBoard win
  | @branch b n q noP legal notFull children ih =>
    apply ZeroTrap.branch (mirror q)
    · intro mirroredWin
      exact noP ((wins_logicalBoard_iff H b P).1 mirroredWin)
    · exact (mirror_legal_U1 H b q).2 legal
    · rw [← mirror_drop_U1]
      intro full
      exact notFull ((mirror_full_U1 H (drop b q Q)).1 full)
    · intro c hc zero
      rw [← mirror_drop_U1] at hc zero
      have legalOriginal : OddHeight.Legal H (drop b q Q) (mirror c) := by
        apply (mirror_legal_U1 H (drop b q Q) (mirror c)).1
        simpa only [mirror_mirror] using hc
      have costOriginal : activeCost H (drop b q Q) q (mirror c) = 0 := by
        have eq := mirror_cost_U1 H (drop b q Q) q (mirror c)
        simp only [mirror_mirror] at eq
        rw [eq] at zero
        exact zero
      have tail := ih (mirror c) legalOriginal costOriginal
      simpa only [mirror_drop_U1, mirror_mirror] using tail

/-- Every opening column admits an actual finite zero-budget counterstrategy. -/
theorem first_even_trap {m : Nat} (hm : 2 ≤ m) (opening : Col) :
    ∃ n, ZeroTrap (2*m) n (drop OddHeight.empty opening P) := by
  have outer := outer_prepare_transport hm ⟨3,outerPrepared_trap hm⟩
  have inner := inner_prepare_transport hm ⟨m,innerPrepared_trap hm⟩
  cases opening with
  | c1 =>
    obtain ⟨n,trap⟩ := outer
    refine ⟨n, ?_⟩
    have eq : drop OddHeight.empty c1 P = firstBoard := by
      funext c; cases c <;> simp [drop, OddHeight.empty, firstBoard, board]
    simpa only [eq] using trap
  | c2 =>
    obtain ⟨n,trap⟩ := inner
    refine ⟨n, ?_⟩
    have eq : drop OddHeight.empty c2 P = board [] [P] [] [] := by
      funext c; cases c <;> simp [drop, OddHeight.empty, board]
    simpa only [eq] using trap
  | c3 =>
    obtain ⟨n,trap⟩ := inner
    refine ⟨n, ?_⟩
    have eq : mirrorBoard (board [] [P] [] []) = drop OddHeight.empty c3 P := by
      funext c
      cases c <;> simp [mirrorBoard, logicalBoard, orient, mirror, drop, OddHeight.empty, board]
    simpa only [eq] using trap.reflected
  | c4 =>
    obtain ⟨n,trap⟩ := outer
    refine ⟨n, ?_⟩
    have eq : mirrorBoard firstBoard = drop OddHeight.empty c4 P := by
      funext c
      cases c <;> simp [mirrorBoard, logicalBoard, orient, mirror, drop,
        OddHeight.empty, firstBoard, board]
    simpa only [eq] using trap.reflected

/-- U1's complete even-height first-player zero-budget obstruction, in the
BudgetSemantics actual four-column Board model, for any history-sized state. -/
theorem first_even_zero_budget_impossible {S : Type} {H : Nat}
    (even : H % 2 = 0) (height : 4 ≤ H)
    (f : Controller S) (s : S) (opening : Col) :
    ¬ BudgetSafe H f 0 (drop OddHeight.empty opening P) s := by
  have hm : 2 ≤ H/2 := by omega
  have decomposition : H = 2*(H/2) := by omega
  obtain ⟨n,trap⟩ := first_even_trap hm opening
  rw [← decomposition] at trap
  exact zeroTrap_not_budgetSafe trap f s

#print axioms first_even_trap
#print axioms first_even_zero_budget_impossible
end UniformFour.U1
