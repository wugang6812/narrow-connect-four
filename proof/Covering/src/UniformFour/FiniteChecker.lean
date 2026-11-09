import UniformFour.Observations

/-!
An actual finite, computable reference checker for U2. Reviewed copy.
No Classical.propDecidable, strategy oracle, or new axiom is used. The slow
reference enumerates finitely many lines/targets; optimization is separate.
-/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

deriving instance ReflBEq, LawfulBEq for Col
deriving instance ReflBEq, LawfulBEq for Cell

private def transportDecision (p q : Prop) (equiv : p ↔ q) [Decidable p] : Decidable q :=
  match (inferInstance : Decidable p) with
  | isTrue h => isTrue (equiv.mp h)
  | isFalse h => isFalse (fun hq => h (equiv.mpr hq))

instance decidableForallCol (P : Col → Prop) [DecidablePred P] : Decidable (∀ c, P c) :=
  transportDecision (P c1 ∧ P c2 ∧ P c3 ∧ P c4) _
    ⟨fun h c => by
       cases c with
       | c1 => exact h.1
       | c2 => exact h.2.1
       | c3 => exact h.2.2.1
       | c4 => exact h.2.2.2,
     fun h => ⟨h c1, h c2, h c3, h c4⟩⟩

instance decidableInBoard (H : Nat) (x : Cell) : Decidable (InBoard H x) := by
  unfold InBoard
  infer_instance
instance decidableValidLine (H : Nat) (L : Line) : Decidable (ValidLine H L) := by
  unfold ValidLine
  infer_instance
instance decidableNonvertical (L : Line) : Decidable L.Nonvertical := by
  cases L <;> unfold Line.Nonvertical <;> infer_instance
instance decidableHasP (b : Board) (L : Line) : Decidable (HasP b L) := by
  unfold HasP
  infer_instance
instance decidableException (H : Nat) (b : Board) (x : Cell) :
    Decidable (exceptionSet H b x) := by
  unfold exceptionSet existingException potentialException
  infer_instance
instance decidableToCheckExact (H : Nat) (b : Board) (L : Line) :
    Decidable (ToCheck H (exceptionSet H b) L) := by
  unfold ToCheck
  infer_instance
instance decidableUnresolved (H : Nat) (b : Board) (L : Line) :
    Decidable (Unresolved H b L) := by
  unfold Unresolved
  infer_instance
instance decidableLegal (H : Nat) (b : Board) (c : Col) : Decidable (Legal H b c) := by
  unfold Legal
  infer_instance
instance decidableBounded (H : Nat) (b : Board) : Decidable (Bounded H b) := by
  unfold Bounded
  infer_instance
instance decidableFull (H : Nat) (b : Board) : Decidable (Full H b) := by
  unfold Full
  infer_instance
instance decidableTopRun (H : Nat) (b : Board) : Decidable (TopRunAtMostTwo H b) := by
  unfold TopRunAtMostTwo
  infer_instance

/-- Some entries are invalid; the ValidLine test filters them. Every valid line
has its constructor's initial row in 0..H, including falling lines. -/
def allLines (H : Nat) : List Line :=
  (List.range (H + 1)).flatMap fun r =>
    [.horizontal r, .rising r, .falling r] ++ allCols.map (fun c => .vertical c r)

theorem valid_mem_allLines {H : Nat} {L : Line} (h : ValidLine H L) : L ∈ allLines H := by
  cases L with
  | horizontal r =>
      have roof : r ≤ H := (h ⟨c1,r⟩ (by simp [Line.cells])).2
      apply List.mem_flatMap.mpr
      refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
      simp
  | rising r =>
      have roof : r ≤ H := (h ⟨c1,r⟩ (by simp [Line.cells])).2
      apply List.mem_flatMap.mpr
      refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
      simp
  | falling r =>
      have roof : r ≤ H := (h ⟨c1,r⟩ (by simp [Line.cells])).2
      apply List.mem_flatMap.mpr
      refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
      simp
  | vertical c r =>
      have roof : r ≤ H := (h ⟨c,r⟩ (by simp [Line.cells])).2
      apply List.mem_flatMap.mpr
      refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
      cases c <;> simp [allCols]

theorem wins_finite_iff (H : Nat) (b : Board) (p : Player) :
    (∃ L ∈ allLines H, ValidLine H L ∧ ∀ x ∈ L.cells, stoneAt b x = some p) ↔
      Wins H b p := by
  constructor
  · rintro ⟨L, _, valid, stones⟩
    exact ⟨L, valid, stones⟩
  · rintro ⟨L, valid, stones⟩
    exact ⟨L, valid_mem_allLines valid, valid, stones⟩

instance decidableWins (H : Nat) (b : Board) (p : Player) : Decidable (Wins H b p) :=
  transportDecision _ _ (wins_finite_iff H b p)

instance decidableLive (H : Nat) (b : Board) : Decidable (Live H b) := by
  unfold Live
  infer_instance
instance decidableCommon (H : Nat) (b : Board) : Decidable (Common H b) := by
  unfold Common
  infer_instance

/-- Turn a universal obligation over unresolved lines into a finite list check. -/
theorem checkedAll_finite_iff (H : Nat) (b : Board) (pred : Line → Prop) :
    (∀ L ∈ allLines H, Unresolved H b L → pred L) ↔
      (∀ L, Unresolved H b L → pred L) := by
  constructor
  · intro h L hu
    exact h L (valid_mem_allLines hu.1.1) hu
  · intro h L _ hu
    exact h L hu

private def checkedAllDecision (H : Nat) (b : Board) (pred : Line → Prop)
    [DecidablePred pred] : Decidable (∀ L, Unresolved H b L → pred L) :=
  transportDecision _ _ (checkedAll_finite_iff H b pred)

instance decidableA0 (H : Nat) (b : Board) : Decidable (A0 H b) :=
  transportDecision (∀ L ∈ allLines H, ¬ Unresolved H b L) _
    ⟨fun h L hu => h L (valid_mem_allLines hu.1.1) hu,
     fun h L _ => h L⟩

instance decidableTargetCondition (H : Nat) (b : Board) (t : Target) :
    Decidable (TargetCondition H b t) :=
  transportDecision
    (InBoard H (targetCell t) ∧ stoneAt b (targetCell t) = none ∧
      height b t.col < t.row ∧ (t.row - height b t.col) % 2 = 0 ∧
      outsideTarget H b t % 2 = 0) _
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
     fun h => ⟨h.inBoard, h.empty, h.positive, h.evenGap, h.outsideEven⟩⟩

instance decidableA1Data (H : Nat) (b : Board) (t : Target) : Decidable (A1Data H b t) := by
  letI := checkedAllDecision H b (fun L => targetCell t ∈ L.cells)
  exact transportDecision
    (TargetCondition H b t ∧ ∀ L, Unresolved H b L → targetCell t ∈ L.cells) _
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.target, h.commonTarget⟩⟩

theorem fixedWinningTarget_finite_iff (H : Nat) (b : Board) (t : Target) :
    (∃ L ∈ allLines H, ValidLine H L ∧ targetCell t ∈ L.cells ∧
      ∀ x ∈ L.cells, x ≠ targetCell t → stoneAt b x = some P) ↔
    FixedWinningTarget H b t := by
  constructor
  · rintro ⟨L, _, hv, ht, fixed⟩
    exact ⟨L, hv, ht, fixed⟩
  · rintro ⟨L, hv, ht, fixed⟩
    exact ⟨L, valid_mem_allLines hv, hv, ht, fixed⟩

instance decidableFixedWinningTarget (H : Nat) (b : Board) (t : Target) :
    Decidable (FixedWinningTarget H b t) :=
  transportDecision _ _ (fixedWinningTarget_finite_iff H b t)

instance decidableA2Data (H : Nat) (b : Board) (t : Target) : Decidable (A2Data H b t) := by
  letI := checkedAllDecision H b
    (fun L => ∃ x ∈ L.cells, x.col = t.col ∧ t.row ≤ x.row)
  exact transportDecision
    (TargetCondition H b t ∧ FixedWinningTarget H b t ∧
      ∀ L, Unresolved H b L → ∃ x ∈ L.cells, x.col = t.col ∧ t.row ≤ x.row) _
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
     fun h => ⟨h.target, h.fixedWin, h.commonUpperColumn⟩⟩

def allTargets (H : Nat) : List Target :=
  allCols.flatMap fun c => (List.range (H + 1)).map (fun r => ⟨c,r⟩)

theorem target_mem_allTargets {H : Nat} {t : Target} (h : t.row ≤ H) :
    t ∈ allTargets H := by
  apply List.mem_flatMap.mpr
  refine ⟨t.col, ?_, ?_⟩
  · cases t.col <;> simp [allCols]
  · apply List.mem_map.mpr
    exact ⟨t.row, List.mem_range.mpr (by omega), by cases t; rfl⟩

instance decidableA1 (H : Nat) (b : Board) : Decidable (A1 H b) :=
  transportDecision (∃ t ∈ allTargets H, A1Data H b t) _
    ⟨fun ⟨t, _, h⟩ => ⟨t, h⟩,
     fun ⟨t, h⟩ => ⟨t, target_mem_allTargets h.target.inBoard.2, h⟩⟩
instance decidableA2 (H : Nat) (b : Board) : Decidable (A2 H b) :=
  transportDecision (∃ t ∈ allTargets H, A2Data H b t) _
    ⟨fun ⟨t, _, h⟩ => ⟨t, h⟩,
     fun ⟨t, h⟩ => ⟨t, target_mem_allTargets h.target.inBoard.2, h⟩⟩
instance decidableA (H : Nat) (b : Board) : Decidable (A H b) := by
  unfold A
  infer_instance
instance decidableOddColumn (H : Nat) (b : Board) (c : Col) : Decidable (OddColumn H b c) := by
  unfold OddColumn
  infer_instance
instance decidableProtected (H : Nat) (b : Board) (x : Cell) : Decidable (Protected H b x) := by
  unfold Protected
  infer_instance
instance decidableExitProtected (H : Nat) (b : Board) (t : Col) (x : Cell) :
    Decidable (ExitProtected H b t x) := by
  unfold ExitProtected
  infer_instance

instance decidableB (H : Nat) (b : Board) : Decidable (B H b) := by
  letI := checkedAllDecision H b (fun L => ∃ x ∈ L.cells, Protected H b x)
  letI : ∀ t, Decidable (∀ L, Unresolved H b L →
      ∃ x ∈ L.cells, ExitProtected H b t x) :=
    fun t => checkedAllDecision H b (fun L => ∃ x ∈ L.cells, ExitProtected H b t x)
  exact transportDecision
    (((oddColumns H b).length = 0 ∨ (oddColumns H b).length = 2) ∧
      (∀ L, Unresolved H b L → ∃ x ∈ L.cells, Protected H b x) ∧
      (∀ f t, f ≠ t → OddColumn H b f → OddColumn H b t →
        ∀ L, Unresolved H b L → ∃ x ∈ L.cells, ExitProtected H b t x)) _
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
     fun h => ⟨h.zeroOrTwo, h.guards, h.bothOrderedExits⟩⟩

private theorem c_pattern_finite_iff (H : Nat) (b : Board) :
    ((∀ c, OddColumn H b c) ∧ b c2 = [] ∧ b c3 = [] ∧
      b c1 = alternatingPairs (height b c1 / 2) ∧
      b c4 = alternatingPairs (height b c4 / 2) ∧
      0 < height b c1 / 2 + height b c4 / 2) ↔ C H b := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1,
      height b c1 / 2, height b c4 / 2, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  · intro h
    rcases h.outerPattern with ⟨a, d, h1, h4, positive⟩
    have len1 : height b c1 = 2 * a := by simp [height, h1]
    have len4 : height b c4 = 2 * d := by simp [height, h4]
    have div1 : height b c1 / 2 = a := by omega
    have div4 : height b c4 / 2 = d := by omega
    exact ⟨h.fourOdd, h.middleTwo, h.middleThree,
      by simpa only [div1] using h1, by simpa only [div4] using h4,
      by simpa only [div1, div4] using positive⟩

instance decidableC (H : Nat) (b : Board) : Decidable (C H b) :=
  transportDecision _ _ (c_pattern_finite_iff H b)
instance decidableCertificate (H : Nat) (b : Board) : Decidable (Certificate H b) := by
  unfold Certificate
  infer_instance
instance decidableSafeTerminal (H : Nat) (b : Board) : Decidable (SafeTerminal H b) := by
  unfold SafeTerminal
  infer_instance
instance decidableGood (H : Nat) (b : Board) : Decidable (Good H b) := by
  unfold Good
  infer_instance
instance decidableQualified (H : Nat) (a : Board) (c : Col) : Decidable (Qualified H a c) := by
  unfold Qualified
  infer_instance
instance decidableBothCorners (a : Board) : Decidable (BothCorners a) := by
  unfold BothCorners
  infer_instance

/-- Slow finite reference implementation. It contains no history/phase state. -/
def referenceObservation (H : Nat) (a : Board) : Observation where
  qualified := fun c => decide (Qualified H a c)
  immediate := fun c => decide (Wins H (drop a c P) P)
  bottomScore := bottomScore H a
  bothCorners := decide (BothCorners a)

theorem referenceObserves (H : Nat) (a : Board) :
    Observes H a (referenceObservation H a) := by
  constructor
  · intro c
    simp only [referenceObservation, decide_eq_true_eq]
  · intro c
    simp only [referenceObservation, decide_eq_true_eq]
  · intro c
    rfl
  · simp only [referenceObservation, decide_eq_true_eq]

/-- One shared response for both roles and every finite height. First-win stopping
    is provided by the driver/Controller semantics, not by hidden phase state. -/
def respond (H : Nat) : StatelessResponse :=
  fun a q => select H a q (referenceObservation H a)

#print axioms referenceObserves
end UniformFour.U2
