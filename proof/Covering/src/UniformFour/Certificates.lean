import OddHeight.Permanent
import OddHeight.Arithmetic

/-!
# U2 certificates, exact geometric layer

Reviewed additive copy. See audit.json and kernel_audit.json for validation.
This file does not edit the frozen v2 sources and does not identify the U2
algorithm with v2's I/E/Delay controller.

Source: `uniform_local_rule_supplement/supplement_U2.md`, Sections 2 and 3.
Rows are one-based. In this relative-colour layer P is the side whose
certificate is being checked, and Q is the other side. This is not a claim
that P is always the first player. A colour-normalization bridge is separate.

`A0`, `A1`, `A2`, `A`, `B`, and `C` are the geometric BODY predicates.
`Certificate` adds the common nonterminal/structural premises to every body.
All exceptions are recomputed as the exact `exceptionSet H b`, not a
previously chosen superset. No assertion of future safety or closure is a
field of any certificate.

The results below prove local opponent-move safety and the permanent A0
cover step, plus some capture/subset facts. They do not prove A1/A2/B/C
closure, the response algorithm, reachability, or global switch bounds.
-/

namespace UniformFour.U2

open OddHeight
open OddHeight.Player OddHeight.Col

/-- U2 Section 2.2: bottom/exception nonvertical lines not already P-blocked. -/
def Unresolved (H : Nat) (b : Board) (L : Line) : Prop :=
  ToCheck H (exceptionSet H b) L ∧ ¬ HasP b L

/-- Shared premises apply only after P's response, before the next Q move. -/
def Common (H : Nat) (b : Board) : Prop :=
  Live H b ∧ TopRunAtMostTwo H b

/-- A0's body says precisely that U is empty. -/
def A0 (H : Nat) (b : Board) : Prop :=
  ∀ L, ¬ Unresolved H b L

/-- One target column is excluded from the finite outside-capacity sum. -/
def outsideTarget (H : Nat) (b : Board) (t : Target) : Nat :=
  outside H b [t]

/-- The common target conditions of A1 and A2, all checked on the current board. -/
structure TargetCondition (H : Nat) (b : Board) (t : Target) : Prop where
  inBoard : InBoard H (targetCell t)
  empty : stoneAt b (targetCell t) = none
  positive : height b t.col < t.row
  evenGap : (t.row - height b t.col) % 2 = 0
  outsideEven : outsideTarget H b t % 2 = 0

/-- A1 uses ONE target common to EVERY unresolved line, not one target per line. -/
structure A1Data (H : Nat) (b : Board) (t : Target) : Prop where
  target : TargetCondition H b t
  commonTarget : ∀ L, Unresolved H b L → targetCell t ∈ L.cells

def A1 (H : Nat) (b : Board) : Prop := ∃ t, A1Data H b t

/-- A2 is a geometric completion with three CURRENT, FIXED P stones.
The target is on a valid four-cell line; all its other cells must already be P.
No intermediate empty cell is hypothetically filled, and this does not perform
a non-gravity move to the target. Valid lines have four distinct cells. -/
def FixedWinningTarget (H : Nat) (b : Board) (t : Target) : Prop :=
  ∃ L, ValidLine H L ∧ targetCell t ∈ L.cells ∧
    ∀ x ∈ L.cells, x ≠ targetCell t → stoneAt b x = some P

/-- Every unresolved line is guarded in the SAME target column at or above g. -/
structure A2Data (H : Nat) (b : Board) (t : Target) : Prop where
  target : TargetCondition H b t
  fixedWin : FixedWinningTarget H b t
  commonUpperColumn : ∀ L, Unresolved H b L →
    ∃ x ∈ L.cells, x.col = t.col ∧ t.row ≤ x.row

def A2 (H : Nat) (b : Board) : Prop := ∃ t, A2Data H b t

def A (H : Nat) (b : Board) : Prop := A0 H b ∨ A1 H b ∨ A2 H b

def OddColumn (H : Nat) (b : Board) (c : Col) : Prop :=
  (H - height b c) % 2 = 1

/-- `allCols` lists each of the four columns exactly once. -/
def oddColumns (H : Nat) (b : Board) : List Col :=
  allCols.filter (fun c => (H - height b c) % 2 == 1)

/-- U2's G: fixed P cells and in-board empty cells at positive even distance. -/
def Protected (H : Nat) (b : Board) (x : Cell) : Prop :=
  InBoard H x ∧
    (stoneAt b x = some P ∨
      (stoneAt b x = none ∧ height b x.col < x.row ∧
        (x.row - height b x.col) % 2 = 0))

/-- Exit protection removes ALL old G cells in target column t and adds (t,H). -/
def ExitProtected (H : Nat) (b : Board) (t : Col) (x : Cell) : Prop :=
  (Protected H b x ∧ x.col ≠ t) ∨ x = ⟨t, H⟩

/-- Section 3.2, including both ordered choices of the first-full odd column.
The universal quantifiers deliberately include (f,t) AND (t,f). -/
structure B (H : Nat) (b : Board) : Prop where
  zeroOrTwo : (oddColumns H b).length = 0 ∨ (oddColumns H b).length = 2
  guards : ∀ L, Unresolved H b L → ∃ x ∈ L.cells, Protected H b x
  bothOrderedExits : ∀ f t, f ≠ t → OddColumn H b f → OddColumn H b t →
    ∀ L, Unresolved H b L → ∃ x ∈ L.cells, ExitProtected H b t x

/-- Literal alternating even column (QP)^n; no I/E/Delay phase is introduced. -/
def alternatingPairs : Nat → List Player
  | 0 => []
  | n + 1 => alternatingPairs n ++ [Q, P]

/-- Section 3.3: empty middle columns, four odd remainders, and not BOTH outer
columns empty. Either outer column may be the nonempty one. -/
structure C (H : Nat) (b : Board) : Prop where
  fourOdd : ∀ c, OddColumn H b c
  middleTwo : b c2 = []
  middleThree : b c3 = []
  outerPattern : ∃ a d, b c1 = alternatingPairs a ∧
    b c4 = alternatingPairs d ∧ 0 < a + d

/-- The exact U2 certificate predicate; all three classes use the same common
premises, and the board is nonterminal before a certificate can be accepted. -/
def Certificate (H : Nat) (b : Board) : Prop :=
  Common H b ∧ (A H b ∨ B H b ∨ C H b)

/-! ## Exact-exception bridges to frozen v2 -/

theorem exact_exception_complete (H : Nat) (b : Board) :
    ExceptionComplete H b (exceptionSet H b) := by
  intro x hx
  exact hx

theorem common_structural {H : Nat} {b : Board} (h : Common H b) :
    Structural H b (exceptionSet H b) := by
  exact ⟨h.1.1, h.1.2.2.1, h.2, exact_exception_complete H b⟩

theorem toCheck_mono {H : Nat} {E F : Cell → Prop}
    (hEF : ∀ x, E x → F x) {L : Line} (h : ToCheck H E L) :
    ToCheck H F L := by
  rcases h with ⟨hv, hn, x, hx, hb | he⟩
  · exact ⟨hv, hn, x, hx, Or.inl hb⟩
  · exact ⟨hv, hn, x, hx, Or.inr (hEF x he)⟩

theorem a0_iff_all_checked_blocked {H : Nat} {b : Board} :
    A0 H b ↔ ∀ L, ToCheck H (exceptionSet H b) L → HasP b L := by
  classical
  constructor
  · intro h L hL
    apply Classical.byContradiction
    intro hn
    exact h L ⟨hL, hn⟩
  · intro h L hL
    exact hL.2 (h L hL.1)

/-- Any v2 permanent witness blocks U2's exact U, even if its E was larger. -/
theorem a0_of_permanent {H : Nat} {b : Board} (h : PermanentHyp H b) :
    A0 H b := by
  rcases h with ⟨E, h⟩
  apply a0_iff_all_checked_blocked.mpr
  intro L hL
  exact h.blocked L (toCheck_mono h.structural.complete hL)

/-- The converse needs only current structure, not no-P-win or nonfullness.
This is an A0 bridge, NOT an equivalence for the new A1/A2/B/C certificates. -/
theorem a0_iff_permanent_of_structural {H : Nat} {b : Board}
    (hs : Structural H b (exceptionSet H b)) :
    A0 H b ↔ PermanentHyp H b := by
  constructor
  · intro h
    exact ⟨exceptionSet H b, hs, a0_iff_all_checked_blocked.mp h⟩
  · exact a0_of_permanent

theorem a0_iff_permanent {H : Nat} {b : Board} (h : Common H b) :
    A0 H b ↔ PermanentHyp H b :=
  a0_iff_permanent_of_structural (common_structural h)

/-- Recomputing U after a cover-or-full round can only REMOVE lines.
There is no certificate-closure assumption here. -/
theorem unresolved_after_cover_subset {H : Nat} {b : Board} {q p : Col}
    (hq : Legal H b q)
    (cover : p = q ∨ height (drop b q Q) q = H) {L : Line}
    (hL : Unresolved H (drop (drop b q Q) p P) L) :
    Unresolved H b L := by
  have complete := exceptionComplete_after_cover
    (exact_exception_complete H b) hq cover
  refine ⟨toCheck_mono complete hL.1, ?_⟩
  intro hp
  exact hL.2 (hasP_drop_preserves (hasP_drop_preserves hp q Q) p P)

/-! ## Elementary guard and capture facts -/

theorem cell_empty_above_height {b : Board} {x : Cell}
    (hx : height b x.col < x.row) : stoneAt b x = none := by
  cases hs : stoneAt b x with
  | none => rfl
  | some p =>
      have hb := (stoneAt_row_le hs).2
      omega

theorem height_after_move_le (b : Board) (q c : Col) (s : Player) :
    height (drop b q s) c ≤ height b c + 1 := by
  by_cases he : c = q
  · subst c
    simp
  · simp [height, drop, he]

theorem target_room {H : Nat} {b : Board} {t : Target}
    (h : TargetCondition H b t) : height b t.col + 2 ≤ t.row := by
  exact (positive_even_gap_room H (height b t.col) t.row
    h.positive h.evenGap h.inBoard.2).1

/-- A target, and every higher cell in its column, stays empty after one Q move. -/
theorem target_upper_empty_after_Q {H : Nat} {b : Board} {t : Target}
    (h : TargetCondition H b t) (q : Col) {x : Cell}
    (hc : x.col = t.col) (hr : t.row ≤ x.row) :
    stoneAt (drop b q Q) x = none := by
  have room := target_room h
  have raised := height_after_move_le b q t.col Q
  apply cell_empty_above_height
  rw [hc]
  omega

theorem target_empty_after_Q {H : Nat} {b : Board} {t : Target}
    (h : TargetCondition H b t) (q : Col) :
    stoneAt (drop b q Q) (targetCell t) = none :=
  target_upper_empty_after_Q h q rfl (Nat.le_refl t.row)

/-- Every G-cell is still either empty or P-owned after the opponent's move. -/
theorem protected_not_Q_after_move {H : Nat} {b : Board} {x : Cell}
    (h : Protected H b x) (q : Col) :
    stoneAt (drop b q Q) x ≠ some Q := by
  rcases h.2 with hp | ⟨_, hpos, heven⟩
  · have keep := stoneAt_drop_preserves hp q Q
    intro hq
    rw [keep] at hq
    cases hq
  · have room : height b x.col + 2 ≤ x.row := by omega
    have raised := height_after_move_le b q x.col Q
    have empty : stoneAt (drop b q Q) x = none :=
      cell_empty_above_height (by omega)
    intro hq
    rw [empty] at hq
    cases hq

/-- Explicitly extract the two ordered exit checks. Neither is discarded. -/
theorem b_two_exit_checks {H : Nat} {b : Board} (h : B H b) {f t : Col}
    (hne : f ≠ t) (hf : OddColumn H b f) (ht : OddColumn H b t) :
    (∀ L, Unresolved H b L → ∃ x ∈ L.cells, ExitProtected H b t x) ∧
    (∀ L, Unresolved H b L → ∃ x ∈ L.cells, ExitProtected H b f x) := by
  exact ⟨h.bothOrderedExits f t hne hf ht,
    h.bothOrderedExits t f (Ne.symm hne) ht hf⟩

theorem odd_column_top_empty {H : Nat} {b : Board} {t : Col}
    (h : OddColumn H b t) :
    Legal H b t ∧ InBoard H ⟨t, H⟩ ∧ stoneAt b ⟨t, H⟩ = none := by
  unfold OddColumn at h
  have hlt : height b t < H := by omega
  refine ⟨hlt, ⟨show 1 ≤ H from by omega, Nat.le_refl H⟩, ?_⟩
  exact cell_empty_above_height hlt

/-- Acquiring the common A1 target blocks all surviving unresolved lines. -/
theorem a1_capture_is_a0 {H : Nat} {b : Board} {t : Target} {q p : Col}
    (h : A1Data H b t) (hq : Legal H b q)
    (cover : p = q ∨ height (drop b q Q) q = H)
    (hit : stoneAt (drop (drop b q Q) p P) (targetCell t) = some P) :
    A0 H (drop (drop b q Q) p P) := by
  intro L hL
  have old := unresolved_after_cover_subset hq cover hL
  exact hL.2 ⟨targetCell t, h.commonTarget L old, hit⟩

/-- Acquiring an A2 target really wins, using ONLY its already fixed three stones. -/
theorem a2_capture_wins {H : Nat} {b : Board} {t : Target} (q p : Col)
    (h : A2Data H b t)
    (hit : stoneAt (drop (drop b q Q) p P) (targetCell t) = some P) :
    Wins H (drop (drop b q Q) p P) P := by
  rcases h.fixedWin with ⟨L, hv, _, fixed⟩
  refine ⟨L, hv, ?_⟩
  intro x hx
  by_cases he : x = targetCell t
  · simpa only [he] using hit
  · exact stoneAt_drop_preserves (stoneAt_drop_preserves (fixed x hx he) q Q) p P

@[simp] theorem alternatingPairs_length (n : Nat) :
    (alternatingPairs n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [alternatingPairs, ih] <;> omega

theorem c_not_both_outer_empty {H : Nat} {b : Board} (h : C H b) :
    ¬ (b c1 = [] ∧ b c4 = []) := by
  rcases h.outerPattern with ⟨a, d, h1, h4, hpos⟩
  rintro ⟨he1, he4⟩
  have len1 : 2 * a = 0 := by
    have hh := congrArg List.length (h1.symm.trans he1)
    simpa only [alternatingPairs_length, List.length_nil] using hh
  have len4 : 2 * d = 0 := by
    have hh := congrArg List.length (h4.symm.trans he4)
    simpa only [alternatingPairs_length, List.length_nil] using hh
  omega

theorem c_height_odd {H : Nat} {b : Board} (h : C H b) : H % 2 = 1 := by
  have odd := h.fourOdd c2
  simpa [OddColumn, height, h.middleTwo] using odd

/-! ## Actual one-opponent-move safety

The intermediate lemmas separate checked lines from support lowering. Their
local line guards are discharged below from the exact A/B/C bodies. No
abstract safe-successor or closed-invariant hypothesis is assumed.
-/

private theorem unresolved_guard_nonvertical_safe
    {H : Nat} {b : Board} (h : Common H b) {q : Col} (hq : Legal H b q)
    (guard : ∀ L, Unresolved H b L →
      ¬ (∀ x ∈ L.cells, stoneAt (drop b q Q) x = some Q))
    {L : Line} (hv : ValidLine H L) (hn : L.Nonvertical) :
    ¬ (∀ x ∈ L.cells, stoneAt (drop b q Q) x = some Q) := by
  intro hall
  by_cases checked : ToCheck H (exceptionSet H b) L
  · by_cases blocked : HasP b L
    · exact blocked_line_not_allQ (hasP_drop_preserves blocked q Q) hall
    · exact guard L ⟨checked, blocked⟩ hall
  · have aboveBottom : ∀ x ∈ L.cells, 2 ≤ x.row := by
      intro x hx
      have pos := (hv x hx).1
      have ne : x.row ≠ 1 := by
        intro he
        exact checked ⟨hv, hn, x, hx, Or.inl he⟩
      omega
    apply h.1.2.1
    apply supported_Q_move_implies_previous_P_win q hv hn aboveBottom
    intro x hx
    apply Q_supported_of_not_exception (aboveBottom x hx) (hall x hx)
    intro ex
    exact checked ⟨hv, hn, x, hx, Or.inr (existing_exception_after_Q hq ex)⟩

private theorem unresolved_guard_Q_move_safe
    {H : Nat} {b : Board} (h : Common H b) {q : Col} (hq : Legal H b q)
    (guard : ∀ L, Unresolved H b L →
      ¬ (∀ x ∈ L.cells, stoneAt (drop b q Q) x = some Q)) :
    ¬ Wins H (drop b q Q) Q := by
  rintro ⟨L, hv, hall⟩
  cases L with
  | horizontal r =>
      exact unresolved_guard_nonvertical_safe h hq guard hv trivial hall
  | vertical c r =>
      exact vertical_Q_after_move_impossible hq h.1.2.2.1 h.2 c r hv hall
  | rising r =>
      exact unresolved_guard_nonvertical_safe h hq guard hv trivial hall
  | falling r =>
      exact unresolved_guard_nonvertical_safe h hq guard hv trivial hall

theorem a0_Q_move_safe {H : Nat} {b : Board} (common : Common H b)
    (h : A0 H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  apply permanent_Q_move_safe
    (show PermanentData H b (exceptionSet H b) from
      ⟨common_structural common, a0_iff_all_checked_blocked.mp h⟩)
    common.1.2.1 hq

theorem a1_Q_move_safe {H : Nat} {b : Board} (common : Common H b)
    (h : A1 H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  rcases h with ⟨t, h⟩
  apply unresolved_guard_Q_move_safe common hq
  intro L hL
  exact empty_target_not_allQ (h.commonTarget L hL) (target_empty_after_Q h.target q)

theorem a2_Q_move_safe {H : Nat} {b : Board} (common : Common H b)
    (h : A2 H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  rcases h with ⟨t, h⟩
  apply unresolved_guard_Q_move_safe common hq
  intro L hL
  rcases h.commonUpperColumn L hL with ⟨x, hx, hc, hr⟩
  exact empty_target_not_allQ hx (target_upper_empty_after_Q h.target q hc hr)

/-- The exit checks are needed for closure, not for safety of this first Q move. -/
theorem b_Q_move_safe {H : Nat} {b : Board} (common : Common H b)
    (h : B H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  apply unresolved_guard_Q_move_safe common hq
  intro L hL hall
  rcases h.guards L hL with ⟨x, hx, hp⟩
  exact protected_not_Q_after_move hp q (hall x hx)

private theorem nonvertical_has_column {L : Line} (h : L.Nonvertical) (c : Col) :
    ∃ x ∈ L.cells, x.col = c := by
  cases L with
  | horizontal r =>
      cases c with
      | c1 => exact ⟨⟨c1, r⟩, by simp [Line.cells], rfl⟩
      | c2 => exact ⟨⟨c2, r⟩, by simp [Line.cells], rfl⟩
      | c3 => exact ⟨⟨c3, r⟩, by simp [Line.cells], rfl⟩
      | c4 => exact ⟨⟨c4, r⟩, by simp [Line.cells], rfl⟩
  | vertical c r => exact False.elim h
  | rising r =>
      cases c with
      | c1 => exact ⟨⟨c1, r⟩, by simp [Line.cells], rfl⟩
      | c2 => exact ⟨⟨c2, r + 1⟩, by simp [Line.cells], rfl⟩
      | c3 => exact ⟨⟨c3, r + 2⟩, by simp [Line.cells], rfl⟩
      | c4 => exact ⟨⟨c4, r + 3⟩, by simp [Line.cells], rfl⟩
  | falling r =>
      cases c with
      | c1 => exact ⟨⟨c1, r⟩, by simp [Line.cells], rfl⟩
      | c2 => exact ⟨⟨c2, r - 1⟩, by simp [Line.cells], rfl⟩
      | c3 => exact ⟨⟨c3, r - 2⟩, by simp [Line.cells], rfl⟩
      | c4 => exact ⟨⟨c4, r - 3⟩, by simp [Line.cells], rfl⟩

private theorem empty_other_column_stays_empty {b : Board} {q c : Col}
    (empty : b c = []) (hne : c ≠ q) {x : Cell} (hx : x.col = c) :
    stoneAt (drop b q Q) x = none := by
  simp [stoneAt, drop, hx, hne, empty]

theorem c_Q_move_safe {H : Nat} {b : Board} (common : Common H b)
    (h : C H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  apply unresolved_guard_Q_move_safe common hq
  intro L hL
  by_cases he : q = c2
  · rcases nonvertical_has_column hL.1.2.1 c3 with ⟨x, hx, hc⟩
    have hne : c3 ≠ q := by simp [he]
    exact empty_target_not_allQ hx
      (empty_other_column_stays_empty h.middleThree hne hc)
  · rcases nonvertical_has_column hL.1.2.1 c2 with ⟨x, hx, hc⟩
    exact empty_target_not_allQ hx
      (empty_other_column_stays_empty h.middleTwo (Ne.symm he) hc)

/-- Every exact U2 certificate excludes the opponent's VERY NEXT legal win.
This is not yet a closure or whole-game nonloss theorem. -/
theorem certificate_Q_move_safe {H : Nat} {b : Board}
    (h : Certificate H b) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q := by
  rcases h with ⟨common, ha | hb | hc⟩
  · rcases ha with h0 | h1 | h2
    · exact a0_Q_move_safe common h0 hq
    · exact a1_Q_move_safe common h1 hq
    · exact a2_Q_move_safe common h2 hq
  · exact b_Q_move_safe common hb hq
  · exact c_Q_move_safe common hc hq

/-! ## A0 closure, with the actual common premises restored at the new board -/

/-- Any legal cover-or-full response preserves A0's blockers. If the new board
has no P win and is not full, it is a new nonterminal U2 A0 certificate.
Q safety is proved here, not supplied as an assumption. -/
theorem a0_cover_closed {H : Nat} {b : Board} (common : Common H b)
    (h : A0 H b) {q p : Col} (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (cover : p = q ∨ height (drop b q Q) q = H)
    (noP : ¬ Wins H (drop (drop b q Q) p P) P)
    (notFull : ¬ Full H (drop (drop b q Q) p P)) :
    Common H (drop (drop b q Q) p P) ∧ A0 H (drop (drop b q Q) p P) := by
  have safe := a0_Q_move_safe common h hq
  have hs := structural_after_cover (common_structural common) hq hp safe cover
  refine ⟨⟨⟨hs.bounded, noP, hs.noQ, notFull⟩, hs.topRun⟩, ?_⟩
  exact a0_of_permanent ⟨exceptionSet H b, hs,
    permanent_blockers_preserved (a0_iff_all_checked_blocked.mp h) q p⟩

#print axioms a0_iff_permanent_of_structural
#print axioms unresolved_after_cover_subset
#print axioms a1_capture_is_a0
#print axioms a2_capture_wins
#print axioms certificate_Q_move_safe
#print axioms a0_cover_closed

end UniformFour.U2
