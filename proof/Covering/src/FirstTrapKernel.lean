import BudgetSemantics
import OddHeight.MoveFacts
import OddHeight.Words

/-! Reviewed copy. Actual-board finite counterstrategy certificates and exact
parameter-trap geometry. The complete roots are assembled by FirstOuterLower, FirstInnerLower, and
FirstEvenLower. This module alone supplies the common trap kernel and geometry. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col

/-- A finite certificate refuting zero-budget safety. Branching is universal
over legal zero-cost replies, including every forced-column exit. A branch may
list continuations after Q has already won: the safety assumption then fails
before any response, so those continuations are never used by soundness. This
is NOT a first-win-normalized actual-play tree. The rank is a response-round
horizon, not a bound on the board height. -/
inductive ZeroTrap (H : Nat) : Nat → Board → Prop where
  | hit {b : Board} {n : Nat} (q : Col)
      (noP : ¬ Wins H b P) (legal : Legal H b q)
      (win : Wins H (drop b q Q) Q) : ZeroTrap H (n+1) b
  | branch {b : Board} {n : Nat} (q : Col)
      (noP : ¬ Wins H b P) (legal : Legal H b q)
      (notFullQ : ¬ Full H (drop b q Q))
      (children : ∀ c, Legal H (drop b q Q) c →
        activeCost H (drop b q Q) q c = 0 →
        ZeroTrap H n (drop (drop b q Q) c P)) : ZeroTrap H (n+1) b

/-- Soundness quantifies arbitrary state and arbitrary controller, without any
assumption that the actual replies follow the intended losing script. -/
theorem zeroTrap_sound {H n : Nat} {b : Board} (trap : ZeroTrap H n b)
    {S : Type} (f : Controller S) (s : S) :
    ¬ BudgetRoundSafe H f n 0 b s := by
  induction trap generalizing s with
  | hit q noP legal win =>
    intro safe
    rcases safe.2 with won | full | moves
    · exact noP won
    · have eq := full q
      unfold Legal at legal
      omega
    · exact (moves q legal).1 win
  | @branch b n q noP legal notFullQ children ih =>
    intro safe
    rcases safe.2 with won | full | moves
    · exact noP won
    · have eq := full q
      unfold Legal at legal
      omega
    · rcases (moves q legal).2 with full | ⟨c,next,_,hc,cost,tail⟩
      · exact notFullQ full
      · have zero : activeCost H (drop b q Q) q c = 0 := by omega
        apply ih c hc zero next
        simpa using tail

theorem zeroTrap_not_budgetSafe {H n : Nat} {b : Board}
    (trap : ZeroTrap H n b) {S : Type} (f : Controller S) (s : S) :
    ¬ BudgetSafe H f 0 b s := by
  intro safe
  exact zeroTrap_sound trap f s (safe n)

/-- A prescribed opponent move with room for a cover has exactly one
zero-cost response. This composes a preparation round without choosing f. -/
theorem ZeroTrap.prepend_cover {H n : Nat} {b : Board} {q : Col}
    (noP : ¬ Wins H b P) (legal : Legal H b q)
    (cover : Legal H (drop b q Q) q)
    (tail : ZeroTrap H n (drop (drop b q Q) q P)) :
    ZeroTrap H (n+1) b := by
  apply ZeroTrap.branch q noP legal
  · intro full
    have eq := full q
    unfold Legal at cover
    omega
  · intro c hc zero
    have eq := zero_cost_forces_cover cover zero
    subst c
    exact tail

/-- Exact concrete execution of n forced cover rounds in one column. -/
def coverBlock : Nat → Board → Col → Board
  | 0, b, _ => b
  | n+1, b, c => drop (drop (coverBlock n b c) c Q) c P

theorem coverBlock_column (n : Nat) (b : Board) (c d : Col) :
    coverBlock n b c d = if d = c then b d ++ qp n else b d := by
  induction n with
  | zero => simp [coverBlock, qp]
  | succ n ih =>
    by_cases eq : d = c
    · subst d
      simp [coverBlock, drop, ih, qp, List.append_assoc]
    · simp [coverBlock, drop, eq, ih]

/-- After the last Q move in the outer-opening preparation; P to play. -/
def outerEndpoint (m : Nat) : Board :=
  board ([P] ++ (qp (m-1) ++ [Q])) (qp m) [] (qp (m-1))

/-- After the last Q move in the inner-opening preparation; P to play.
The first column is deliberately fixed at FOUR, not filled to 2*m. -/
def innerEndpoint (m : Nat) : Board :=
  board (qp 2) ([P] ++ (qp (m-1) ++ [Q])) (qp m) (qp 1)

/-- U1 section 7.3's preparation order, without the final unpaired Q move. -/
def outerPrepared (m : Nat) : Board :=
  coverBlock (m-1)
    (coverBlock (m-1) (coverBlock m firstBoard c2) c4) c1

/-- U1 section 7.4's preparation order. Column one receives exactly two pairs. -/
def innerPrepared (m : Nat) : Board :=
  coverBlock (m-1)
    (coverBlock 1
      (coverBlock m (coverBlock 2 (board [] [P] [] []) c1) c3) c4) c2

theorem outer_preparation_shape (m : Nat) :
    drop (outerPrepared m) c1 Q = outerEndpoint m := by
  funext c
  cases c <;>
    simp [outerPrepared, outerEndpoint, drop, coverBlock_column,
      firstBoard, board, List.append_assoc]

theorem inner_preparation_shape (m : Nat) :
    drop (innerPrepared m) c2 Q = innerEndpoint m := by
  funext c
  cases c <;>
    simp [innerPrepared, innerEndpoint, drop, coverBlock_column,
      board, List.append_assoc]

theorem outerEndpoint_choices {m : Nat} (hm : 2 ≤ m) (c : Col) :
    Legal (2*m) (outerEndpoint m) c ↔ c = c3 ∨ c = c4 := by
  cases c <;> simp [Legal, height, outerEndpoint, board] <;> omega

theorem innerEndpoint_choices {m : Nat} (hm : 2 ≤ m) (c : Col) :
    Legal (2*m) (innerEndpoint m) c ↔ (c = c1 ∧ 3 ≤ m) ∨ c = c4 := by
  cases c <;> simp [Legal, height, innerEndpoint, board] <;> omega

theorem outerEndpoint_bound {m : Nat} (hm : 2 ≤ m) :
    Bounded (2*m) (outerEndpoint m) := by
  intro c
  cases c <;> simp [height, outerEndpoint, board] <;> omega

theorem innerEndpoint_bound {m : Nat} (hm : 2 ≤ m) :
    Bounded (2*m) (innerEndpoint m) := by
  intro c
  cases c <;> simp [height, innerEndpoint, board] <;> omega

@[simp] theorem read_pqpq_P_U1 (a r : Nat) :
    readRow (P :: (qp a ++ [Q])) r = some P ↔
      0 < r ∧ r ≤ 2*a+1 ∧ r % 2 = 1 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
    cases r with
    | zero => simp [readRow]
    | succ r =>
      change (qp a ++ [Q])[r]? = some P ↔ _
      rw [qpq_get_P]
      omega

@[simp] theorem read_pqpq_Q_U1 (a r : Nat) :
    readRow (P :: (qp a ++ [Q])) r = some Q ↔
      2 ≤ r ∧ r ≤ 2*a+2 ∧ r % 2 = 0 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
    cases r with
    | zero => simp [readRow]
    | succ r =>
      change (qp a ++ [Q])[r]? = some Q ↔ _
      rw [qpq_get_Q]
      omega

/-- The preparation endpoint itself has no premature defender victory. -/
theorem outerEndpoint_no_P {m : Nat} (hm : 2 ≤ m) :
    ¬ Wins (2*m) (outerEndpoint m) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    all_goals simp_all [outerEndpoint, board, List.append_assoc] <;> omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    all_goals simp_all [outerEndpoint, board, List.append_assoc] <;> omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r-2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    all_goals simp_all [outerEndpoint, board, List.append_assoc] <;> omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c
    all_goals simp_all [outerEndpoint, board, List.append_assoc] <;> omega

/-- The preparation endpoint itself has no premature defender victory. -/
theorem innerEndpoint_no_P {m : Nat} (hm : 2 ≤ m) :
    ¬ Wins (2*m) (innerEndpoint m) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    all_goals simp_all [innerEndpoint, board, List.append_assoc] <;> omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    all_goals simp_all [innerEndpoint, board, List.append_assoc] <;> omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c3,r-2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    all_goals simp_all [innerEndpoint, board, List.append_assoc] <;> omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c
    all_goals simp_all [innerEndpoint, board, List.append_assoc] <;> omega

theorem wins_coverBlock_preserves {H : Nat} {b : Board} {p : Player}
    (win : Wins H b p) (n : Nat) (c : Col) : Wins H (coverBlock n b c) p := by
  induction n with
  | zero => exact win
  | succ n ih => exact wins_drop_preserves (wins_drop_preserves ih c Q) c P

theorem noP_before_coverBlock {H n : Nat} {b : Board} {c : Col}
    (noP : ¬ Wins H (coverBlock n b c) P) : ¬ Wins H b P :=
  fun win => noP (wins_coverBlock_preserves win n c)

/-- Compose an entire parameter-length preparation block. Final nonvictory
implies nonvictory at every prefix by append monotonicity. The capacity bound
proves Q legality and cover legality independently at every intermediate move. -/
theorem prepend_coverBlock {H n : Nat} {b : Board} {c : Col}
    (room : height b c + 2*n ≤ H)
    (noP : ¬ Wins H (coverBlock n b c) P)
    (tail : ∃ k, ZeroTrap H k (coverBlock n b c)) :
    ∃ k, ZeroTrap H k b := by
  revert room noP tail
  induction n with
  | zero =>
    intro room noP tail
    exact tail
  | succ n ih =>
    intro room noP tail
    have prevNoP : ¬ Wins H (coverBlock n b c) P := by
      intro win
      exact noP (wins_drop_preserves (wins_drop_preserves win c Q) c P)
    have heightEq : height (coverBlock n b c) c = height b c + 2*n := by
      simp [height, coverBlock_column]
    have legal : Legal H (coverBlock n b c) c := by
      unfold Legal
      omega
    have canCover : Legal H (drop (coverBlock n b c) c Q) c := by
      simp only [Legal, height_drop_same]
      omega
    obtain ⟨k, tk⟩ := tail
    have previous : ∃ k, ZeroTrap H k (coverBlock n b c) :=
      ⟨k+1, ZeroTrap.prepend_cover prevNoP legal canCover tk⟩
    exact ih (by omega) prevNoP previous

/-- All preparation legality and no-premature-P-win obligations for the outer
opening are discharged here. Only the exit trap at outerPrepared remains input. -/
theorem outer_prepare_transport {m : Nat} (hm : 2 ≤ m)
    (tail : ∃ n, ZeroTrap (2*m) n (outerPrepared m)) :
    ∃ n, ZeroTrap (2*m) n firstBoard := by
  let b1 := coverBlock m firstBoard c2
  let b2 := coverBlock (m-1) b1 c4
  have no3 : ¬ Wins (2*m) (outerPrepared m) P := by
    intro win
    apply outerEndpoint_no_P hm
    rw [← outer_preparation_shape m]
    exact wins_drop_preserves win c1 Q
  have no2 : ¬ Wins (2*m) b2 P := noP_before_coverBlock no3
  have no1 : ¬ Wins (2*m) b1 P := noP_before_coverBlock no2
  have t2 : ∃ n, ZeroTrap (2*m) n b2 := by
    apply prepend_coverBlock (n := m-1) (c := c1) _ no3 tail
    simp [b2, b1, height, coverBlock_column, firstBoard, board]
    omega
  have t1 : ∃ n, ZeroTrap (2*m) n b1 := by
    apply prepend_coverBlock (n := m-1) (c := c4) _ no2 t2
    simp [b1, height, coverBlock_column, firstBoard, board]
    omega
  apply prepend_coverBlock (n := m) (c := c2) _ no1 t1
  simp [height, firstBoard, board]

/-- The inner preparation has fixed two-pair and one-pair blocks, and arbitrary
m-pair and (m-1)-pair blocks. In particular c1 is never prepared above row four. -/
theorem inner_prepare_transport {m : Nat} (hm : 2 ≤ m)
    (tail : ∃ n, ZeroTrap (2*m) n (innerPrepared m)) :
    ∃ n, ZeroTrap (2*m) n (board [] [P] [] []) := by
  let b0 : Board := board [] [P] [] []
  let b1 := coverBlock 2 b0 c1
  let b2 := coverBlock m b1 c3
  let b3 := coverBlock 1 b2 c4
  have no4 : ¬ Wins (2*m) (innerPrepared m) P := by
    intro win
    apply innerEndpoint_no_P hm
    rw [← inner_preparation_shape m]
    exact wins_drop_preserves win c2 Q
  have no3 : ¬ Wins (2*m) b3 P := noP_before_coverBlock no4
  have no2 : ¬ Wins (2*m) b2 P := noP_before_coverBlock no3
  have no1 : ¬ Wins (2*m) b1 P := noP_before_coverBlock no2
  have t3 : ∃ n, ZeroTrap (2*m) n b3 := by
    apply prepend_coverBlock (n := m-1) (c := c2) _ no4 tail
    simp [b3, b2, b1, b0, height, coverBlock_column, board]
    omega
  have t2 : ∃ n, ZeroTrap (2*m) n b2 := by
    apply prepend_coverBlock (n := 1) (c := c4) _ no3 t3
    simp [b2, b1, b0, height, coverBlock_column, board]
    omega
  have t1 : ∃ n, ZeroTrap (2*m) n b1 := by
    apply prepend_coverBlock (n := m) (c := c3) _ no2 t2
    simp [b1, b0, height, coverBlock_column, board]
  apply prepend_coverBlock (n := 2) (c := c1) _ no1 t1
  simp [b0, height, board]
  omega

/-- The outer trap's advertised final square really completes the falling line.
This lemma alone is not a legal-first-win claim: preceding safety remains a
separate obligation in constructing the ZeroTrap certificate. -/
theorem outerEndpoint_finish {m : Nat} (hm : 2 ≤ m) :
    Wins (2*m) (drop (drop (outerEndpoint m) c3 P) c3 Q) Q := by
  refine ⟨Line.falling 4, ?_, ?_⟩
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [InBoard] <;> omega
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [drop, outerEndpoint, board, List.append_assoc] <;> omega
    · simp [drop, outerEndpoint, board] <;> omega
    · simp [drop, outerEndpoint, board, readRow]
    · simp [drop, outerEndpoint, board] <;> omega

/-- The inner trap's advertised final square really completes the rising line. -/
theorem innerEndpoint_finish {m : Nat} (hm : 2 ≤ m) :
    Wins (2*m) (drop (drop (innerEndpoint m) c4 P) c4 Q) Q := by
  refine ⟨Line.rising 1, ?_, ?_⟩
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [InBoard] <;> omega
  · intro x hx
    simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [drop, innerEndpoint, board] <;> omega
    · simp [drop, innerEndpoint, board, List.append_assoc] <;> omega
    · simp [drop, innerEndpoint, board] <;> omega
    · simp [drop, innerEndpoint, board, qp, readRow]

#print axioms zeroTrap_sound
#print axioms outerEndpoint_finish
#print axioms innerEndpoint_finish
end UniformFour.U1
