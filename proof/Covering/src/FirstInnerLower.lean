import FirstOuterLower

/-! Reviewed copy. Parameterized inner-opening delay, with the first column
prepared to exactly four stones. No finite-height enumeration is used. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col

def innerState (m : Nat) (xs ys : List Player) : Board :=
  board xs ([P] ++ (qp (m-1) ++ [Q])) (qp m) ys

def innerDelay (m k : Nat) : Board :=
  innerState m (qp 2 ++ ([P] ++ qp k)) (qp 1)

/-- All possible P rows in the first-column delaying family. Row six is absent,
which is the essential high falling-line obstruction. -/
theorem delay_P_rows (k r : Nat)
    (h : readRow (qp 2 ++ ([P] ++ qp k)) r = some P) :
    r = 2 ∨ r = 4 ∨ (5 ≤ r ∧ r % 2 = 1) := by
  cases r with
  | zero => simp [readRow] at h
  | succ r =>
    cases r with
    | zero => simp [readRow, qp] at h
    | succ r =>
      cases r with
      | zero => exact Or.inl rfl
      | succ r =>
        cases r with
        | zero => simp [readRow, qp] at h
        | succ r =>
          cases r with
          | zero => exact Or.inr (Or.inl rfl)
          | succ r =>
            have h' : readRow ([P] ++ qp k) (r+1) = some P := h
            have rows := (read_pqp_P k (r+1)).1 h'
            right
            right
            omega

theorem initial_inner_P_rows (r : Nat) (h : readRow (qp 2) r = some P) :
    r = 2 ∨ r = 4 ∨ (5 ≤ r ∧ r % 2 = 1) := by
  have rows := (read_qp_P 2 r).1 h
  omega

/-- A geometric envelope covering the initial exit, every delaying state, and
all P moves into the fourth column. It explicitly excludes premature P wins. -/
theorem innerState_no_P {H m : Nat} {xs ys : List Player}
    (firstRows : ∀ r, readRow xs r = some P →
      r = 2 ∨ r = 4 ∨ (5 ≤ r ∧ r % 2 = 1))
    (lastRows : ∀ r, readRow ys r = some P → r = 2 ∨ r = 3) :
    ¬ Wins H (innerState m xs ys) P := by
  rintro ⟨L, hv, hs⟩
  cases L with
  | horizontal r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r⟩ (by simp [Line.cells])
    simp only [stoneAt_readRow, innerState, board] at h0 h1 h3
    have a := firstRows r h0
    have d := lastRows r h3
    have b := (read_pqpq_P_U1 (m-1) r).1 h1
    omega
  | rising r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r+3⟩ (by simp [Line.cells])
    simp only [stoneAt_readRow, innerState, board] at h0 h3
    have a := firstRows r h0
    have d := lastRows (r+3) h3
    omega
  | falling r =>
    have h0 := hs ⟨c1,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c2,r-1⟩ (by simp [Line.cells])
    have h3 := hs ⟨c4,r-3⟩ (by simp [Line.cells])
    simp only [stoneAt_readRow, innerState, board] at h0 h1 h3
    have a := firstRows r h0
    have d := lastRows (r-3) h3
    have b := (read_pqpq_P_U1 (m-1) (r-1)).1 h1
    omega
  | vertical c r =>
    have h0 := hs ⟨c,r⟩ (by simp [Line.cells])
    have h1 := hs ⟨c,r+1⟩ (by simp [Line.cells])
    have h2 := hs ⟨c,r+2⟩ (by simp [Line.cells])
    have h3 := hs ⟨c,r+3⟩ (by simp [Line.cells])
    cases c with
    | c1 =>
      simp only [stoneAt_readRow, innerState, board] at h0 h1 h2 h3
      have a := firstRows r h0
      have b := firstRows (r+1) h1
      have c := firstRows (r+2) h2
      have d := firstRows (r+3) h3
      omega
    | c2 => simp_all [innerState, board] <;> omega
    | c3 => simp_all [innerState, board] <;> omega
    | c4 =>
      simp only [stoneAt_readRow, innerState, board] at h0 h1 h2 h3
      have a := lastRows r h0
      have b := lastRows (r+1) h1
      have c := lastRows (r+2) h2
      have d := lastRows (r+3) h3
      omega

private theorem lastPair_rows (r : Nat) (h : readRow (qp 1) r = some P) :
    r = 2 ∨ r = 3 := by
  have rows := (read_qp_P 1 r).1 h
  omega

private theorem lastPairP_rows (r : Nat) (h : readRow (qp 1 ++ [P]) r = some P) :
    r = 2 ∨ r = 3 := by
  simp only [read_append_P_P_U1, qp_length] at h
  rcases h with old | new
  · exact lastPair_rows r old
  · exact Or.inr new

theorem innerDelay_no_P (m k : Nat) : ¬ Wins (2*m) (innerDelay m k) P :=
  innerState_no_P (delay_P_rows k) lastPair_rows

/-- Any first column satisfying the delaying envelope gives an immediate trap
once P enters the fourth column. Only its fixed bottom Q is used for the win. -/
theorem inner_fourth_trap {m n : Nat} {xs : List Player} (hm : 2 ≤ m)
    (firstRows : ∀ r, readRow xs r = some P →
      r = 2 ∨ r = 4 ∨ (5 ≤ r ∧ r % 2 = 1))
    (bottom : readRow xs 1 = some Q) :
    ZeroTrap (2*m) (n+1) (innerState m xs (qp 1 ++ [P])) := by
  apply ZeroTrap.hit c4 (innerState_no_P firstRows lastPairP_rows)
  · simp [Legal, height, innerState, board]
    omega
  · refine ⟨Line.rising 1, ?_, ?_⟩
    · intro x hx
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [InBoard] <;> omega
    · intro x hx
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simpa [drop, innerState, board] using bottom
      · simp [drop, innerState, board] <;> omega
      · simp [drop, innerState, board] <;> omega
      · simp [drop, innerState, board, qp, readRow]

theorem innerDelay_round (m k : Nat) :
    drop (drop (innerDelay m k) c1 Q) c1 P = innerDelay m (k+1) := by
  funext c
  cases c <;> simp [innerDelay, innerState, drop, board, qp, List.append_assoc]

/-- t counts the remaining complete cover rounds in the delaying first column.
At t=0 Q fills it and every legal P reply is forced into column four. -/
theorem innerDelay_trap (t : Nat) : ∀ k m, m = k+t+3 →
    ZeroTrap (2*m) (t+2) (innerDelay m k) := by
  induction t with
  | zero =>
    intro k m hm
    apply ZeroTrap.branch c1 (innerDelay_no_P m k)
    · simp [Legal, height, innerDelay, innerState, board]
      omega
    · intro full
      have h := full c4
      simp [height, innerDelay, innerState, drop, board] at h
      omega
    · intro c hc _
      have only : c = c4 := by
        cases c <;> simp_all [Legal, height, innerDelay, innerState, drop, board] <;> omega
      subst c
      have shape : drop (drop (innerDelay m k) c1 Q) c4 P =
          innerState m ((qp 2 ++ ([P] ++ qp k)) ++ [Q]) (qp 1 ++ [P]) := by
        funext d
        cases d <;> simp [innerDelay, innerState, drop, board]
      rw [shape]
      apply inner_fourth_trap (by omega)
      · intro r h
        exact delay_P_rows k r ((read_append_Q_P_U1 _ r).1 h)
      · simp [readRow, qp]
  | succ t ih =>
    intro k m hm
    have tail : ZeroTrap (2*m) (t+2) (drop (drop (innerDelay m k) c1 Q) c1 P) := by
      rw [innerDelay_round]
      exact ih (k+1) m (by omega)
    have result := ZeroTrap.prepend_cover (innerDelay_no_P m k)
      (q := c1) (by simp [Legal, height, innerDelay, innerState, board]; omega)
      (by simp [Legal, height, innerDelay, innerState, drop, board]; omega) tail
    simpa [Nat.add_assoc] using result

theorem innerPrepared_trap {m : Nat} (hm : 2 ≤ m) :
    ZeroTrap (2*m) m (innerPrepared m) := by
  have positive : m = (m-1)+1 := by omega
  suffices h : ZeroTrap (2*m) ((m-1)+1) (innerPrepared m) from by
    simpa only [← positive] using h
  apply ZeroTrap.branch c2
  · intro win
    apply innerEndpoint_no_P hm
    rw [← inner_preparation_shape m]
    exact wins_drop_preserves win c2 Q
  · simp [Legal, height, innerPrepared, coverBlock_column, board]
    omega
  · rw [inner_preparation_shape]
    intro full
    have h := full c4
    simp [height, innerEndpoint, board] at h
    omega
  · rw [inner_preparation_shape]
    intro c hc _
    rcases (innerEndpoint_choices hm c).1 hc with ⟨rfl,h3⟩ | rfl
    · have shape : drop (innerEndpoint m) c1 P = innerDelay m 0 := by
        funext d
        cases d <;> simp [innerEndpoint, innerDelay, innerState, drop, board, qp]
      rw [shape]
      have result := innerDelay_trap (m-3) 0 m (by omega)
      have rank : m-3+2 = m-1 := by omega
      simpa only [rank] using result
    · have shape : drop (innerEndpoint m) c4 P = innerState m (qp 2) (qp 1 ++ [P]) := by
        funext d
        cases d <;> simp [innerEndpoint, innerState, drop, board]
      rw [shape]
      have rank : m-1 = (m-2)+1 := by omega
      rw [rank]
      exact inner_fourth_trap hm initial_inner_P_rows (by simp [readRow, qp])

/-- Inner first opening, arbitrary history-dependent controller state. -/
theorem first_inner_zero_budget_impossible {S : Type} {m : Nat}
    (hm : 2 ≤ m) (f : Controller S) (s : S) :
    ¬ BudgetSafe (2*m) f 0 (board [] [P] [] []) s := by
  obtain ⟨n,trap⟩ := inner_prepare_transport hm ⟨m,innerPrepared_trap hm⟩
  exact zeroTrap_not_budgetSafe trap f s

#print axioms innerDelay_trap
#print axioms first_inner_zero_budget_impossible
end UniformFour.U1
