import OddHeight.Core

namespace OddHeight
open Player Col

def qp : Nat → List Player
  | 0 => []
  | n + 1 => qp n ++ [Q,P]

@[simp] theorem qp_length (n : Nat) : (qp n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [qp, ih] <;> omega

def firstBoard : Board := board [P] [] [] []
def readRow (xs : List Player) (r : Nat) : Option Player :=
  if r = 0 then none else xs[r - 1]?

@[simp] theorem stoneAt_readRow (b : Board) (c : Col) (r : Nat) :
    stoneAt b ⟨c,r⟩ = readRow (b c) r := rfl

theorem qp_succ_front (a : Nat) : qp (a + 1) = Q :: P :: qp a := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change qp (a + 1) ++ [Q,P] = Q :: P :: (qp a ++ [Q,P])
      rw [ih]
      rfl

theorem qp_get_Q (a i : Nat) :
    (qp a)[i]? = some Q ↔ i < 2 * a ∧ i % 2 = 0 := by
  induction a generalizing i with
  | zero => simp [qp]
  | succ a ih =>
      rw [qp_succ_front]
      cases i with
      | zero => simp <;> omega
      | succ i =>
          cases i with
          | zero => simp
          | succ i =>
              change (qp a)[i]? = some Q ↔ _
              rw [ih]
              omega

theorem qp_get_P (a i : Nat) :
    (qp a)[i]? = some P ↔ i < 2 * a ∧ i % 2 = 1 := by
  induction a generalizing i with
  | zero => simp [qp]
  | succ a ih =>
      rw [qp_succ_front]
      cases i with
      | zero => simp
      | succ i =>
          cases i with
          | zero => simp <;> omega
          | succ i =>
              change (qp a)[i]? = some P ↔ _
              rw [ih]
              omega

theorem qpq_get_Q (a i : Nat) :
    (qp a ++ [Q])[i]? = some Q ↔ i ≤ 2 * a ∧ i % 2 = 0 := by
  induction a generalizing i with
  | zero =>
      cases i with
      | zero => simp [qp]
      | succ i => simp [qp]
  | succ a ih =>
      rw [qp_succ_front]
      cases i with
      | zero => simp
      | succ i =>
          cases i with
          | zero => simp
          | succ i =>
              change (qp a ++ [Q])[i]? = some Q ↔ _
              rw [ih]
              omega

theorem qpq_get_P (a i : Nat) :
    (qp a ++ [Q])[i]? = some P ↔ i < 2 * a ∧ i % 2 = 1 := by
  induction a generalizing i with
  | zero =>
      cases i with
      | zero => simp [qp]
      | succ i => simp [qp]
  | succ a ih =>
      rw [qp_succ_front]
      cases i with
      | zero => simp
      | succ i =>
          cases i with
          | zero => simp <;> omega
          | succ i =>
              change (qp a ++ [Q])[i]? = some P ↔ _
              rw [ih]
              omega

@[simp] theorem read_qp_Q (a r : Nat) :
    readRow (qp a) r = some Q ↔ 0 < r ∧ r ≤ 2 * a ∧ r % 2 = 1 := by
  unfold readRow
  by_cases h : r = 0
  · simp [h]
  · simp only [if_neg h, qp_get_Q]
    omega

@[simp] theorem read_qp_P (a r : Nat) :
    readRow (qp a) r = some P ↔ 0 < r ∧ r ≤ 2 * a ∧ r % 2 = 0 := by
  unfold readRow
  by_cases h : r = 0
  · simp [h]
  · simp only [if_neg h, qp_get_P]
    omega

@[simp] theorem read_pqp_Q (a r : Nat) :
    readRow (P :: qp a) r = some Q ↔
      0 < r ∧ r ≤ 2 * a + 1 ∧ r % 2 = 0 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          change (qp a)[r]? = some Q ↔ _
          rw [qp_get_Q]
          omega

@[simp] theorem read_pqp_P (a r : Nat) :
    readRow (P :: qp a) r = some P ↔
      0 < r ∧ r ≤ 2 * a + 1 ∧ r % 2 = 1 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          change (qp a)[r]? = some P ↔ _
          rw [qp_get_P]
          omega

@[simp] theorem read_qpq_Q (a r : Nat) :
    readRow (qp a ++ [Q]) r = some Q ↔
      0 < r ∧ r ≤ 2 * a + 1 ∧ r % 2 = 1 := by
  unfold readRow
  by_cases h : r = 0
  · simp [h]
  · simp only [if_neg h, qpq_get_Q]
    omega

@[simp] theorem read_qpq_P (a r : Nat) :
    readRow (qp a ++ [Q]) r = some P ↔
      0 < r ∧ r ≤ 2 * a ∧ r % 2 = 0 := by
  unfold readRow
  by_cases h : r = 0
  · simp [h]
  · simp only [if_neg h, qpq_get_P]
    omega

@[simp] theorem read_nil (r : Nat) : readRow [] r = none := by
  simp [readRow]

@[simp] theorem read_one_Q (p : Player) (r : Nat) :
    readRow [p] r = some Q ↔ r = 1 ∧ p = Q := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r => simp [readRow]

@[simp] theorem read_one_P (p : Player) (r : Nat) :
    readRow [p] r = some P ↔ r = 1 ∧ p = P := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r => simp [readRow]


end OddHeight
