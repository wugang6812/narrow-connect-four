import OddHeight.Words
import OddHeight.Strategy

namespace OddHeight
open Player Col

def innerBoard (a : Nat) : Board := board ([P] ++ qp a) [Q] [] []
def outerBoard (a d : Nat) : Board := board (qp a) [] [] (qp d)

def a1 (a d : Nat) : Board := board (qp a) [Q] [P] (qp d)
def a2 (a d : Nat) : Board := board (qp a) [P] [Q] (qp d)
def a3 (a d : Nat) : Board := board (qp a ++ [Q]) [] [P] (qp d)
def a4 (a d : Nat) : Board := board (qp a) [P] [] (qp d ++ [Q])

/-- These four exits use d=0 or d=1. The c4 move to d=2 is a different exit. -/
def middleExit1 (d : Nat) : Board := board [Q,P] [Q,Q,P] [P] (qp d)
def middleExit2 (d : Nat) : Board := board [Q,P] [P] [Q,Q,P] (qp d)
def middleExit3 (d : Nat) : Board := board [Q,P] [Q] [P,Q,P] (qp d)
def middleExit4 (d : Nat) : Board := board [Q,P] [P,Q,P] [Q] (qp d)

def InnerFamily (H : Nat) (b : Board) : Prop :=
  ∃ a, b = innerBoard a ∧ 1 + 2 * a ≤ H

def OuterFamily (H : Nat) (b : Board) : Prop :=
  ∃ a d, 1 ≤ a ∧ b = outerBoard a d ∧ 2 * a ≤ H ∧ 2 * d ≤ H

def DelayFamily (b : Board) : Prop :=
  ∃ d, (d = 0 ∨ d = 1) ∧ (b = a1 1 d ∨ b = a2 1 d)

/-- Phase data contain the STATIC geometric hypotheses, not the desired nonloss theorem. -/
def PhaseInvariant (H : Nat) (b : Board) : Phase → Prop
  | .innerWait => InnerFamily H b
  | .outerWait => OuterFamily H b
  | .delay => DelayFamily b
  | .candidate L ts => CandidateHyp H b L ts
  | .permanent => PermanentHyp H b

@[simp] theorem inner_height_one (a : Nat) : height (innerBoard a) c1 = 1 + 2 * a := by
  simp [height, innerBoard, board, Nat.add_comm]

@[simp] theorem outer_height_one (a d : Nat) : height (outerBoard a d) c1 = 2 * a := by
  simp [height, outerBoard, board]

@[simp] theorem outer_height_four (a d : Nat) : height (outerBoard a d) c4 = 2 * d := by
  simp [height, outerBoard, board]

/-- These equalities certify that an A3/A4 full outer column is Q-topped. -/
theorem a3_full_height (a d : Nat) : height (a3 a d) c1 = 2 * a + 1 := by
  simp [height, a3, board]

theorem a4_full_height (a d : Nat) : height (a4 a d) c4 = 2 * d + 1 := by
  simp [height, a4, board]

/-- Four exact, finite transition checks. No unbounded game assertion is hidden here. -/
example : reply 5 (a1 1 0) c2 .delay = some (c2, .candidate rise [⟨c3,3⟩]) := by decide
example : reply 5 (a2 1 0) c3 .delay = some (c3, .candidate down [⟨c2,3⟩]) := by decide
example : reply 5 (a1 1 1) c4 .delay = some (c4, .candidate down [⟨c2,3⟩]) := by decide
example : reply 5 (a1 1 0) c4 .delay = some (c4, .delay) := by decide

/-- Exact abstract delay transition, for every height; move legality is proved separately. -/
theorem a1_stays_delayed_iff (H d : Nat) (hd : d = 0 ∨ d = 1) (q : Col) :
    reply H (a1 1 d) q .delay = some (q, .delay) ↔ d = 0 ∧ q = c4 := by
  rcases hd with rfl | rfl <;> cases q <;> (dsimp [reply, rawReply]; decide)

theorem a2_stays_delayed_iff (H d : Nat) (hd : d = 0 ∨ d = 1) (q : Col) :
    reply H (a2 1 d) q .delay = some (q, .delay) ↔ d = 0 ∧ q = c4 := by
  rcases hd with rfl | rfl <;> cases q <;> (dsimp [reply, rawReply]; decide)

theorem a1_delaying_round_shape :
    drop (drop (a1 1 0) c4 Q) c4 P = a1 1 1 := by
  funext c
  cases c <;> rfl

theorem a2_delaying_round_shape :
    drop (drop (a2 1 0) c4 Q) c4 P = a2 1 1 := by
  funext c
  cases c <;> rfl

theorem a1_next_round_exits_delay (H : Nat) (q : Col) :
    reply H (a1 1 1) q .delay ≠ some (q, .delay) := by cases q <;> (dsimp [reply, rawReply]; decide)

theorem a2_next_round_exits_delay (H : Nat) (q : Col) :
    reply H (a2 1 1) q .delay ≠ some (q, .delay) := by cases q <;> (dsimp [reply, rawReply]; decide)

end OddHeight
