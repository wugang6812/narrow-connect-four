import Std
import Lean.Elab.Tactic.Omega

/-!
Standalone model. Rows are 1-based; columns are named c1,...,c4.
This is NOT a replacement for the user's Connect4 definitions.
Local validation records accompany this copy. A bridge to the older repository model is separate.
-/
namespace OddHeight

inductive Player where
  | P | Q
  deriving DecidableEq, BEq, Repr

inductive Col where
  | c1 | c2 | c3 | c4
  deriving DecidableEq, BEq, Repr

open Player Col

@[simp] theorem player_beq_true (p q : Player) : (p == q) = true ↔ p = q := by
  cases p <;> cases q <;> decide

@[simp] theorem col_beq_true (c d : Col) : (c == d) = true ↔ c = d := by
  cases c <;> cases d <;> decide

@[simp] theorem option_player_beq_true (a b : Option Player) :
    (a == b) = true ↔ a = b := by
  cases a with
  | none =>
      cases b with
      | none => decide
      | some q => cases q <;> decide
  | some p =>
      cases b with
      | none => cases p <;> decide
      | some q => cases p <;> cases q <;> decide

def allCols : List Col := [c1, c2, c3, c4]

def mirror : Col → Col
  | c1 => c4 | c2 => c3 | c3 => c2 | c4 => c1

@[simp] theorem mirror_mirror (c : Col) : mirror (mirror c) = c := by
  cases c <;> rfl

abbrev Board := Col → List Player

def board (a b c d : List Player) : Board
  | c1 => a | c2 => b | c3 => c | c4 => d

def empty : Board := board [] [] [] []
def height (b : Board) (c : Col) : Nat := (b c).length

def drop (b : Board) (c : Col) (p : Player) : Board :=
  fun d => if d = c then b d ++ [p] else b d

def Legal (H : Nat) (b : Board) (c : Col) : Prop := height b c < H

instance (H : Nat) (b : Board) (c : Col) : Decidable (Legal H b c) :=
  inferInstanceAs (Decidable (height b c < H))

def Bounded (H : Nat) (b : Board) : Prop := ∀ c, height b c ≤ H

def Full (H : Nat) (b : Board) : Prop := ∀ c, height b c = H

@[simp] theorem drop_same (b : Board) (c : Col) (p : Player) :
    drop b c p c = b c ++ [p] := by simp [drop]

@[simp] theorem drop_other (b : Board) (c d : Col) (p : Player) (h : d ≠ c) :
    drop b c p d = b d := by simp [drop, h]

@[simp] theorem height_drop_same (b : Board) (c : Col) (p : Player) :
    height (drop b c p) c = height b c + 1 := by simp [height]

theorem drop_bounded {H : Nat} {b : Board} {c : Col}
    (hb : Bounded H b) (hc : Legal H b c) (p : Player) :
    Bounded H (drop b c p) := by
  intro d
  by_cases hd : d = c
  · subst d
    simp only [height_drop_same]
    unfold Legal at hc
    omega
  · simpa [height, drop, hd] using hb d

theorem bounded_notFull_exists_legal {H : Nat} {b : Board}
    (hb : Bounded H b) (hf : ¬ Full H b) : ∃ c, Legal H b c := by
  classical
  apply Classical.byContradiction
  intro hn
  apply hf
  intro c
  have hbound := hb c
  have hnot : ¬ Legal H b c := fun hc => hn ⟨c, hc⟩
  unfold Legal at hnot
  omega

structure Cell where
  col : Col
  row : Nat
  deriving DecidableEq, BEq, Repr

def stoneAt (b : Board) (x : Cell) : Option Player :=
  if x.row = 0 then none else (b x.col)[x.row - 1]?

/-- Each nonvertical line crosses all four columns; falling starts at its top-left cell. -/
inductive Line where
  | horizontal (r : Nat)
  | vertical (c : Col) (r : Nat)
  | rising (r : Nat)
  | falling (r : Nat)
  deriving DecidableEq, BEq, Repr

def Line.cells : Line → List Cell
  | .horizontal r => [⟨c1,r⟩, ⟨c2,r⟩, ⟨c3,r⟩, ⟨c4,r⟩]
  | .vertical c r => [⟨c,r⟩, ⟨c,r+1⟩, ⟨c,r+2⟩, ⟨c,r+3⟩]
  | .rising r => [⟨c1,r⟩, ⟨c2,r+1⟩, ⟨c3,r+2⟩, ⟨c4,r+3⟩]
  | .falling r => [⟨c1,r⟩, ⟨c2,r-1⟩, ⟨c3,r-2⟩, ⟨c4,r-3⟩]

def Line.Nonvertical : Line → Prop
  | .vertical _ _ => False
  | _ => True

def InBoard (H : Nat) (x : Cell) : Prop := 1 ≤ x.row ∧ x.row ≤ H

def ValidLine (H : Nat) (L : Line) : Prop := ∀ x ∈ L.cells, InBoard H x

def HasP (b : Board) (L : Line) : Prop := ∃ x ∈ L.cells, stoneAt b x = some P

def Wins (H : Nat) (b : Board) (p : Player) : Prop :=
  ∃ L, ValidLine H L ∧ ∀ x ∈ L.cells, stoneAt b x = some p

/-- Live excludes BOTH players' wins. A strategy must stop at a P win. -/
def Live (H : Nat) (b : Board) : Prop :=
  Bounded H b ∧ ¬ Wins H b P ∧ ¬ Wins H b Q ∧ ¬ Full H b

def rise : Line := .rising 1
def down : Line := .falling 4
def rowTwo : Line := .horizontal 2

def existingException (b : Board) (x : Cell) : Prop :=
  2 ≤ x.row ∧ stoneAt b x = some Q ∧ stoneAt b ⟨x.col, x.row - 1⟩ = some Q

/-- Full Q-topped columns have NO potential exception above the board. -/
def potentialException (H : Nat) (b : Board) (x : Cell) : Prop :=
  0 < height b x.col ∧ height b x.col < H ∧
  x.row = height b x.col + 1 ∧ stoneAt b ⟨x.col, height b x.col⟩ = some Q

def exceptionSet (H : Nat) (b : Board) (x : Cell) : Prop :=
  existingException b x ∨ potentialException H b x

def ExceptionComplete (H : Nat) (b : Board) (E : Cell → Prop) : Prop :=
  ∀ x, exceptionSet H b x → E x

def ToCheck (H : Nat) (E : Cell → Prop) (L : Line) : Prop :=
  ValidLine H L ∧ L.Nonvertical ∧ ∃ x ∈ L.cells, x.row = 1 ∨ E x

/-- No nonfull column ends in three Q stones. Initial Q fours are excluded separately. -/
def TopRunAtMostTwo (H : Nat) (b : Board) : Prop :=
  ∀ c, height b c < H → 3 ≤ height b c →
    ¬ (stoneAt b ⟨c, height b c⟩ = some Q ∧
       stoneAt b ⟨c, height b c - 1⟩ = some Q ∧
       stoneAt b ⟨c, height b c - 2⟩ = some Q)

structure Structural (H : Nat) (b : Board) (E : Cell → Prop) : Prop where
  bounded : Bounded H b
  noQ : ¬ Wins H b Q
  topRun : TopRunAtMostTwo H b
  complete : ExceptionComplete H b E

structure PermanentData (H : Nat) (b : Board) (E : Cell → Prop) : Prop where
  structural : Structural H b E
  blocked : ∀ L, ToCheck H E L → HasP b L

def PermanentHyp (H : Nat) (b : Board) : Prop := ∃ E, PermanentData H b E

structure Target where
  col : Col
  row : Nat
  deriving DecidableEq, BEq, Repr

def targetCell (t : Target) : Cell := ⟨t.col, t.row⟩
def inJ (ts : List Target) (c : Col) : Bool := ts.any (fun t => t.col == c)
def outside (H : Nat) (b : Board) (ts : List Target) : Nat :=
  (allCols.map (fun c => if inJ ts c then 0 else H - height b c)).foldl (· + ·) 0

/-- Static C6 premises. They do not assert C6 or its strategy is already proved. -/
structure CandidateData (H : Nat) (b : Board) (L : Line) (ts : List Target)
    (E : Cell → Prop) : Prop where
  structural : Structural H b E
  nonempty : ts ≠ []
  distinctColumns : (ts.map Target.col).Nodup
  lineValid : ValidLine H L
  otherBlocked : ∀ M, ToCheck H E M → M ≠ L → HasP b M
  onLine : ∀ t ∈ ts, targetCell t ∈ L.cells
  positive : ∀ t ∈ ts, height b t.col < t.row
  evenGap : ∀ t ∈ ts, (t.row - height b t.col) % 2 = 0
  belowRoof : ∀ t ∈ ts, t.row ≤ H
  outsideEven : outside H b ts % 2 = 0

def CandidateHyp (H : Nat) (b : Board) (L : Line) (ts : List Target) : Prop :=
  ∃ E, CandidateData H b L ts E

/-- Correct weakened top statement used after A3/A4, not 'all columns P-topped'. -/
def NonfullPTopped (H : Nat) (b : Board) : Prop :=
  ∀ c, 0 < height b c → height b c < H → stoneAt b ⟨c, height b c⟩ = some P

theorem no_potential_of_nonfull_ptopped {H : Nat} {b : Board}
    (h : NonfullPTopped H b) : ∀ x, ¬ potentialException H b x := by
  intro x hx
  have hp := h x.col hx.1 hx.2.1
  have hq := hx.2.2.2
  rw [hp] at hq
  cases hq

/-- A permanent P blocker excludes an all-Q line independently of the rest of the board. -/
theorem blocked_line_not_allQ {b : Board} {L : Line} (hp : HasP b L) :
    ¬ (∀ x ∈ L.cells, stoneAt b x = some Q) := by
  rcases hp with ⟨x, hx, hp⟩
  intro hq
  have h := hq x hx
  rw [hp] at h
  cases h

/-- C6 needs an actually empty target, not just a target label in a phase. -/
theorem empty_target_not_allQ {b : Board} {L : Line} {x : Cell}
    (hx : x ∈ L.cells) (he : stoneAt b x = none) :
    ¬ (∀ y ∈ L.cells, stoneAt b y = some Q) := by
  intro hq
  have h := hq x hx
  rw [he] at h
  cases h

theorem full_column_no_potential {H : Nat} {b : Board} {x : Cell}
    (hf : height b x.col = H) : ¬ potentialException H b x := by
  intro hx
  have hl := hx.2.1
  omega

theorem first_target_on_down : targetCell ⟨c3,2⟩ ∈ down.cells := by simp [targetCell, down, Line.cells]
theorem rise_target_on_rise : targetCell ⟨c3,3⟩ ∈ rise.cells := by simp [targetCell, rise, Line.cells]
theorem down_target_on_down : targetCell ⟨c2,3⟩ ∈ down.cells := by simp [targetCell, down, Line.cells]

end OddHeight
