import HistoryRoots

namespace UniformFour.PaperOne
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U1 UniformFour.U2

/-- The opening placement has no preceding opponent move. A different reply
counts here even when the opponent has just filled the previous column. -/
def switch (q p : Col) : Nat := if p = q then 0 else 1

/-- Only completed replies charge the counters. A winning reply is included. -/
inductive Counted {S : Type} (H : Nat) (f : Controller S) (root : Board) (initial : S) :
    Nat → Nat → Board → S → Prop
  | nil : Counted H f root initial 0 0 root initial
  | step {a t b s q p next} (prior : Counted H f root initial a t b s)
      (noP : ¬ Wins H b P) (noQ : ¬ Wins H b Q) (notFull : ¬ Full H b)
      (legalQ : Legal H b q) (safeQ : ¬ Wins H (drop b q Q) Q)
      (notFullQ : ¬ Full H (drop b q Q))
      (chosen : f b q s = some (p,next)) (legalP : Legal H (drop b q Q) p) :
      Counted H f root initial (a + activeCost H (drop b q Q) q p) (t + switch q p)
        (afterRound b q p) next

theorem counted_prefix {S H f root initial a t b} {s : S}
    (path : Counted H f root initial a t b s) : Prefix H f root initial a b s := by
  induction path with
  | nil => exact .nil
  | step _ h1 h2 h3 h4 h5 h6 h7 h8 ih => exact .step ih h1 h2 h3 h4 h5 h6 h7 h8

def openBit (H : Nat) (b : Board) (c : Col) : Nat := if Legal H b c then 1 else 0
def openCols (H : Nat) (b : Board) : Nat :=
  openBit H b c1 + openBit H b c2 + openBit H b c3 + openBit H b c4

private theorem legal_implies_positive {H b q} (hq : Legal H b q) : 0 < openCols H b := by
  cases q <;> simp [openCols, openBit, hq] <;> omega

private theorem open_drop {H b q} (hq : Legal H b q) (v : Player) :
    openCols H (drop b q v) + (if Legal H (drop b q v) q then 0 else 1) = openCols H b := by
  have other (c : Col) (ne : c ≠ q) : openBit H (drop b q v) c = openBit H b c := by
    have eq : Legal H (drop b q v) c ↔ Legal H b c := by simp [Legal,height,drop,ne]
    by_cases hc : Legal H b c
    · simp [openBit,hc,eq.mpr hc]
    · have post : ¬ Legal H (drop b q v) c := fun h => hc (eq.mp h)
      simp [openBit,hc,post]
  have atq : openBit H (drop b q v) q + (if Legal H (drop b q v) q then 0 else 1) =
      openBit H b q := by
    by_cases room : Legal H (drop b q v) q <;> simp [openBit, hq, room]
  cases q with
  | c1 =>
    simp only [openCols, other c2 (by decide), other c3 (by decide), other c4 (by decide)]
    omega
  | c2 =>
    simp only [openCols, other c1 (by decide), other c3 (by decide), other c4 (by decide)]
    omega
  | c3 =>
    simp only [openCols, other c1 (by decide), other c2 (by decide), other c4 (by decide)]
    omega
  | c4 =>
    simp only [openCols, other c1 (by decide), other c2 (by decide), other c3 (by decide)]
    omega

private theorem switch_capacity {H b q p} (hq : Legal H b q) (hp : Legal H (drop b q Q) p) :
    switch q p + (openCols H (afterRound b q p) - 1) ≤
      activeCost H (drop b q Q) q p + (openCols H b - 1) := by
  have e1 := open_drop hq Q
  have e2 := open_drop hp P
  have positive := legal_implies_positive hp
  unfold afterRound
  by_cases same : p = q <;> by_cases cover : Legal H (drop b q Q) q <;>
    simp [switch, activeCost, same, cover] at * <;> omega

theorem passive_capacity {S H f root initial a t b} {s : S}
    (path : Counted H f root initial a t b s) :
    t + (openCols H b - 1) ≤ a + (openCols H root - 1) := by
  induction path with
  | nil => omega
  | step prior _ _ _ hq _ _ _ hp ih =>
    have := switch_capacity hq hp
    omega

theorem four_open_bound (H : Nat) (b : Board) : openCols H b ≤ 4 := by
  have bound (c : Col) : openBit H b c ≤ 1 := by unfold openBit; split <;> decide
  have := bound c1
  have := bound c2
  have := bound c3
  have := bound c4
  unfold openCols
  omega

/-- The same fixed first-player response as the exact active-budget theorem. -/
theorem first_total_from_root {H : Nat} (positive : 0 < H) :
    HistoryBudget H (stateless (respond H)) (firstBudget H) firstBoard () ∧
    ∀ a t b s, Counted H (stateless (respond H)) firstBoard () a t b s → t ≤ 4 := by
  have safe := first_positive_budget positive
  refine ⟨budget_to_history safe, ?_⟩
  intro a t b s path
  have total := passive_capacity path
  have active := (budget_along_prefix safe (counted_prefix path)).1
  have bound := four_open_bound H firstBoard
  unfold firstBudget at active
  split at active <;> omega

theorem first_total_zero :
    HistoryBudget 0 (stateless (respond 0)) 0 empty () ∧
    ∀ a t b s, Counted 0 (stateless (respond 0)) empty () a t b s → t = 0 := by
  refine ⟨budget_to_history first_height_zero_budget, ?_⟩
  intro a t b s path
  have total := passive_capacity path
  have active := (budget_along_prefix first_height_zero_budget (counted_prefix path)).1
  have emptyZero : openCols 0 empty = 0 := by decide
  omega

#print axioms first_total_from_root
#print axioms first_total_zero
end UniformFour.PaperOne
