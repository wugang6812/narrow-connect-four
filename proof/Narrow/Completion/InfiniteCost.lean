import experiments.InfiniteNarrowBoards

namespace Connect4.InfiniteNarrowBoards.Cost
open FourColumns (partner partner_ne InP)
variable {w : Nat}

/-- Reversed move history, matching SafeUsing. The opening is free. -/
def switch (hist : List (Fin w)) (c : Fin w) : Nat :=
  match hist with
  | [] => 0
  | q :: _ => if c = q then 0 else 1

inductive Run (p : Player) (s : Strategy w) :
    List (Fin w) → Board w → Nat → Prop
  | start : Run p s [] (emptyBoard w) 0
  | step {hist b n c} (prior : Run p s hist b n)
      (own : ¬ HasFour b p) (opp : ¬ HasFour b (opponent p))
      (chosen : toMove b = p → s hist = c) :
      Run p s (c :: hist) (play b c (toMove b))
        (n + if toMove b = p then switch hist c else 0)

def SafePolicy (p : Player) (s : Strategy w) : Prop :=
  ∀ k, SafeUsing p s k [] (emptyBoard w)

def Achieves (p : Player) (s : Strategy w) (budget : Nat) : Prop :=
  SafePolicy p s ∧ ∀ hist b n, Run p s hist b n → n ≤ budget

def Exact (w : Nat) (p : Player) (budget : Nat) : Prop :=
  (∃ s : Strategy w, Achieves p s budget) ∧
  ∀ (s : Strategy w) n, Achieves p s n → budget ≤ n

theorem safe_on_run {p : Player} {s : Strategy w} (safe : SafePolicy p s)
    {hist b n} (path : Run p s hist b n) : ∀ k, SafeUsing p s k hist b := by
  induction path with
  | start => exact safe
  | @step hist b n c path own opp chosen ih =>
    intro k
    have next := ((ih (k+1)).2).resolve_left own
    by_cases turn : toMove b = p
    · rw [if_pos turn, chosen turn] at next
      exact next
    · rw [if_neg turn] at next
      exact next c

theorem cover_zero {p : Player} {s : Strategy w}
    (covers : ∀ c hist, s (c :: hist) = c)
    {hist b n} (path : Run p s hist b n) : n = 0 := by
  induction path with
  | start => rfl
  | @step hist b n c path own opp chosen ih =>
    by_cases turn : toMove b = p
    · cases hist with
      | nil => simp [turn, switch, ih]
      | cons q qs =>
        have eq := (chosen turn).symm.trans (covers q qs)
        simp [turn, switch, ih, eq]
    · simp [turn, ih]

theorem white_cost {hist b n} (path : Run .white whiteStrategy hist b n) :
    n ≤ (if 2 ≤ hist.length then 1 else 0) := by
  induction path with
  | start => decide
  | @step hist b n c path own opp chosen ih =>
    cases hist with
    | nil => simpa [switch] using ih
    | cons q rest =>
      cases rest with
      | nil =>
        simp at ih
        simp [ih, switch]
        split <;> simp_all
        split <;> decide
      | cons t ts =>
        by_cases turn : toMove b = .white
        · have eq : c = q := (chosen turn).symm
          simpa [turn, switch, eq] using ih
        · simpa [turn] using ih

end Connect4.InfiniteNarrowBoards.Cost
