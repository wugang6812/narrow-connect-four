import BudgetSemantics

/-!
An explicit finite-history interpretation of the budget semantics.
Prefixes stop before any new round after a win or a full board. The last P
response may itself win and its active cost is still included. Missing or
illegal responses are rejected by HistoryBudget, not hidden by Prefix.
This is a bridge inside the supplied four-column model, not a bridge to the
older repository's differently named Board / IsDraw definitions.
-/
namespace UniformFour.U1
open OddHeight OddHeight.Player

inductive Prefix {S : Type} (H : Nat) (f : Controller S) (root : Board) (initial : S) :
    Nat → Board → S → Prop where
  | nil : Prefix H f root initial 0 root initial
  | step {cost : Nat} {b : Board} {s : S} {q p : Col} {next : S}
      (prior : Prefix H f root initial cost b s)
      (noP : ¬ Wins H b P) (noQ : ¬ Wins H b Q) (notFull : ¬ Full H b)
      (legalQ : Legal H b q) (safeQ : ¬ Wins H (drop b q Q) Q)
      (notFullQ : ¬ Full H (drop b q Q))
      (chosen : f b q s = some (p,next)) (legalP : Legal H (drop b q Q) p) :
      Prefix H f root initial (cost + activeCost H (drop b q Q) q p)
        (drop (drop b q Q) p P) next

/-- Universal quantification over all actual legal prefixes. At every live
prefix, every legal Q move is safe and has a legal selected reply unless full. -/
def HistoryBudget {S : Type} (H : Nat) (f : Controller S) (budget : Nat)
    (root : Board) (initial : S) : Prop :=
  ∀ cost b s, Prefix H f root initial cost b s →
    cost ≤ budget ∧ ¬ Wins H b Q ∧
      (Wins H b P ∨ Full H b ∨ ∀ q, Legal H b q →
        ¬ Wins H (drop b q Q) Q ∧
          (Full H (drop b q Q) ∨ ∃ p next,
            f b q s = some (p,next) ∧ Legal H (drop b q Q) p))

theorem budget_step {S : Type} {H budget : Nat} {f : Controller S}
    {b : Board} {s : S} (safe : BudgetSafe H f budget b s)
    (noP : ¬ Wins H b P) (notFull : ¬ Full H b)
    {q p : Col} {next : S} (legalQ : Legal H b q)
    (notFullQ : ¬ Full H (drop b q Q)) (chosen : f b q s = some (p,next)) :
    activeCost H (drop b q Q) q p ≤ budget ∧
      BudgetSafe H f (budget - activeCost H (drop b q Q) q p)
        (drop (drop b q Q) p P) next := by
  have atHorizon : ∀ k, activeCost H (drop b q Q) q p ≤ budget ∧
      BudgetRoundSafe H f k (budget - activeCost H (drop b q Q) q p)
        (drop (drop b q Q) p P) next := by
    intro k
    rcases (safe (k+1)).2 with win | full | moves
    · exact False.elim (noP win)
    · exact False.elim (notFull full)
    · rcases (moves q legalQ).2 with full | ⟨p',next',eq,_,cost,tail⟩
      · exact False.elim (notFullQ full)
      · have same := Option.some.inj (chosen.symm.trans eq)
        cases same
        exact ⟨cost,tail⟩
  exact ⟨(atHorizon 0).1,fun k => (atHorizon k).2⟩

theorem budget_along_prefix {S : Type} {H budget : Nat} {f : Controller S}
    {root b : Board} {initial s : S} {cost : Nat}
    (safe : BudgetSafe H f budget root initial)
    (run : Prefix H f root initial cost b s) :
    cost ≤ budget ∧ BudgetSafe H f (budget-cost) b s := by
  induction run with
  | nil => exact ⟨Nat.zero_le _,by simpa using safe⟩
  | @step cost b s q p next prior noP noQ notFull legalQ safeQ notFullQ chosen legalP ih =>
      have step := budget_step ih.2 noP notFull legalQ notFullQ chosen
      refine ⟨by omega,?_⟩
      have subtract : budget - (cost + activeCost H (drop b q Q) q p) =
          (budget-cost) - activeCost H (drop b q Q) q p := by omega
      rw [subtract]
      exact step.2

theorem budget_to_history {S : Type} {H budget : Nat} {f : Controller S}
    {root : Board} {initial : S} (safe : BudgetSafe H f budget root initial) :
    HistoryBudget H f budget root initial := by
  intro cost b s run
  have localSafe := budget_along_prefix safe run
  refine ⟨localSafe.1,(localSafe.2 0),?_⟩
  rcases (localSafe.2 1).2 with win | full | moves
  · exact Or.inl win
  · exact Or.inr (Or.inl full)
  · apply Or.inr; apply Or.inr
    intro q hq
    rcases moves q hq with ⟨safeQ, full | ⟨p,next,chosen,legal,_,_⟩⟩
    · exact ⟨safeQ,Or.inl full⟩
    · exact ⟨safeQ,Or.inr ⟨p,next,chosen,legal⟩⟩

theorem history_to_budget {S : Type} {H budget : Nat} {f : Controller S}
    {root : Board} {initial : S} (history : HistoryBudget H f budget root initial) :
    BudgetSafe H f budget root initial := by
  have fromPrefix : ∀ k cost b s, Prefix H f root initial cost b s →
      BudgetRoundSafe H f k (budget-cost) b s := by
    intro k
    induction k with
    | zero => intro cost b s run; exact (history cost b s run).2.1
    | succ k ih =>
        intro cost b s run
        have node := history cost b s run
        refine ⟨node.2.1,?_⟩
        by_cases noP : Wins H b P
        · exact Or.inl noP
        by_cases notFull : Full H b
        · exact Or.inr (Or.inl notFull)
        apply Or.inr; apply Or.inr
        intro q legalQ
        have moves := node.2.2.resolve_left noP |>.resolve_left notFull
        have opponent := moves q legalQ
        refine ⟨opponent.1,?_⟩
        by_cases notFullQ : Full H (drop b q Q)
        · exact Or.inl notFullQ
        rcases opponent.2.resolve_left notFullQ with ⟨p,next,chosen,legalP⟩
        have child := Prefix.step run noP node.2.1 notFull legalQ opponent.1
          notFullQ chosen legalP
        have costBound := (history _ _ _ child).1
        refine Or.inr ⟨p,next,chosen,legalP,by omega,?_⟩
        have subtract : budget - (cost + activeCost H (drop b q Q) q p) =
            (budget-cost) - activeCost H (drop b q Q) q p := by omega
        simpa only [subtract] using ih _ _ _ child
  intro k
  simpa using fromPrefix k 0 root initial Prefix.nil

theorem budgetSafe_iff_historyBudget {S : Type} (H budget : Nat)
    (f : Controller S) (root : Board) (initial : S) :
    BudgetSafe H f budget root initial ↔ HistoryBudget H f budget root initial :=
  ⟨budget_to_history,history_to_budget⟩

/-- Any function of the complete chronological column history is an allowed
controller. No computability or finite-memory premise is imposed on policy. -/
def historyController (policy : List Col → Option Col) : Controller (List Col) :=
  fun _ q history => (policy (history ++ [q])).map
    (fun p => (p,history ++ [q,p]))

#print axioms budgetSafe_iff_historyBudget
end UniformFour.U1
