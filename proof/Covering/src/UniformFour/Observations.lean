import UniformFour.Priority
import UniformFour.RoundFacts

/-! Exact U2 observation specification, independent of a checker implementation.
Reviewed copy. No observations are assumed true by their Boolean values alone. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- a is the actual board after Q's last move, before P's response. -/
def Qualified (H : Nat) (a : Board) (c : Col) : Prop :=
  Legal H a c ∧ Good H (drop a c P)

/-- Precisely the in-board bottom-touching nonvertical lines on four columns. -/
def bottomLines (H : Nat) : List Line :=
  if 4 ≤ H then [.horizontal 1, .rising 1, .falling 4]
  else if 1 ≤ H then [.horizontal 1] else []

def bottomScore (H : Nat) (a : Board) (c : Col) : Nat :=
  ((bottomLines H).filter (hasPBool (drop a c P))).length

def BothCorners (a : Board) : Prop :=
  stoneAt a ⟨c1, 1⟩ = some P ∧ stoneAt a ⟨c4, 1⟩ = some P

/-- All observations match the mathematical U2 rule, not merely some safe rule. -/
structure Observes (H : Nat) (a : Board) (o : Observation) : Prop where
  qualified : ∀ c, o.qualified c = true ↔ Qualified H a c
  immediate : ∀ c, o.immediate c = true ↔ Wins H (drop a c P) P
  bottomScore : ∀ c, o.bottomScore c = UniformFour.U2.bottomScore H a c
  bothCorners : o.bothCorners = true ↔ BothCorners a

/-- Certified legal covering is selected before all other priorities. -/
theorem select_cover_of_qualified {H : Nat} {a : Board} {q : Col} {o : Observation}
    (obs : Observes H a o) (good : Qualified H a q) : select H a q o = some q := by
  have hq := (obs.qualified q).2 good
  have legal : height a q < H := good.1
  simp [select, legal, hq]

/-- Owning both bottom corners also forces legal coverage, as prescribed by U2. -/
theorem select_cover_of_corners {H : Nat} {a : Board} {q : Col} {o : Observation}
    (obs : Observes H a o) (hq : Legal H a q) (corners : BothCorners a) :
    select H a q o = some q := by
  have hc := obs.bothCorners.2 corners
  have legal : height a q < H := hq
  simp [select, legal, hc]

theorem no_qualified_bool {H : Nat} {a : Board} {o : Observation}
    (obs : Observes H a o) (none : ¬ ∃ c, Qualified H a c) :
    ∀ c, o.qualified c = false := by
  intro c
  cases h : o.qualified c with
  | false => rfl
  | true => exact False.elim (none ⟨c, (obs.qualified c).1 h⟩)

/-- With no qualified move and no corner override, U2 executes its exact fallback. -/
theorem select_fallback_of_none {H : Nat} {a : Board} {q : Col} {o : Observation}
    (obs : Observes H a o) (none : ¬ ∃ c, Qualified H a c)
    (corners : ¬ BothCorners a) :
    select H a q o = fallback H a q o.bottomScore := by
  have good := no_qualified_bool obs none
  have notCorners : o.bothCorners = false := by
    cases h : o.bothCorners with
    | false => rfl
    | true => exact False.elim (corners (obs.bothCorners.1 h))
  simp [select, good, notCorners, chooseFirst, allCols]

/-- If a qualified move exists, the only possible nonqualified selection is the
    explicit double-corner override. This theorem does not silently discard it. -/
theorem select_qualified_or_corner_cover {H : Nat} {a : Board} {q c : Col}
    {o : Observation} (obs : Observes H a o) (existsGood : ∃ d, Qualified H a d)
    (chosen : select H a q o = some c) :
    Qualified H a c ∨ (c = q ∧ BothCorners a) := by
  unfold select at chosen
  split at chosen
  next direct =>
    have eq : q = c := Option.some.inj chosen
    subst c
    rcases direct.2 with good | corners
    · exact Or.inl ((obs.qualified q).1 good)
    · exact Or.inr ⟨rfl, obs.bothCorners.1 corners⟩
  next notDirect =>
    dsimp only at chosen
    split at chosen
    next d found =>
      have good := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp (chooseFirst_sound found).2).1).2
      have eq : d = c := Option.some.inj chosen
      subst c
      exact Or.inl ((obs.qualified d).1 good)
    next none =>
      split at chosen
      next d found =>
        have good := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp (chooseFirst_sound found).2).1).2
        have eq : d = c := Option.some.inj chosen
        subst c
        exact Or.inl ((obs.qualified d).1 good)
      next none' =>
        split at chosen
        next d found =>
          have good := ((Bool.and_eq_true _ _).mp (chooseFirst_sound found).2).2
          have eq : d = c := Option.some.inj chosen
          subst c
          exact Or.inl ((obs.qualified d).1 good)
        next noGood =>
          have witness : ∃ d ∈ allCols,
              (decide (height a d < H) && o.qualified d) = true := by
            rcases existsGood with ⟨d, hd⟩
            refine ⟨d, ?_, ?_⟩
            · cases d <;> simp [allCols]
            · have legal : height a d < H := hd.1
              simp [legal, (obs.qualified d).2 hd]
          rcases chooseFirst_complete witness with ⟨d, hd⟩
          rw [noGood] at hd
          cases hd

theorem select_qualified_of_no_corners {H : Nat} {a : Board} {q c : Col}
    {o : Observation} (obs : Observes H a o) (existsGood : ∃ d, Qualified H a d)
    (corners : ¬ BothCorners a) (chosen : select H a q o = some c) :
    Qualified H a c := by
  rcases select_qualified_or_corner_cover obs existsGood chosen with good | corner
  · exact good
  · exact False.elim (corners corner.2)

end UniformFour.U2
