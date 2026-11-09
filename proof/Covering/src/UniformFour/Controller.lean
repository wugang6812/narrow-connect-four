import SafetyKernel
import OddHeight.Assembly
import OddHeight.Capacity

/-!
ADD-ON TO THE FROZEN v2 SOURCES. Reviewed copy.
A controller-parametric safety semantics. This file proves composition and
refinement, not that the U2 certificate library or its openings are closed.
All boards have exactly the four columns in OddHeight.Col.
-/
namespace UniformFour
open OddHeight OddHeight.Player

def legacy (H : Nat) : Controller Phase := OddHeight.reply H

theorem terminal_roundSafe {S : Type} {H : Nat} {f : Controller S} {b : Board}
    (h : OddHeight.SafeTerminal H b) (k : Nat) (s : S) :
    RoundSafe H f k b s := by
  cases k with
  | zero => exact h.1
  | succ k =>
      refine ⟨h.1, ?_⟩
      rcases h.2 with hp | hf
      · exact Or.inl hp
      · exact Or.inr (Or.inl hf)

/-- An explicit proof interface, not an axiom or a U2 instance.
    A final U2 root must construct this record from actual geometry/entry proofs. -/
structure Closed {S : Type} (H : Nat) (f : Controller S)
    (Inv : Board → S → Prop) : Prop where
  state : ∀ b s, Inv b s → Bounded H b ∧ ¬ Wins H b Q
  step : ∀ b s, Inv b s → Live H b → ∀ q, Legal H b q →
    ¬ Wins H (drop b q Q) Q ∧
    (Full H (drop b q Q) ∨
      ∃ c next,
        f b q s = some (c, next) ∧
        Legal H (drop b q Q) c ∧
        (OddHeight.SafeTerminal H (drop (drop b q Q) c P) ∨
         Inv (drop (drop b q Q) c P) next))

theorem closed_safe {S : Type} {H : Nat} {f : Controller S}
    {Inv : Board → S → Prop} (hc : Closed H f Inv)
    {b : Board} {s : S} (entry : Inv b s) : Safe H f b s := by
  intro k
  induction k generalizing b s with
  | zero => exact (hc.state b s entry).2
  | succ k ih =>
      have hs := hc.state b s entry
      refine ⟨hs.2, ?_⟩
      by_cases hp : Wins H b P
      · exact Or.inl hp
      by_cases hf : Full H b
      · exact Or.inr (Or.inl hf)
      apply Or.inr
      apply Or.inr
      intro q hq
      have live : Live H b := ⟨hs.1, hp, hs.2, hf⟩
      rcases hc.step b s entry live q hq with ⟨hn, full | response⟩
      · exact ⟨hn, Or.inl full⟩
      · rcases response with ⟨c, next, heq, legal, terminal | child⟩
        · exact ⟨hn, Or.inr ⟨c, next, heq, legal,
            terminal_roundSafe terminal k next⟩⟩
        · exact ⟨hn, Or.inr ⟨c, next, heq, legal, ih child⟩⟩

/-- All horizons refer to the SAME functional response, so one response works
    for all later horizons. This is not horizon-dependent strategy choice. -/
theorem safe_response {S : Type} {H : Nat} {f : Controller S}
    {b : Board} {s : S} (hs : Safe H f b s)
    (hp : ¬ Wins H b P) (hf : ¬ Full H b)
    (q : Col) (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q ∧
    (Full H (drop b q Q) ∨
      ∃ c next,
        f b q s = some (c, next) ∧
        Legal H (drop b q Q) c ∧
        Safe H f (drop (drop b q Q) c P) next) := by
  have get : ∀ k, ¬ Wins H (drop b q Q) Q ∧
      (Full H (drop b q Q) ∨
        ∃ c next, f b q s = some (c, next) ∧
          Legal H (drop b q Q) c ∧
          RoundSafe H f k (drop (drop b q Q) c P) next) := by
    intro k
    rcases (hs (k + 1)).2 with hw | full | move
    · exact False.elim (hp hw)
    · exact False.elim (hf full)
    · exact move q hq
  refine ⟨(get 0).1, ?_⟩
  by_cases hfull : Full H (drop b q Q)
  · exact Or.inl hfull
  · rcases (get 0).2 with full | ⟨c, next, heq, legal, _⟩
    · exact False.elim (hfull full)
    · refine Or.inr ⟨c, next, heq, legal, ?_⟩
      intro k
      rcases (get k).2 with full | ⟨d, next', heq', _, tail⟩
      · exact False.elim (hfull full)
      · have pair : (c, next) = (d, next') :=
          Option.some.inj (heq.symm.trans heq')
        have cd : c = d := congrArg Prod.fst pair
        have nn : next = next' := congrArg Prod.snd pair
        subst d
        subst next'
        exact tail

theorem safe_reply_total {S : Type} {H : Nat} {f : Controller S}
    {b : Board} {s : S} (hs : Safe H f b s) (live : Live H b)
    {q : Col} (hq : Legal H b q) (hf : ¬ Full H (drop b q Q)) :
    ∃ c next, f b q s = some (c, next) ∧ Legal H (drop b q Q) c := by
  rcases (safe_response hs live.2.1 live.2.2.2 q hq).2 with full | response
  · exact False.elim (hf full)
  · rcases response with ⟨c, next, heq, legal, _⟩
    exact ⟨c, next, heq, legal⟩

/-- Refinement is allowed to change representation/state, but NOT the selected
    physical column. The relation is re-established after the actual Q/P moves.
    Equality is required only where the real first-win driver needs a response.
    This interface has no complexity or generic-certificate soundness claim. -/
structure Refines {S T : Type} (H : Nat) (f : Controller S) (g : Controller T)
    (Rel : Board → S → T → Prop) : Prop where
  step : ∀ b s t, Rel b s t →
    ¬ Wins H b P → ¬ Wins H b Q → ¬ Full H b →
    ∀ q, Legal H b q → ¬ Wins H (drop b q Q) Q → ¬ Full H (drop b q Q) →
    ∀ c next, f b q s = some (c, next) →
    ∃ next', g b q t = some (c, next') ∧
      Rel (drop (drop b q Q) c P) next next'

theorem refinement_roundSafe {S T : Type} {H : Nat}
    {f : Controller S} {g : Controller T} {Rel : Board → S → T → Prop}
    (simulation : Refines H f g Rel) (k : Nat) {b : Board} {s : S} {t : T}
    (rel : Rel b s t) (safe : RoundSafe H f k b s) :
    RoundSafe H g k b t := by
  induction k generalizing b s t with
  | zero => exact safe
  | succ k ih =>
      refine ⟨safe.1, ?_⟩
      by_cases hp : Wins H b P
      · exact Or.inl hp
      by_cases hf : Full H b
      · exact Or.inr (Or.inl hf)
      apply Or.inr
      apply Or.inr
      have moves : ∀ q, Legal H b q →
          ¬ Wins H (drop b q Q) Q ∧
          (Full H (drop b q Q) ∨ ∃ c next,
            f b q s = some (c, next) ∧ Legal H (drop b q Q) c ∧
            RoundSafe H f k (drop (drop b q Q) c P) next) := by
        rcases safe.2 with win | full | moves
        · exact False.elim (hp win)
        · exact False.elim (hf full)
        · exact moves
      intro q hq
      have response := moves q hq
      refine ⟨response.1, ?_⟩
      by_cases fullQ : Full H (drop b q Q)
      · exact Or.inl fullQ
      · rcases response.2 with full | ⟨c, next, heq, legal, tail⟩
        · exact False.elim (fullQ full)
        · rcases simulation.step b s t rel hp safe.1 hf q hq response.1 fullQ
            c next heq with ⟨next', heq', rel'⟩
          exact Or.inr ⟨c, next', heq', legal, ih rel' tail⟩

theorem refinement_safe {S T : Type} {H : Nat}
    {f : Controller S} {g : Controller T} {Rel : Board → S → T → Prop}
    (simulation : Refines H f g Rel) {b : Board} {s : S} {t : T}
    (rel : Rel b s t) (safe : Safe H f b s) : Safe H g b t :=
  fun k => refinement_roundSafe simulation k rel (safe k)

/-- Regression bridge to v2. No claim is made that U2 equals the old phase policy. -/
theorem legacy_roundSafe_iff (H k : Nat) (b : Board) (ph : Phase) :
    RoundSafe H (legacy H) k b ph ↔ OddHeight.RoundsSafe H k b ph := by
  induction k generalizing b ph with
  | zero => rfl
  | succ k ih =>
      simp only [legacy] at ih
      simp only [RoundSafe, OddHeight.RoundsSafe, legacy, ih]

theorem legacy_safe_iff (H : Nat) (b : Board) (ph : Phase) :
    Safe H (legacy H) b ph ↔ OddHeight.AllRoundsSafe H b ph := by
  constructor
  · intro h k
    exact (legacy_roundSafe_iff H k b ph).1 (h k)
  · intro h k
    exact (legacy_roundSafe_iff H k b ph).2 (h k)

/-- Finite-board termination is independent of the response algorithm or encoding. -/
theorem physical_history_length {H n : Nat} {b z : Board}
    (bounded : Bounded H b) (moves : OddHeight.Moves H n b z) :
    n ≤ OddHeight.remaining H b := OddHeight.moves_length_le moves bounded

#print axioms closed_safe
#print axioms refinement_safe
#print axioms legacy_safe_iff
end UniformFour
