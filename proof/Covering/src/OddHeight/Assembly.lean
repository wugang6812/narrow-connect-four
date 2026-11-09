import OddHeight.Families

namespace OddHeight
open Player

/-- A reached terminal is safe only if Q has not already won. -/
def SafeTerminal (H : Nat) (b : Board) : Prop :=
  ¬ Wins H b Q ∧ (Wins H b P ∨ Full H b)

/-- Safety for a fixed executable controller over k complete Q/P rounds.
    Q's win test is BEFORE the existence of a P response.
    A full board after Q needs no response. A P win at entry stops the game. -/
def RoundsSafe (H : Nat) : Nat → Board → Phase → Prop
  | 0, b, _ => ¬ Wins H b Q
  | k + 1, b, ph =>
      ¬ Wins H b Q ∧
      (Wins H b P ∨ Full H b ∨
        ∀ q, Legal H b q →
          ¬ Wins H (drop b q Q) Q ∧
          (Full H (drop b q Q) ∨
            ∃ c next,
              reply H b q ph = some (c, next) ∧
              Legal H (drop b q Q) c ∧
              RoundsSafe H k (drop (drop b q Q) c P) next))

def AllRoundsSafe (H : Nat) (b : Board) (ph : Phase) : Prop :=
  ∀ k, RoundsSafe H k b ph

theorem terminal_rounds_safe {H : Nat} {b : Board} (ht : SafeTerminal H b)
    (k : Nat) (ph : Phase) : RoundsSafe H k b ph := by
  cases k with
  | zero => exact ht.1
  | succ k =>
      refine ⟨ht.1, ?_⟩
      rcases ht.2 with hp | hf
      · exact Or.inl hp
      · exact Or.inr (Or.inl hf)

/-- Local proof obligations for a fixed controller. No global nonloss field is assumed. -/
structure ClosedInvariant (H : Nat) (Inv : Board → Phase → Prop) : Prop where
  stateSafe : ∀ b ph, Inv b ph → Bounded H b ∧ ¬ Wins H b Q
  step : ∀ b ph, Inv b ph → Live H b → ∀ q, Legal H b q →
    ¬ Wins H (drop b q Q) Q ∧
    (Full H (drop b q Q) ∨
      ∃ c next,
        reply H b q ph = some (c, next) ∧
        Legal H (drop b q Q) c ∧
        (SafeTerminal H (drop (drop b q Q) c P) ∨
         Inv (drop (drop b q Q) c P) next))

/-- Generic induction is supplied. The phase-specific geometry is NOT supplied by this theorem. -/
theorem invariant_all_rounds_safe {H : Nat} {Inv : Board → Phase → Prop}
    (closed : ClosedInvariant H Inv) {b : Board} {ph : Phase} (hb : Inv b ph) :
    AllRoundsSafe H b ph := by
  intro k
  induction k generalizing b ph with
  | zero => exact (closed.stateSafe b ph hb).2
  | succ k ih =>
      have hs := closed.stateSafe b ph hb
      refine ⟨hs.2, ?_⟩
      by_cases hp : Wins H b P
      · exact Or.inl hp
      by_cases hf : Full H b
      · exact Or.inr (Or.inl hf)
      apply Or.inr
      apply Or.inr
      intro q hq
      have hl : Live H b := ⟨hs.1, hp, hs.2, hf⟩
      rcases closed.step b ph hb hl q hq with ⟨hn, hend | hreply⟩
      · exact ⟨hn, Or.inl hend⟩
      · rcases hreply with ⟨c, next, heq, hlegal, hterminal | hinv⟩
        · exact ⟨hn, Or.inr ⟨c, next, heq, hlegal, terminal_rounds_safe hterminal k next⟩⟩
        · exact ⟨hn, Or.inr ⟨c, next, heq, hlegal, ih hinv⟩⟩

/-- Proposed proof invariant. Raw shape membership is NOT enough: initial no-Q and bounds matter. -/
def ClaudeInvariant (H : Nat) (b : Board) (ph : Phase) : Prop :=
  Bounded H b ∧ ¬ Wins H b Q ∧ PhaseInvariant H b ph

/-- CONDITIONAL assembly. `closed` is the main unfinished geometric/F1 proof obligation. -/
theorem claude_round_safety {H : Nat}
    (closed : ClosedInvariant H (ClaudeInvariant H))
    {b : Board} {ph : Phase} (entry : ClaudeInvariant H b ph) :
    AllRoundsSafe H b ph :=
  invariant_all_rounds_safe closed entry

#print axioms invariant_all_rounds_safe
#print axioms claude_round_safety

end OddHeight
