import UniformFour.CertificateController
import UniformFour.SecondEntry

/-! Actual U2 second-player root, including zero height. Reviewed copy.
The opening witness never replaces the exact select response. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

theorem zero_empty_terminal : SafeTerminal 0 empty := by
  refine ⟨empty_no_win 0 Q, Or.inr ?_⟩
  intro c
  cases c <;> rfl

/-- The empty board is a Q-turn root for the second player. Same respond function
as first_allSafe, with no first/second role input and no parity action table. -/
theorem second_allSafe (H : Nat) :
    UniformFour.Safe H (UniformFour.stateless (respond H)) empty () := by
  by_cases zero : H = 0
  · subst H
    intro k
    exact UniformFour.terminal_roundSafe zero_empty_terminal k ()
  have positive : 0 < H := by omega
  intro k
  cases k with
  | zero => exact empty_no_win H Q
  | succ k =>
      refine ⟨empty_no_win H Q, Or.inr (Or.inr ?_)⟩
      intro q hq
      refine ⟨oneStone_no_win H q Q, ?_⟩
      by_cases full : Full H (drop empty q Q)
      · exact Or.inl full
      · rcases select_total_legal (q := q) (o := referenceObservation H (drop empty q Q))
          (drop_bounded (empty_bounded H) hq Q) full with ⟨p, chosen, legal⟩
        have good := second_selected_opening_good positive
          (referenceObserves H (drop empty q Q)) chosen
        refine Or.inr ⟨p, (), ?_, legal, ?_⟩
        · simp only [UniformFour.stateless, respond, chosen, Option.map_some]
        · rcases good.2 with terminal | certificate
          · exact UniformFour.terminal_roundSafe terminal k ()
          · exact certificate_allSafe certificate k

#print axioms second_allSafe
end UniformFour.U2
