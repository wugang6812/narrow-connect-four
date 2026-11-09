import UniformFour.CertificateController
import UniformFour.OpeningFallback

/-! Complete first-player safety assembly for the actual U2 response, at every
positive finite height. All branch proofs are concrete imports. Reviewed copy. -/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- A proof invariant only. The controller stores no indication of this disjunction. -/
def FirstInvariant (H : Nat) (b : Board) : Prop :=
  Certificate H b ∨ FirstPending H b

theorem first_invariant_closed (H : Nat) :
    UniformFour.Closed H (UniformFour.stateless (respond H))
      (fun b _ => FirstInvariant H b) := by
  constructor
  · intro b unit h
    rcases h with certificate | pending
    · exact ⟨certificate.1.1.1, certificate.1.1.2.2.1⟩
    · exact pending_state_safe pending
  · intro b unit h live q hq
    rcases h with certificate | pending
    · rcases (certificate_closed H).step b unit certificate live q hq with
        ⟨safeQ, full | ⟨p, next, chosen, legal, terminal | successor⟩⟩
      · exact ⟨safeQ, Or.inl full⟩
      · exact ⟨safeQ, Or.inr ⟨p, next, chosen, legal, Or.inl terminal⟩⟩
      · exact ⟨safeQ, Or.inr ⟨p, next, chosen, legal, Or.inr (Or.inl successor)⟩⟩
    · rcases pending_selected_step pending hq (referenceObserves H (drop b q Q)) with
        ⟨safeQ, full | ⟨p, chosen, legal, good | successor⟩⟩
      · exact ⟨safeQ, Or.inl full⟩
      · refine ⟨safeQ, Or.inr ⟨p, (), ?_, legal, ?_⟩⟩
        · simp only [UniformFour.stateless, respond, chosen, Option.map_some]
        · rcases good with terminal | certificate
          · exact Or.inl terminal
          · exact Or.inr (Or.inl certificate)
      · refine ⟨safeQ, Or.inr ⟨p, (), ?_, legal, Or.inr (Or.inr successor)⟩⟩
        simp only [UniformFour.stateless, respond, chosen, Option.map_some]

theorem firstBoard_invariant {H : Nat} (positive : 0 < H) :
    FirstInvariant H firstBoard := by
  by_cases small : H ≤ 3
  · exact Or.inl (firstBoard_certificate_small (by omega) small)
  by_cases odd : H % 2 = 1
  · exact Or.inl (firstBoard_certificate_odd odd)
  · have even : H % 2 = 0 := by omega
    exact Or.inr (firstBoard_pending_even even (by omega))

/-- No extra closure, strategy-existence, or certificate hypothesis remains. -/
theorem first_allSafe {H : Nat} (positive : 0 < H) :
    UniformFour.Safe H (UniformFour.stateless (respond H)) firstBoard () :=
  UniformFour.closed_safe (first_invariant_closed H) (firstBoard_invariant positive)

#print axioms first_invariant_closed
#print axioms first_allSafe
end UniformFour.U2
