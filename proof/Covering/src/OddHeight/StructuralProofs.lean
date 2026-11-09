import OddHeight.Assembly
import OddHeight.Permanent
import OddHeight.CandidateCapacity

/-!
C6 and the combined permanent/candidate tail invariant.
No safety/closure interface is assumed: both local cases are instantiated from
the spatial support, actual exception, vertical-run and capacity lemmas.
These are reviewed Lean scripts; see the local validation records.
-/
namespace OddHeight
open Player

/-- A target is still above the current column, so the candidate board is not full. -/
theorem candidate_not_full {H : Nat} {b : Board} {L : Line}
    {ts : List Target} (h : CandidateHyp H b L ts) : ¬ Full H b := by
  rcases h with ⟨E, d⟩
  intro full
  cases ts with
  | nil => exact d.nonempty rfl
  | cons t rest =>
      have ht : t ∈ t :: rest := by simp
      have hp := d.positive t ht
      have hr := d.belowRoof t ht
      have hf := full t.col
      omega

/-- C6 excludes Q's win BEFORE a P response is chosen. -/
theorem candidate_Q_move_safe {H : Nat} {b : Board} {L : Line}
    {ts : List Target} {E : Cell → Prop}
    (data : CandidateData H b L ts E) (hnoP : ¬ Wins H b P)
    {q : Col} (hq : Legal H b q) : ¬ Wins H (drop b q Q) Q := by
  rintro ⟨M, hv, hall⟩
  have hex := existing_exception_after_Q_in_E data.structural.complete hq
  cases M with
  | vertical c r =>
      exact vertical_Q_after_move_impossible hq data.structural.noQ
        data.structural.topRun c r hv hall
  | horizontal r =>
      exact candidate_excludes_nonvertical_after_Q data q hnoP hex hv trivial hall
  | rising r =>
      exact candidate_excludes_nonvertical_after_Q data q hnoP hex hv trivial hall
  | falling r =>
      exact candidate_excludes_nonvertical_after_Q data q hnoP hex hv trivial hall

/-- Only proved static certificates, not nonloss itself, occur in this invariant. -/
def TailInvariant (H : Nat) (b : Board) : Phase → Prop
  | .candidate L ts => CandidateHyp H b L ts
  | .permanent => PermanentHyp H b
  | _ => False

/-- The full C6 local step: actual legal reply, unchanged candidates or permanent
defence after a hit. A full Q board is handled without any extra P move. -/
theorem candidate_local_step {H : Nat} {b : Board} {L : Line}
    {ts : List Target} (data : CandidateHyp H b L ts)
    (hnoP : ¬ Wins H b P) {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q ∧
    (Full H (drop b q Q) ∨ ∃ p next,
      reply H b q (.candidate L ts) = some (p, next) ∧
      Legal H (drop b q Q) p ∧
      TailInvariant H (drop (drop b q Q) p P) next) := by
  rcases data with ⟨E, data⟩
  have safeQ := candidate_Q_move_safe data hnoP hq
  refine ⟨safeQ, ?_⟩
  by_cases fullQ : Full H (drop b q Q)
  · exact Or.inl fullQ
  · right
    rcases candidate_reply_legal data hq fullQ with ⟨p, raw, legalP, cover, outsideP⟩
    have coverOrFull : p = q ∨ height (drop b q Q) q = H := by
      by_cases fullColumn : height (drop b q Q) q = H
      · exact Or.inr fullColumn
      · have bound := drop_bounded data.structural.bounded hq Q q
        exact Or.inl (cover (by omega))
    have structureAfter := structural_after_cover data.structural hq legalP safeQ coverOrFull
    cases hit : ts.any (fun t =>
        stoneAt (drop (drop b q Q) p P) (targetCell t) == some P) with
    | true =>
        refine ⟨p, .permanent, ?_, legalP, ?_⟩
        · simp only [reply, raw, Option.map_some, settle, hit, ite_true]
        · apply candidate_hit_permanent data structureAfter
          · intro M hm
            exact hasP_drop_preserves (hasP_drop_preserves hm q Q) p P
          · exact hit
    | false =>
        refine ⟨p, .candidate L ts,
          candidate_reply_phase_no_hit raw hit, legalP, E, ?_⟩
        exact candidateData_after_round_no_hit data hq legalP cover outsideP structureAfter hit

/-- All obligations of the earlier generic contract are now discharged for the
two tail modes. No `ClosedInvariant` assumption survives in this declaration. -/
theorem tail_invariant_closed (H : Nat) : ClosedInvariant H (TailInvariant H) := by
  constructor
  · intro b ph inv
    cases ph with
    | innerWait => exact False.elim inv
    | outerWait => exact False.elim inv
    | delay => exact False.elim inv
    | candidate L ts =>
        rcases inv with ⟨E, d⟩
        exact ⟨d.structural.bounded, d.structural.noQ⟩
    | permanent =>
        rcases inv with ⟨E, d⟩
        exact ⟨d.structural.bounded, d.structural.noQ⟩
  · intro b ph inv live q legalQ
    have noP := live.2.1
    cases ph with
    | innerWait => exact False.elim inv
    | outerWait => exact False.elim inv
    | delay => exact False.elim inv
    | candidate L ts =>
        rcases candidate_local_step inv noP legalQ with ⟨safeQ, fullQ | response⟩
        · exact ⟨safeQ, Or.inl fullQ⟩
        · rcases response with ⟨p, next, hr, hp, hn⟩
          exact ⟨safeQ, Or.inr ⟨p, next, hr, hp, Or.inr hn⟩⟩
    | permanent =>
        rcases permanent_local_step inv noP legalQ with ⟨safeQ, fullQ | response⟩
        · exact ⟨safeQ, Or.inl fullQ⟩
        · rcases response with ⟨p, hr, hp, hn⟩
          exact ⟨safeQ, Or.inr ⟨p, .permanent, hr, hp, Or.inr hn⟩⟩

/-- L4 for every finite horizon of the single fixed executable controller. -/
theorem permanent_allRoundsSafe {H : Nat} {b : Board}
    (h : PermanentHyp H b) : AllRoundsSafe H b .permanent := by
  exact invariant_all_rounds_safe (tail_invariant_closed H)
    (show TailInvariant H b .permanent from h)

/-- C6 for every finite horizon of the single fixed executable controller.
All candidate geometry/capacity obligations are concrete static premises;
no unproved tail safety or strategy closure is accepted as an argument. -/
theorem candidate_allRoundsSafe {H : Nat} {b : Board} {L : Line}
    {ts : List Target} (h : CandidateHyp H b L ts) :
    AllRoundsSafe H b (.candidate L ts) := by
  exact invariant_all_rounds_safe (tail_invariant_closed H)
    (show TailInvariant H b (.candidate L ts) from h)

#print axioms candidate_Q_move_safe
#print axioms candidate_local_step
#print axioms tail_invariant_closed
#print axioms permanent_allRoundsSafe
#print axioms candidate_allRoundsSafe
end OddHeight
