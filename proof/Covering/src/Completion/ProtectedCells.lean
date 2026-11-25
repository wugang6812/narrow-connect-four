import Completion.Reserves
import UniformFour.CClosure

namespace UniformFour.Reserves
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2 UniformFour.U1

/-- Only moves concerning j are constrained. The opponent may visit any column.
A legal cover in j is compulsory, and unsolicited entries by P are forbidden. -/
inductive CoversColumn (H : Nat) (j : Col) (root : Board) : Board → Prop
  | start : CoversColumn H j root root
  | step {b q p} : CoversColumn H j root b → Legal H b q → Legal H (drop b q Q) p →
      (q = j → Legal H (drop b q Q) j → p = j) → (p = j → q = j) →
      CoversColumn H j root (afterRound b q p)

private theorem protected_round {H b x q p} (old : Protected H b x)
    (cover : q = x.col → Legal H (drop b q Q) x.col → p = x.col)
    (only : p = x.col → q = x.col) : Protected H (afterRound b q p) x := by
  by_cases same : p = q
  · subst p; exact protected_after_cover old q
  rcases old.2 with held | ⟨_,pos,even⟩
  · exact ⟨old.1,Or.inl (stoneAt_drop_preserves (stoneAt_drop_preserves held q Q) p P)⟩
  have roof := old.1.2
  have qout : q ≠ x.col := by
    intro he
    have room : Legal H (drop b q Q) x.col := by
      unfold Legal
      rw [← he,height_drop_same]
      rw [← he] at pos even
      omega
    exact same ((cover he room).trans he.symm)
  have pout : p ≠ x.col := fun eq => qout (only eq)
  have ht : height (afterRound b q p) x.col = height b x.col := by
    simp [afterRound,height,drop,Ne.symm qout,Ne.symm pout]
  have ahead : height (afterRound b q p) x.col < x.row := by rw [ht]; exact pos
  exact ⟨old.1,Or.inr ⟨cell_empty_above_height ahead,ahead,by rw [ht]; exact even⟩⟩

theorem protected_cell_history {H root b x} (old : Protected H root x)
    (path : CoversColumn H x.col root b) :
    Protected H b x ∧ ∀ q, stoneAt (drop b q Q) x ≠ some Q := by
  have keep : Protected H b x := by
    induction path with
    | start => exact old
    | step _ _ _ cover only ih => exact protected_round ih cover only
  exact ⟨keep,protected_not_Q_after_move keep⟩

/-- Paper Lemma 3, at every completed round and also immediately after Q moves. -/
theorem even_distance_protected {H root b j k} (pos : 0 < k)
    (inside : height root j + 2*k ≤ H) (path : CoversColumn H j root b) :
    let x : Cell := ⟨j,height root j + 2*k⟩
    Protected H b x ∧ ∀ q, stoneAt (drop b q Q) x ≠ some Q := by
  apply protected_cell_history (root := root) _ path
  apply protected_of_even_height_gap
  · exact ⟨by dsimp; omega,inside⟩
  · dsimp; omega
  · dsimp; omega

private theorem data_single {H b t} {k : Kind}
    (cond : TargetCondition H b t) (typed : Typed H b k t)
    (guard : ∀ L, Unresolved H b L → Guards k t L) : Data H b (fun _ => k) [t] := by
  refine ⟨?_,?_,fun _ => cond.outsideEven,?_,?_⟩
  · intro u hu v hv; simp_all
  · intro u hu; obtain rfl := List.mem_singleton.mp hu
    exact ⟨cond.positive,cond.evenGap,cond.inBoard.2⟩
  · intro u hu; simpa only [List.mem_singleton.mp hu] using typed
  · exact fun L bad => ⟨t,by simp,guard L bad⟩

/-- Every branch stops at an earlier P win or reaches the target while the last
opponent move was still safe. A capture explicitly carries its promised exit. -/
inductive Takes (H : Nat) (t : Target) (exit : Board → Prop) : Board → Prop
  | earlier {b} : ¬ Wins H b Q → Wins H b P → Takes H t exit b
  | captured {b} : ¬ Wins H b Q → stoneAt b (targetCell t) = some P →
      exit b → Takes H t exit b
  | step {b} : Common H b →
      (∀ q, Legal H b q → ¬ Wins H (drop b q Q) Q ∧ ¬ Full H (drop b q Q) ∧
        ∃ p, Reply H b [t] q p) →
      (∀ q, Legal H b q → ∀ p, Reply H b [t] q p → Takes H t exit (afterRound b q p)) →
      Takes H t exit b

private def One (H : Nat) (b : Board) (t : Target) (win : Bool) : Prop :=
  if win then A2Data H b t else A1Data H b t
private def Exit (H : Nat) (win : Bool) (b : Board) : Prop :=
  if win then Wins H b P else A0 H b

private theorem takes_one {H b t win} (common : Common H b) (arg : One H b t win) :
    Takes H t (Exit H win) b := by
  have cond : TargetCondition H b t := by cases win <;> exact arg.target
  let k : Kind := if win then .winning else .blocking
  have d : Data H b (fun _ => k) [t] := by
    cases win with
    | false => exact data_single cond arg.commonTarget arg.commonTarget
    | true => exact data_single cond arg.fixedWin arg.commonUpperColumn
  have opponent {q} (hq : Legal H b q) : ¬ Wins H (drop b q Q) Q ∧ ¬ Full H (drop b q Q) := by
    refine ⟨?_,?_⟩
    · cases win with
      | false => exact a1_Q_move_safe common ⟨t,arg⟩ hq
      | true => exact a2_Q_move_safe common ⟨t,arg⟩ hq
    · have gap := target_room cond
      have bound := height_after_move_le b q t.col Q
      have roof := cond.inBoard.2
      change t.row ≤ H at roof
      intro full
      have filled := full t.col
      omega
  refine .step common (fun q hq => ⟨(opponent hq).1,(opponent hq).2,
    reply_exists d common.1.1 hq (opponent hq).2⟩) ?_
  intro q hq p r
  have obey : TargetRound H b t q p := by
    refine ⟨r.covers,?_⟩
    intro outside
    exact (inJ_singleton_false t p).1 (r.outside ((inJ_singleton_false t q).2 outside))
  have cover := targetRound_cover_or_full common.1.1 hq obey
  have st := structural_after_cover (common_structural common) hq r.legal (opponent hq).1 cover
  rcases target_after_round cond hq r.legal obey with hit | pending
  · refine .captured st.noQ hit ?_
    cases win with
    | false => exact a1_capture_is_a0 arg hq cover hit
    | true => exact a2_capture_wins q p arg hit
  · by_cases won : Wins H (afterRound b q p) P
    · exact .earlier st.noQ won
    have space : ¬ Full H (afterRound b q p) := by
      intro filled
      have h1 := pending.positive
      have h2 := pending.inBoard.2
      change t.row ≤ H at h2
      have h3 := filled t.col
      omega
    have next := common_after_cover common hq r.legal (opponent hq).1 cover won space
    apply takes_one next
    cases win with
    | false => exact ⟨pending,fun L hL => arg.commonTarget L (unresolved_after_cover_subset hq cover hL)⟩
    | true => exact ⟨pending,fixedWinningTarget_preserved arg.fixedWin q p,
        fun L hL => arg.commonUpperColumn L (unresolved_after_cover_subset hq cover hL)⟩
termination_by remaining H b
decreasing_by
  have step := remaining_round common.1.1 hq r.legal
  unfold afterRound
  omega

theorem one_blocking_target {H b t} (common : Common H b) (arg : A1Data H b t) :
    (Takes H t (A0 H) b ∧ Resolves H (fun _ => .blocking) b [t]) ∧
    HistoryBudget H (reservePolicy H (fun _ => .blocking)) 0 b [t] := by
  have multi := multitarget_resource common (data_single (k := .blocking) arg.target arg.commonTarget arg.commonTarget)
  exact ⟨⟨takes_one (win := false) common arg,multi.1⟩,multi.2⟩

theorem one_winning_target {H b t} (common : Common H b) (arg : A2Data H b t) :
    (Takes H t (fun z => Wins H z P) b ∧ Resolves H (fun _ => .winning) b [t]) ∧
    HistoryBudget H (reservePolicy H (fun _ => .winning)) 0 b [t] := by
  have multi := multitarget_resource common (data_single (k := .winning) arg.target arg.fixedWin arg.commonUpperColumn)
  exact ⟨⟨takes_one (win := true) common arg,multi.1⟩,multi.2⟩

#print axioms even_distance_protected
#print axioms one_blocking_target
#print axioms one_winning_target
end UniformFour.Reserves
