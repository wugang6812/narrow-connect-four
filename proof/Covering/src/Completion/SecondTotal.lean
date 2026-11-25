import Completion.TotalSwitch

namespace UniformFour.PaperOne
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U1 UniformFour.U2

inductive Stage | opening | waiting | paired deriving DecidableEq
open Stage

private def outer (q : Col) : Prop := q = c1 ∨ q = c4
private def cross : Col → Col | c1 | c2 => c3 | c3 | c4 => c2

private noncomputable def otherOdd (H : Nat) (b : Board) (q : Col) : Col := by
  classical
  exact if h : ∃ t, q ≠ t ∧ OddColumn H b t then h.choose else q

private noncomputable def plan (H : Nat) (b : Board) (q : Col) (s : Stage) : Col × Stage := by
  classical
  exact match s with
  | opening => if H % 2 = 1 ∧ 3 ≤ H ∧ outer q then (q,waiting) else (partner q,paired)
  | waiting => if outer q ∧ Legal H (drop b q Q) q then (q,waiting) else (cross q,paired)
  | paired => if Legal H (drop b q Q) q then (q,paired) else (otherOdd H b q,paired)

noncomputable def secondPaper (H : Nat) : Controller Stage := fun b q s => some (plan H b q s)

private def Inv (H : Nat) (b : Board) : Stage → Prop
  | opening => b = empty
  | waiting => Good H b ∧ C H b
  | paired => Good H b ∧ B H b

private def remActive (H : Nat) : Stage → Nat
  | opening => secondBudget H | waiting => 1 | paired => 0

private def remTotal (H : Nat) (b : Board) : Stage → Nat
  | opening | waiting => 2
  | paired => if oddColumns H b = [] then 0 else 1

private def Correct (H : Nat) (b : Board) (q : Col) (s : Stage) (p : Col) (next : Stage) : Prop :=
  Legal H (drop b q Q) p ∧ Inv H (afterRound b q p) next ∧
  activeCost H (drop b q Q) q p + remActive H next ≤ remActive H s ∧
  switch q p + remTotal H (afterRound b q p) next ≤ remTotal H b s

private theorem paired_cap (H : Nat) (b : Board) : remTotal H b paired ≤ 1 := by
  change (if oddColumns H b = [] then 0 else 1) ≤ 1
  split <;> decide

private theorem paired_step {H b q} (common : Common H b) (body : B H b) (hq : Legal H b q) :
    Correct H b q paired (plan H b q paired).1 (plan H b q paired).2 := by
  classical
  by_cases cover : Legal H (drop b q Q) q
  · simp only [plan,cover, ↓reduceIte]
    refine ⟨cover, ⟨b_cover_good common body hq cover, b_cover_body body hq cover⟩, ?_, ?_⟩
    · simp [activeCost,remActive]
    · simp [switch,remTotal,odd_columns_cover cover]
  · have bound := drop_bounded common.1.1 hq Q q
    have full : height (drop b q Q) q = H := by unfold Legal at cover; omega
    obtain ⟨t,ne,pair⟩ := b_other_odd body (full_move_was_odd hq full)
    have ex : ∃ t, q ≠ t ∧ OddColumn H b t := ⟨t,ne,(pair t).2 (Or.inr rfl)⟩
    have chosen : otherOdd H b q = t := by
      rw [otherOdd, dif_pos ex]
      exact ((pair ex.choose).1 ex.choose_spec.2).resolve_left (Ne.symm ex.choose_spec.1)
    have old : oddColumns H b ≠ [] := by
      have len := odd_pair_length ne pair
      intro nil; simp [nil] at len
    have newCols := odd_columns_nil_of_even (full_transfer_all_even ne full pair)
    have good := b_full_good common body hq ne full pair
    simp only [plan,cover, ↓reduceIte,chosen]
    refine ⟨good.1, ⟨good.2,b_full_body body hq ne full pair⟩, ?_, ?_⟩
    · simp [activeCost,cover,remActive]
    · simp [switch,Ne.symm ne,remTotal,newCols,old]

private theorem waiting_step {H b q} (common : Common H b) (body : C H b) (hq : Legal H b q) :
    Correct H b q waiting (plan H b q waiting).1 (plan H b q waiting).2 := by
  classical
  have onCover (out : outer q) (hp : Legal H (drop b q Q) q) :
      Correct H b q waiting q waiting := by
    exact ⟨hp, ⟨c_cover_good common body hq out hp,c_cover_body body out hp⟩,
      by simp [activeCost,remActive],by simp [switch,remTotal]⟩
  have onExit {p : Col} {E : Cell → Prop} (hp : Legal H (drop b q Q) p)
      (st : Structural H (afterRound b q p) E) (ex : B H (afterRound b q p)) :
      Correct H b q waiting p paired := by
    refine ⟨hp, ⟨good_of_structural st (fun _ _ => Or.inr (Or.inl ex)), ex⟩, ?_, ?_⟩
    · simpa [remActive] using activeCost_le_one H (drop b q Q) q p
    · have cap := paired_cap H (afterRound b q p)
      change switch q p + _ ≤ 2
      unfold switch; split <;> omega
  by_cases stay : outer q ∧ Legal H (drop b q Q) q
  · simpa [plan,stay] using onCover stay.1 stay.2
  simp only [plan,stay,↓reduceIte]
  have odd := c_height_odd body
  have h3 := c_height_at_least_three common.1.1 body
  obtain ⟨a,d,rfl,pos⟩ := c_outer_shape body
  have ha : 2*a ≤ H := by simpa using common.1.1 c1
  have hd : 2*d ≤ H := by simpa using common.1.1 c4
  have hp : Legal H (drop (outerBoard a d) q Q) (cross q) := by
    cases q <;> simp [cross,Legal,height,drop,outerBoard,board] <;> omega
  have casesExit : ∃ E, Structural H (afterRound (outerBoard a d) q (cross q)) E ∧
      B H (afterRound (outerBoard a d) q (cross q)) := by
    cases q with
    | c1 =>
      have cut : ¬ Legal H (drop (outerBoard a d) c1 Q) c1 := fun hc => stay ⟨Or.inl rfl,hc⟩
      have bound := drop_bounded common.1.1 hq Q c1
      simp only [Legal,height_drop_same,outer_height_one] at cut bound
      have full : 2*a+1 = H := by omega
      simp only [cross,afterRound,outer_event1_shape]
      exact ⟨_,second_endpoint_structural (SecondEndpoint.event3 a d full hd (by omega)),
        c_left_full_B odd full hd h3⟩
    | c2 =>
      simp only [cross,afterRound,outer_event2_shape]
      exact ⟨_,(middle_event_elementary (by omega : 1 ≤ H) ha hd).1.structural,
        (c_middle_events_B odd ha hd pos).1⟩
    | c3 =>
      simp only [cross,afterRound,outer_event3_shape]
      exact ⟨_,(middle_event_elementary (by omega : 1 ≤ H) ha hd).2.structural,
        (c_middle_events_B odd ha hd pos).2⟩
    | c4 =>
      have cut : ¬ Legal H (drop (outerBoard a d) c4 Q) c4 := fun hc => stay ⟨Or.inr rfl,hc⟩
      have bound := drop_bounded common.1.1 hq Q c4
      simp only [Legal,height_drop_same,outer_height_four] at cut bound
      have full : 2*d+1 = H := by omega
      simp only [cross,afterRound,outer_event4_shape]
      exact ⟨_,second_endpoint_structural (SecondEndpoint.event4 a d ha full (by omega)),
        c_right_full_B odd ha full h3⟩
  obtain ⟨_,st,bc⟩ := casesExit
  exact onExit hp st bc

private theorem opening_step {H q} (hq : Legal H empty q) :
    Correct H empty q opening (plan H empty q opening).1 (plan H empty q opening).2 := by
  classical
  have positive : 0 < H := by cases q <;> simpa [Legal,height,empty,board] using hq
  by_cases wait : H%2 = 1 ∧ 3 ≤ H ∧ outer q
  · simp only [plan,wait]
    have entry := odd_outer_opening_good wait.1 wait.2.1 wait.2.2
    refine ⟨entry.1, ⟨entry.2,odd_outer_opening_C wait.1 wait.2.1 wait.2.2⟩, ?_, ?_⟩
    · have two : 2 ≤ H := by have := wait.2.1; omega
      simp [activeCost,remActive,secondBudget,two]
    · simp [switch,remTotal]
  simp only [plan,wait,↓reduceIte]
  have body : B H (afterRound empty q (partner q)) := by
    by_cases one : H = 1
    · subst H
      apply b_of_outside_odd_guards (Or.inr (by cases q <;> decide))
      exact fun L hL => False.elim (height_one_cross_A0 q L hL)
    by_cases odd : H%2 = 1
    · have three : 3 ≤ H := by omega
      have inner : q = c2 ∨ q = c3 := by
        cases q <;> simp_all [outer]
      exact odd_inner_opening_B odd inner
    exact even_cross_opening_B (by omega) positive q
  have good := good_of_structural (cross_opening_structural positive q)
    (fun _ _ => Or.inr (Or.inl body))
  refine ⟨cross_opening_legal positive q, ⟨good,body⟩, ?_, ?_⟩
  · by_cases two : 2 ≤ H
    · simpa [remActive,secondBudget,two] using activeCost_le_one H (drop empty q Q) q (partner q)
    · have one : H = 1 := by omega
      subst H
      have filled : ¬ Legal 1 (drop empty q Q) q := by simp [Legal,height,drop,empty,board]
      simp [activeCost,filled,remActive,secondBudget]
  · have bound := paired_cap H (afterRound empty q (partner q))
    change switch q (partner q) + _ ≤ 2
    unfold switch; split <;> omega

private theorem good_common {H b} (good : Good H b) (noP : ¬ Wins H b P)
    (room : ¬ Full H b) : Common H b := by
  rcases good with term | cert
  · exact False.elim (term.2.elim noP room)
  · exact cert.1

private theorem next_step {H b s q} (inv : Inv H b s) (noP : ¬ Wins H b P)
    (room : ¬ Full H b) (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q ∧ Correct H b q s (plan H b q s).1 (plan H b q s).2 := by
  cases s with
  | opening =>
    change b = empty at inv
    subst b
    exact ⟨oneStone_no_win H q Q,opening_step hq⟩
  | waiting =>
    have common := good_common inv.1 noP room
    exact ⟨c_Q_move_safe common inv.2 hq,waiting_step common inv.2 hq⟩
  | paired =>
    have common := good_common inv.1 noP room
    exact ⟨b_Q_move_safe common inv.2 hq,paired_step common inv.2 hq⟩

private theorem at_prefix {H a t b s} (path : Counted H (secondPaper H) empty opening a t b s) :
    Inv H b s ∧ a + remActive H s ≤ secondBudget H ∧ t + remTotal H b s ≤ 2 := by
  induction path with
  | nil => exact ⟨rfl,by simp [remActive],by simp [remTotal]⟩
  | @step a t b s q p n path noP noQ room hq sq qr chosen hp ih =>
    have eq : plan H b q s = (p,n) := Option.some.inj chosen
    have step := (next_step ih.1 noP room hq).2
    rw [eq] at step
    rcases step with ⟨_,newInv,ca,ct⟩
    rcases ih with ⟨_,aBound,tBound⟩
    exact ⟨newInv,by dsimp at ca; omega,by dsimp at ct; omega⟩

private theorem lift_prefix {S H f root initial a b} {s : S}
    (path : Prefix H f root initial a b s) : ∃ t, Counted H f root initial a t b s := by
  induction path with
  | nil => exact ⟨0,.nil⟩
  | step prior np nq room hq sq rq chosen hp ih =>
    obtain ⟨t,old⟩ := ih
    exact ⟨_,.step old np nq room hq sq rq chosen hp⟩

theorem second_total_and_active (H : Nat) :
    HistoryBudget H (secondPaper H) (secondBudget H) empty opening ∧
    ∀ a t b s, Counted H (secondPaper H) empty opening a t b s → t ≤ 2 := by
  constructor
  · intro a b s path
    obtain ⟨t,both⟩ := lift_prefix path
    obtain ⟨inv,cap,_⟩ := at_prefix both
    have safe : ¬ Wins H b Q := by
      cases s with
      | opening => rw [show b = empty from inv]; exact empty_no_win H Q
      | waiting => exact good_noQ inv.1
      | paired => exact good_noQ inv.1
    refine ⟨by omega,safe,?_⟩
    by_cases np : Wins H b P
    · exact Or.inl np
    by_cases room : Full H b
    · exact Or.inr (Or.inl room)
    apply Or.inr; apply Or.inr
    intro q hq
    have step := next_step inv np room hq
    exact ⟨step.1,Or.inr ⟨_,_,rfl,step.2.1⟩⟩
  · intro a t b s path
    have bound := (at_prefix path).2.2
    omega

#print axioms second_total_and_active
end UniformFour.PaperOne
