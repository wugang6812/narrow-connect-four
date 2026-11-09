import UniformFour.Controller

/-!
Reviewed copy. Exact U2 tie-breaking on a supplied observation of the current
post-Q board. This executable selector is separate from certificate truth.
The Boolean fields must later be proved equal to the exact U2 predicates.
-/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

/-- Observations concern candidate boards after one P move. `qualified` includes
    immediate P wins, no-winner full draws, and live A/B/C certificate acceptance.
    No field here is assumed to be a proof of safety. -/
structure Observation where
  qualified : Col → Bool
  immediate : Col → Bool
  bottomScore : Col → Nat
  bothCorners : Bool

def chooseFirst (p : Col → Bool) : List Col → Option Col
  | [] => none
  | c :: cs => if p c then some c else chooseFirst p cs

theorem chooseFirst_sound {p : Col → Bool} {cs : List Col} {c : Col}
    (h : chooseFirst p cs = some c) : c ∈ cs ∧ p c = true := by
  revert h
  induction cs with
  | nil => intro h; simp [chooseFirst] at h
  | cons d ds ih =>
      intro h
      by_cases hd : p d = true
      · simp [chooseFirst, hd] at h
        cases h
        exact ⟨by simp, hd⟩
      · have hp : p d = false := by cases e : p d <;> simp_all
        have tail : chooseFirst p ds = some c := by simpa [chooseFirst, hp] using h
        have result := ih tail
        exact ⟨by simp [result.1], result.2⟩

theorem chooseFirst_complete {p : Col → Bool} {cs : List Col}
    (h : ∃ c ∈ cs, p c = true) : ∃ c, chooseFirst p cs = some c := by
  revert h
  induction cs with
  | nil =>
      intro h
      rcases h with ⟨c, hc, _⟩
      simp at hc
  | cons d ds ih =>
      intro h
      by_cases hd : p d = true
      · exact ⟨d, by simp [chooseFirst, hd]⟩
      · have hp : p d = false := by cases e : p d <;> simp_all
        have witness : ∃ c ∈ ds, p c = true := by
          rcases h with ⟨c, hc, good⟩
          rcases List.mem_cons.mp hc with hcd | hc
          · subst c
            exact False.elim (hd good)
          · exact ⟨c, hc, good⟩
        rcases ih witness with ⟨c, hc⟩
        exact ⟨c, by simpa [chooseFirst, hp] using hc⟩

/-- Return a maximum-score column. Equal scores prefer the earlier list element. -/
def bestFrom (score : Col → Nat) : List Col → Option Col
  | [] => none
  | c :: cs =>
      match bestFrom score cs with
      | none => some c
      | some d => if score c ≥ score d then some c else some d

theorem bestFrom_mem {score : Col → Nat} {cs : List Col} {c : Col}
    (h : bestFrom score cs = some c) : c ∈ cs := by
  revert h
  induction cs with
  | nil => intro h; simp [bestFrom] at h
  | cons d ds ih =>
      intro h
      cases e : bestFrom score ds with
      | none =>
          simp [bestFrom, e] at h
          cases h
          simp
      | some t =>
          by_cases hd : score d ≥ score t
          · simp [bestFrom, e, hd] at h
            cases h
            simp
          · have ht : t = c := by simpa [bestFrom, e, hd] using h
            subst c
            exact List.mem_cons_of_mem d (ih e)

theorem bestFrom_exists {score : Col → Nat} {cs : List Col}
    (h : cs ≠ []) : ∃ c, bestFrom score cs = some c := by
  cases cs with
  | nil => exact False.elim (h rfl)
  | cons c cs =>
      cases e : bestFrom score cs with
      | none => exact ⟨c, by simp [bestFrom, e]⟩
      | some d =>
          by_cases hd : score c ≥ score d
          · exact ⟨c, by simp [bestFrom, e, hd]⟩
          · exact ⟨d, by simp [bestFrom, e, hd]⟩

/-- The q-first list implements the same-column tie preference, and then leftmost. -/
def fallback (H : Nat) (a : Board) (q : Col) (score : Col → Nat) : Option Col :=
  if height a q < H then
    if 3 ≤ height a q then some q
    else bestFrom score ((q :: allCols.filter (fun c => c != q)).filter
      (fun c => decide (height a c < H)))
  else chooseFirst (fun c => decide (height a c < H)) allCols

/-- Literal priority order from U2 §4.2, including the off-domain full-q fallback.
    It is intentionally not a complete game driver: call only after terminal tests. -/
def select (H : Nat) (a : Board) (q : Col) (o : Observation) : Option Col :=
  if height a q < H ∧ (o.qualified q = true ∨ o.bothCorners = true) then some q
  else
    let legal := fun c => decide (height a c < H)
    match chooseFirst (fun c => (legal c && o.qualified c) && o.immediate c) allCols with
    | some c => some c
    | none =>
        match chooseFirst (fun c => (legal c && o.qualified c) &&
            decide ((H - height a c) % 2 = 1)) allCols with
        | some c => some c
        | none =>
            match chooseFirst (fun c => legal c && o.qualified c) allCols with
            | some c => some c
            | none => fallback H a q o.bottomScore

/-- Legal output is unconditional on the correctness of certificate observations. -/
theorem fallback_legal {H : Nat} {a : Board} {q c : Col} {score : Col → Nat}
    (h : fallback H a q score = some c) : Legal H a c := by
  unfold fallback at h
  split at h
  next hq =>
    split at h
    next high =>
      cases Option.some.inj h
      exact hq
    next low =>
      have mem := bestFrom_mem h
      have good := (List.mem_filter.mp mem).2
      simpa only [Legal, decide_eq_true_eq] using good
  next hq =>
    have good := (chooseFirst_sound h).2
    simpa only [Legal, decide_eq_true_eq] using good

theorem select_legal {H : Nat} {a : Board} {q c : Col} {o : Observation}
    (h : select H a q o = some c) : Legal H a c := by
  unfold select at h
  split at h
  next direct =>
    cases Option.some.inj h
    exact direct.1
  next noDirect =>
    dsimp only at h
    split at h
    next d found =>
      have good := (chooseFirst_sound found).2
      have legal : height a d < H := by
        have v := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp good).1).1
        simpa only [Legal, decide_eq_true_eq] using v
      cases Option.some.inj h
      exact legal
    next none =>
      split at h
      next d found =>
        have good := (chooseFirst_sound found).2
        have legal : height a d < H := by
          have v := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp good).1).1
          simpa only [Legal, decide_eq_true_eq] using v
        cases Option.some.inj h
        exact legal
      next none' =>
        split at h
        next d found =>
          have good := (chooseFirst_sound found).2
          have legal : height a d < H := by
            simpa only [Legal, decide_eq_true_eq] using ((Bool.and_eq_true _ _).mp good).1
          cases Option.some.inj h
          exact legal
        next none'' => exact fallback_legal h

theorem fallback_total {H : Nat} {a : Board} {q : Col} {score : Col → Nat}
    (existsLegal : ∃ c, Legal H a c) : ∃ c, fallback H a q score = some c := by
  unfold fallback
  by_cases hq : height a q < H
  · rw [if_pos hq]
    by_cases high : 3 ≤ height a q
    · exact ⟨q, by simp [high]⟩
    · rw [if_neg high]
      apply bestFrom_exists
      have mem : q ∈ ((q :: allCols.filter (fun c => c != q)).filter
          (fun c => decide (height a c < H))) := by simp [hq]
      intro empty
      rw [empty] at mem
      simp at mem
  · rw [if_neg hq]
    apply chooseFirst_complete
    rcases existsLegal with ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · cases c <;> simp [allCols]
    · simpa only [Legal, decide_eq_true_eq] using hc

theorem select_total {H : Nat} {a : Board} {q : Col} {o : Observation}
    (existsLegal : ∃ c, Legal H a c) : ∃ c, select H a q o = some c := by
  unfold select
  split
  next direct => exact ⟨q, rfl⟩
  next noDirect =>
    dsimp only
    split
    next c found => exact ⟨c, rfl⟩
    next none =>
      split
      next c found => exact ⟨c, rfl⟩
      next none' =>
        split
        next c found => exact ⟨c, rfl⟩
        next none'' => exact fallback_total existsLegal

/-- A bounded nonfull input always gets an actual legal response. This theorem
    says nothing about first-win safety or whether a returned certificate is true. -/
theorem select_total_legal {H : Nat} {a : Board} {q : Col} {o : Observation}
    (bounded : Bounded H a) (notFull : ¬ Full H a) :
    ∃ c, select H a q o = some c ∧ Legal H a c := by
  rcases select_total (o := o) (q := q)
    (bounded_notFull_exists_legal bounded notFull) with ⟨c, hc⟩
  exact ⟨c, hc, select_legal hc⟩

/-- Exact observation equality suffices for exact action equality, including all
    tie-breaks. Merely accepting an equally safe candidate does NOT suffice. -/
theorem select_congr {H : Nat} {a : Board} {q : Col} {o o' : Observation}
    (qualified : o.qualified = o'.qualified)
    (immediate : o.immediate = o'.immediate)
    (bottomScore : o.bottomScore = o'.bottomScore)
    (bothCorners : o.bothCorners = o'.bothCorners) :
    select H a q o = select H a q o' := by
  cases o
  cases o'
  simp_all

#print axioms select_legal
#print axioms select_congr
end UniformFour.U2
