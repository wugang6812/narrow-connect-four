import UniformFour.Priority
import UniformFour.AClosure
import OddHeight.Capacity
import HistoryBudget

namespace UniformFour.Reserves
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U1 UniformFour.U2

inductive Kind | ordinary | blocking | winning deriving DecidableEq

def Guards : Kind → Target → Line → Prop
  | .ordinary, t, L | .blocking, t, L => targetCell t ∈ L.cells
  | .winning, t, L => ∃ x ∈ L.cells, x.col = t.col ∧ t.row ≤ x.row

def Typed (H : Nat) (b : Board) : Kind → Target → Prop
  | .ordinary, t => (H - t.row) % 2 = 0
  | .blocking, t => ∀ L, Unresolved H b L → targetCell t ∈ L.cells
  | .winning, t => FixedWinningTarget H b t

/-- A pending column has one designated row. An empty list is permanent
defence and no longer needs an outside-parity premise. -/
structure Data (H : Nat) (b : Board) (kind : Target → Kind) (ts : List Target) : Prop where
  uniqueCol : ∀ t ∈ ts, ∀ u ∈ ts, t.col = u.col → t = u
  room : ∀ t ∈ ts, height b t.col < t.row ∧
    (t.row-height b t.col)%2 = 0 ∧ t.row ≤ H
  outsideEven : ts ≠ [] → outside H b ts % 2 = 0
  typeOK : ∀ t ∈ ts, Typed H b (kind t) t
  guards : ∀ L, Unresolved H b L → ∃ t ∈ ts, Guards (kind t) t L

def Ready (H : Nat) (b : Board) (kind : Target → Kind) (ts : List Target) : Prop :=
  SafeTerminal H b ∨ (Common H b ∧ Data H b kind ts)

structure Reply (H : Nat) (b : Board) (ts : List Target) (q p : Col) : Prop where
  legal : Legal H (drop b q Q) p
  covers : Legal H (drop b q Q) q → p = q
  outside : inJ ts q = false → inJ ts p = false

private theorem cover_room {H b kind ts q} (d : Data H b kind ts) (hj : inJ ts q = true) :
    Legal H (drop b q Q) q := by
  obtain ⟨t,ht,he⟩ := inJ_iff.mp hj
  obtain ⟨pos,even,roof⟩ := d.room t ht
  rw [he] at pos even
  unfold Legal
  rw [height_drop_same]
  omega

theorem reply_exists {H b kind ts q} (d : Data H b kind ts) (bound : Bounded H b)
    (hq : Legal H b q) (space : ¬ Full H (drop b q Q)) : ∃ p, Reply H b ts q p := by
  by_cases cover : Legal H (drop b q Q) q
  · exact ⟨q,cover,fun _ => rfl,id⟩
  cases hj : inJ ts q with
  | true => exact False.elim (cover (cover_room d hj))
  | false =>
    by_cases nil : ts = []
    · obtain ⟨p,hp⟩ := bounded_notFull_exists_legal (drop_bounded bound hq Q) space
      exact ⟨p,hp,fun h => False.elim (cover h),fun _ => by simp [nil,inJ]⟩
    · obtain ⟨p,hp,hj'⟩ := outside_reply_exists (d.outsideEven nil) hq hj
      exact ⟨p,hp,fun h => False.elim (cover h),fun _ => hj'⟩

private theorem cover_or_full {H b ts q p} (bound : Bounded H b)
    (hq : Legal H b q) (r : Reply H b ts q p) :
    p = q ∨ height (drop b q Q) q = H := by
  by_cases cover : Legal H (drop b q Q) q
  · exact Or.inl (r.covers cover)
  · have h := drop_bounded bound hq Q q
    unfold Legal at cover
    exact Or.inr (by omega)

private theorem outside_round {H b kind ts q p} (d : Data H b kind ts) (nonempty : ts ≠ [])
    (hq : Legal H b q) (r : Reply H b ts q p) : outside H (afterRound b q p) ts % 2 = 0 := by
  have even := d.outsideEven nonempty
  cases hj : inJ ts q with
  | true =>
    have same := r.covers (cover_room d hj)
    subst p
    simpa only [afterRound,outside_drop_inside hj] using even
  | false =>
    have e1 := outside_drop hq hj Q
    have e2 := outside_drop r.legal (r.outside hj) P
    unfold afterRound
    omega

private theorem erased_mem {ts : List Target} {q : Col} {u : Target} :
    u ∈ ts.filter (fun t => decide (t.col ≠ q)) ↔ u ∈ ts ∧ u.col ≠ q := by simp

private theorem erased_col {ts : List Target} {q c : Col} (ne : c ≠ q) :
    inJ (ts.filter (fun t => decide (t.col ≠ q))) c = inJ ts c := by
  apply Bool.eq_iff_iff.mpr
  simp only [inJ_iff,erased_mem]
  constructor
  · rintro ⟨t,⟨ht,_⟩,he⟩; exact ⟨t,ht,he⟩
  · rintro ⟨t,ht,he⟩; exact ⟨t,⟨ht,he ▸ ne⟩,he⟩

private theorem erased_same (ts : List Target) (q : Col) :
    inJ (ts.filter (fun t => decide (t.col ≠ q))) q = false := by
  cases h : inJ _ q with
  | false => rfl
  | true =>
    obtain ⟨t,ht,he⟩ := inJ_iff.mp h
    exact False.elim ((erased_mem.mp ht).2 he)

/-- The released column contributes precisely its remaining capacity. -/
theorem release_capacity {H b ts q} (pend : inJ ts q = true) :
    outside H b (ts.filter (fun t => decide (t.col ≠ q))) =
      outside H b ts + (H-height b q) := by
  cases q with
  | c1 =>
    simp only [outside_expanded, erased_same, erased_col (q := c1) (c := c2) (by decide), erased_col (q := c1) (c := c3) (by decide), erased_col (q := c1) (c := c4) (by decide), pend, Bool.false_eq_true, ite_false, ite_true]
    omega
  | c2 =>
    simp only [outside_expanded, erased_same, erased_col (q := c2) (c := c1) (by decide), erased_col (q := c2) (c := c3) (by decide), erased_col (q := c2) (c := c4) (by decide), pend, Bool.false_eq_true, ite_false, ite_true]
    omega
  | c3 =>
    simp only [outside_expanded, erased_same, erased_col (q := c3) (c := c1) (by decide), erased_col (q := c3) (c := c2) (by decide), erased_col (q := c3) (c := c4) (by decide), pend, Bool.false_eq_true, ite_false, ite_true]
    omega
  | c4 =>
    simp only [outside_expanded, erased_same, erased_col (q := c4) (c := c1) (by decide), erased_col (q := c4) (c := c2) (by decide), erased_col (q := c4) (c := c3) (by decide), pend, Bool.false_eq_true, ite_false, ite_true]
    omega

/-- Height bookkeeping for an individual pending cell. -/
private theorem target_step {H b kind ts q p t} (d : Data H b kind ts) (ht : t ∈ ts)
    (r : Reply H b ts q p) :
    (t.col = q ∧ height (afterRound b q p) q = t.row ∧
      stoneAt (afterRound b q p) (targetCell t) = some P) ∨
    (height (afterRound b q p) t.col < t.row ∧
      (t.row - height (afterRound b q p) t.col)%2 = 0) := by
  obtain ⟨pos,even,roof⟩ := d.room t ht
  by_cases same : q = t.col
  · subst q
    have pp := r.covers (cover_room d (inJ_of_mem ht))
    subst p
    have ht' : height (afterRound b t.col t.col) t.col = height b t.col + 2 := by
      simp [afterRound,Nat.add_assoc]
    by_cases hit : t.row = height b t.col + 2
    · left
      refine ⟨rfl,ht'.trans hit.symm,?_⟩
      have cell : targetCell t = ⟨t.col,height (drop b t.col Q) t.col+1⟩ := by
        unfold targetCell; rw [height_drop_same,hit]
      rw [cell]
      exact candidate_stoneAt_new_top _ _ _
    · right; rw [ht']; constructor <;> omega
  · have diff : p ≠ t.col := by
      cases hj : inJ ts q with
      | true => simpa only [r.covers (cover_room d hj)] using same
      | false =>
        intro he
        have tmp := r.outside hj
        rw [he,inJ_of_mem ht] at tmp
        contradiction
    right
    simpa [afterRound,height,drop,Ne.symm same,Ne.symm diff] using And.intro pos even

private theorem resource_Q_safe {H b kind ts q} (common : Common H b)
    (d : Data H b kind ts) (hq : Legal H b q) : ¬ Wins H (drop b q Q) Q := by
  apply unresolved_guard_Q_move_safe common hq
  intro L hL
  obtain ⟨t,ht,hg⟩ := d.guards L hL
  obtain ⟨pos,even,roof⟩ := d.room t ht
  have guard : ∃ x ∈ L.cells, x.col = t.col ∧ t.row ≤ x.row := by
    cases tag : kind t with
    | winning => simpa [tag,Guards] using hg
    | ordinary | blocking =>
      exact ⟨targetCell t,by simpa [tag,Guards] using hg,rfl,Nat.le_refl _⟩
  obtain ⟨x,hx,hcol,above⟩ := guard
  apply empty_target_not_allQ hx
  apply cell_empty_above_height
  rw [hcol]
  have := height_after_move_le b q t.col Q
  omega

/-- Update only the target in the column just visited. A blocking or winning
    capture ends the waiting phase; an ordinary capture frees that column. -/
noncomputable def advance (kind : Target → Kind) (after : Board) (ts : List Target) (q : Col) :
    List Target := by
  classical
  exact if hit : ∃ t ∈ ts, t.col = q ∧ height after q = t.row then
    match kind hit.choose with
    | .ordinary => ts.filter (fun u => decide (u.col ≠ q))
    | .blocking | .winning => []
  else ts

private theorem emptyData {H b kind} (permanent : A0 H b) : Data H b kind [] := by
  refine ⟨by simp,by simp,by simp,by simp,?_⟩
  exact fun L hL => False.elim (permanent L hL)

private theorem typed_after {H b k t q p} (old : Typed H b k t) (hq : Legal H b q)
    (cover : p = q ∨ height (drop b q Q) q = H) : Typed H (afterRound b q p) k t := by
  cases k with
  | ordinary => exact old
  | blocking => exact fun L hL => old L (unresolved_after_cover_subset hq cover hL)
  | winning => exact fixedWinningTarget_preserved old q p

theorem round_ready {H b kind ts q p} (common : Common H b) (d : Data H b kind ts)
    (hq : Legal H b q) (r : Reply H b ts q p) :
    Ready H (afterRound b q p) kind (advance kind (afterRound b q p) ts q) := by
  classical
  let z := afterRound b q p
  have cover := cover_or_full common.1.1 hq r
  have st := structural_after_cover (common_structural common) hq r.legal (resource_Q_safe common d hq) cover
  by_cases win : Wins H z P
  · exact Or.inl ⟨st.noQ,Or.inl win⟩
  by_cases full : Full H z
  · exact Or.inl ⟨st.noQ,Or.inr full⟩
  refine Or.inr ⟨⟨⟨st.bounded,win,st.noQ,full⟩,st.topRun⟩,?_⟩
  change Data H z kind (advance kind z ts q)
  have typed {u} (hu : u ∈ ts) : Typed H z (kind u) u := typed_after (d.typeOK u hu) hq cover
  have stay {u} (hu : u ∈ ts) (avoid : ¬ (u.col = q ∧ height z q = u.row)) :
      height z u.col < u.row ∧ (u.row-height z u.col)%2 = 0 ∧ u.row ≤ H := by
    rcases target_step d hu r with ⟨e1,e2,_⟩ | ⟨pos,even⟩
    · exact False.elim (avoid ⟨e1,e2⟩)
    · exact ⟨pos,even,(d.room u hu).2.2⟩
  by_cases hit : ∃ t ∈ ts, t.col = q ∧ height z q = t.row
  · let t := hit.choose
    obtain ⟨ht,tc,tr⟩ := hit.choose_spec
    change t ∈ ts at ht
    change t.col = q at tc
    change height z q = t.row at tr
    have stone : stoneAt z (targetCell t) = some P := by
      rcases target_step d ht r with captured | pending
      · exact captured.2.2
      · change height z t.col < t.row ∧ _ at pending
        rw [tc,tr] at pending
        omega
    have typedT := d.typeOK t ht
    rw [advance,dif_pos hit]
    change Data H z kind (match kind t with
      | .ordinary => ts.filter (fun u => decide (u.col ≠ q))
      | .blocking | .winning => [])
    cases tag : kind t with
    | winning =>
      have fixed : FixedWinningTarget H z t := fixedWinningTarget_preserved (by simpa [tag,Typed] using typedT) q p
      obtain ⟨L,hv,_,fixed⟩ := fixed
      apply False.elim (win ⟨L,hv,?_⟩)
      intro x hx
      by_cases eq : x = targetCell t
      · exact eq ▸ stone
      · exact fixed x hx eq
    | blocking =>
      apply emptyData
      intro L bad
      have block : ∀ L, Unresolved H b L → targetCell t ∈ L.cells := by simpa [tag,Typed] using typedT
      exact bad.2 ⟨targetCell t,block L (unresolved_after_cover_subset hq cover bad),stone⟩
    | ordinary =>
      have source : ts ≠ [] := by intro empty; simp [empty] at ht
      refine ⟨fun u hu v hv => d.uniqueCol u (erased_mem.mp hu).1 v (erased_mem.mp hv).1,
        fun u hu => stay (erased_mem.mp hu).1 (fun h => (erased_mem.mp hu).2 h.1),
        ?_, fun u hu => typed (erased_mem.mp hu).1, ?_⟩
      · intro _
        have ord : (H-t.row)%2=0 := by simpa [Typed,tag] using typedT
        have atQ : inJ ts q = true := tc ▸ inJ_of_mem ht
        rw [release_capacity atQ,tr]
        have even := outside_round d source hq r
        change outside H z ts % 2 = 0 at even
        omega
      · intro L bad
        obtain ⟨u,hu,hg⟩ := d.guards L (unresolved_after_cover_subset hq cover bad)
        by_cases same : u.col = q
        · have eq := d.uniqueCol u hu t ht (same.trans tc.symm)
          subst u
          have onLine : targetCell t ∈ L.cells := by simpa [tag,Guards] using hg
          exact False.elim (bad.2 ⟨targetCell t,onLine,stone⟩)
        · exact ⟨u,erased_mem.mpr ⟨hu,same⟩,hg⟩
  · rw [advance,dif_neg hit]
    refine ⟨d.uniqueCol,fun u hu => stay hu (fun h => hit ⟨u,hu,h⟩),
      fun nonempty => outside_round d nonempty hq r, fun u hu => typed hu,?_⟩
    exact fun L bad => d.guards L (unresolved_after_cover_subset hq cover bad)

/-- All branches reach either a genuine terminal position or permanent
defence. Each branch quantifies every admissible outside fallback. -/
inductive Resolves (H : Nat) (kind : Target → Kind) : Board → List Target → Prop
  | terminal {b ts} : SafeTerminal H b → Resolves H kind b ts
  | permanent {b} : Common H b → A0 H b → Resolves H kind b []
  | round {b ts} (pending : ts ≠ []) (atTurn : Common H b)
      (moves : ∀ q, Legal H b q →
        ¬ Wins H (drop b q Q) Q ∧ ¬ Full H (drop b q Q) ∧ (∃ p, Reply H b ts q p))
      (continuations : ∀ q, Legal H b q → ∀ p, Reply H b ts q p →
        Resolves H kind (afterRound b q p) (advance kind (afterRound b q p) ts q)) :
      Resolves H kind b ts

theorem resolves {H kind b ts} (ready : Ready H b kind ts) : Resolves H kind b ts := by
  rcases ready with term | ⟨common,d⟩
  · exact .terminal term
  by_cases nil : ts = []
  · subst ts
    apply Resolves.permanent common
    intro L bad
    obtain ⟨_,ht,_⟩ := d.guards L bad
    cases ht
  apply Resolves.round nil common
  · intro q hq
    have space : ¬ Full H (drop b q Q) := by
      obtain ⟨t,ht⟩ : ∃ t, t ∈ ts := by cases ts with
        | nil => contradiction
        | cons t us => exact ⟨t,by simp⟩
      obtain ⟨pos,even,roof⟩ := d.room t ht
      have bound := height_after_move_le b q t.col Q
      intro filled
      have atCol := filled t.col
      omega
    exact ⟨resource_Q_safe common d hq,space,reply_exists d common.1.1 hq space⟩
  · intro q hq p r
    exact resolves (round_ready common d hq r)
termination_by remaining H b
decreasing_by
  have step := remaining_round common.1.1 hq r.legal
  unfold afterRound
  omega

private noncomputable def eligible (H : Nat) (b : Board) (ts : List Target) (q p : Col) : Bool := by
  classical
  exact decide (Reply H b ts q p)

noncomputable def reservePolicy (H : Nat) (kind : Target → Kind) : Controller (List Target) :=
  fun b q ts => (chooseFirst (eligible H b ts q) allCols).map
    (fun p => (p,advance kind (afterRound b q p) ts q))

private theorem fixed_reply {H b ts q} (witness : ∃ p, Reply H b ts q p) (kind : Target → Kind) :
    ∃ p, Reply H b ts q p ∧ reservePolicy H kind b q ts =
      some (p,advance kind (afterRound b q p) ts q) := by
  classical
  obtain ⟨p,r⟩ := witness
  have mem : p ∈ allCols := by cases p <;> simp [allCols]
  have yes : eligible H b ts q p = true := by simpa [eligible] using r
  obtain ⟨c,chosen⟩ := chooseFirst_complete ⟨p,mem,yes⟩
  exact ⟨c,by simpa [eligible] using (chooseFirst_sound chosen).2,by simp [reservePolicy,chosen]⟩

theorem reserve_zero_budget {H kind b ts} (ready : Ready H b kind ts) :
    BudgetSafe H (reservePolicy H kind) 0 b ts := by
  intro k
  induction k generalizing b ts with
  | zero =>
    rcases ready with term | ⟨common,_⟩
    · exact term.1
    · exact common.1.2.2.1
  | succ k ih =>
    rcases ready with term | ⟨common,d⟩
    · exact ⟨term.1,term.2.imp_right Or.inl⟩
    refine ⟨common.1.2.2.1,Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨resource_Q_safe common d hq,?_⟩
    by_cases full : Full H (drop b q Q)
    · exact Or.inl full
    obtain ⟨p,r,chosen⟩ := fixed_reply (reply_exists d common.1.1 hq full) kind
    have zero : activeCost H (drop b q Q) q p = 0 := by
      by_cases room : Legal H (drop b q Q) q
      · simp [activeCost,r.covers room]
      · simp [activeCost,room]
    exact Or.inr ⟨p,_,chosen,r.legal,by omega,by simpa [zero] using ih (round_ready common d hq r)⟩

theorem multitarget_resource {H b kind ts} (common : Common H b) (data : Data H b kind ts) :
    Resolves H kind b ts ∧ HistoryBudget H (reservePolicy H kind) 0 b ts :=
  ⟨resolves (Or.inr ⟨common,data⟩),budget_to_history (reserve_zero_budget (Or.inr ⟨common,data⟩))⟩

#print axioms multitarget_resource
end UniformFour.Reserves
