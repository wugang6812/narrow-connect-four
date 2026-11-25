import experiments.NarrowBoards
import Mathlib.Data.Finset.Max

namespace Connect4.NarrowBoards.Cost

variable {w h : Nat}

/-- Leftmost playable column, used after a filled column or at the opening. -/
private noncomputable def firstLegal (h : Nat) (b : Board w) (ex : ∃ c, Legal h b c) :
    {c : Fin w // Legal h b c} := by
  classical
  let cs := Finset.univ.filter (Legal h b)
  have existsCol : cs.Nonempty := by
    obtain ⟨c,hc⟩ := ex
    exact ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩⟩
  exact ⟨cs.min' existsCol,(Finset.mem_filter.mp (Finset.min'_mem cs existsCol)).2⟩

/-- A fixed policy: cover if possible; otherwise choose a legal column. -/
noncomputable def coverMove (h : Nat) (b : Board w) (last : Option (Fin w)) :
    Option (Fin w) := by
  classical
  exact if hl : ∃ c, last = some c ∧ Legal h b c then some (Classical.choose hl)
    else if ha : ∃ c, Legal h b c then some (firstLegal h b ha).val else none

def Active (h : Nat) (b : Board w) (last : Option (Fin w)) (c : Fin w) : Prop :=
  ∃ d, last = some d ∧ Legal h b d ∧ c ≠ d

theorem cover_spec {b : Board w} {last : Option (Fin w)}
    (hv : Valid h b) (live : ¬ BoardFull h b) :
    ∃ c, coverMove h b last = some c ∧ Legal h b c ∧ ¬ Active h b last c := by
  classical
  unfold coverMove
  split
  · rename_i hl
    obtain ⟨he, legal⟩ := Classical.choose_spec hl
    refine ⟨Classical.choose hl, rfl, legal, ?_⟩
    rintro ⟨d, hd, _, ne⟩
    have : Classical.choose hl = d := Option.some.inj (he.symm.trans hd)
    exact ne this
  · rename_i hl
    have ha := exists_legal hv live
    rw [dif_pos ha]
    refine ⟨(firstLegal h b ha).val, rfl, (firstLegal h b ha).property, ?_⟩
    rintro ⟨d, hd, legal, _⟩
    exact hl ⟨d, hd, legal⟩

theorem cover_same {b : Board w} {c : Fin w} (hc : Legal h b c) :
    coverMove h b (some c) = some c := by
  classical
  unfold coverMove
  have he : ∃ d, some c = some d ∧ Legal h b d := ⟨c, rfl, hc⟩
  rw [dif_pos he]
  exact (Classical.choose_spec he).1.symm

/-- The same policy is used for every horizon. No move is taken after a win.
At own turns every chosen reply must have zero active cost, including wins. -/
def SafeZero (h : Nat) (p : Player) : Nat → Option (Fin w) → Board w → Prop
  | 0, _, b => ¬ HasFour h b (opponent p)
  | k+1, last, b =>
    ¬ HasFour h b (opponent p) ∧
    (HasFour h b p ∨ BoardFull h b ∨
      if toMove b = p then
        ∃ c, coverMove h b last = some c ∧ Legal h b c ∧
          ¬ Active h b last c ∧ SafeZero h p k (some c) (play b c (toMove b))
      else ∀ c, Legal h b c → SafeZero h p k (some c) (play b c (toMove b)))

theorem zero_induction (hw : w ≤ 3) (h : Nat) (p : Player) (k : Nat) :
    (∀ (b : Board w) last, Valid h b → Protected h (opponent p) b →
      SafeZero h p k last b) ∧
    (∀ (b : Board w) c, Valid h b → OpenAt h (opponent p) b c →
      toMove b = p → SafeZero h p k (some c) b) := by
  induction k with
  | zero =>
    exact ⟨fun _ _ _ hb => hasFour_false_of_noPairs hw hb.1,
      fun _ _ _ hb _ => hasFour_false_of_noPairs hw hb.1⟩
  | succ k ih =>
    constructor
    · intro b last hv hb
      refine ⟨hasFour_false_of_noPairs hw hb.1, Or.inr ?_⟩
      by_cases full : BoardFull h b
      · exact Or.inl full
      · apply Or.inr
        by_cases ht : toMove b = p
        · rw [if_pos ht]
          obtain ⟨c, chosen, legal, cost⟩ := cover_spec (last := last) hv full
          refine ⟨c, chosen, legal, cost, ?_⟩
          rw [ht]
          exact ih.1 _ _ (play_valid hv legal)
            (protected_play_other hb (player_ne_opponent p) c)
        · rw [if_neg ht]
          intro c hc
          have ht' := eq_opponent_of_ne _ _ ht
          apply ih.2 _ c (play_valid hv hc)
          · rw [ht']; exact protected_play_self hb hc
          · rw [toMove_play, ht', opponent_involutive]
    · intro b c hv hb ht
      refine ⟨hasFour_false_of_noPairs hw hb.1, Or.inr ?_⟩
      by_cases full : BoardFull h b
      · exact Or.inl full
      · apply Or.inr
        rw [if_pos ht]
        by_cases legal : Legal h b c
        · refine ⟨c, cover_same legal, legal, ?_, ?_⟩
          · rintro ⟨d, hd, _, ne⟩
            exact ne (Option.some.inj hd)
          · rw [ht]
            exact ih.1 _ _ (play_valid hv legal)
              (open_cover hb (player_ne_opponent p))
        · obtain ⟨d, chosen, hd, cost⟩ := cover_spec (last := some c) hv full
          refine ⟨d, chosen, hd, cost, ?_⟩
          rw [ht]
          exact ih.1 _ _ (play_valid hv hd)
            (protected_play_other (open_closed hb legal) (player_ne_opponent p) d)

theorem narrow_fixed_zero (w h : Nat) (hw : w ≤ 3) (p : Player) :
    ∀ k, SafeZero h p k none (emptyBoard w) :=
  fun k => (zero_induction hw h p k).1 _ _ (empty_valid w h) (empty_protected w h _)

theorem safeZero_forget {p : Player} {b : Board w} {last : Option (Fin w)}
    {k : Nat} (hs : SafeZero h p k last b) : SafeFor h p k b := by
  induction k generalizing last b with
  | zero => exact hs
  | succ k ih =>
    refine ⟨hs.1, ?_⟩
    rcases hs.2 with win | full | move
    · exact Or.inl win
    · exact Or.inr (Or.inl full)
    · apply Or.inr; apply Or.inr
      by_cases ht : toMove b = p
      · rw [if_pos ht] at move ⊢
        obtain ⟨c, _, hc, _, next⟩ := move
        exact ⟨c, hc, ih next⟩
      · rw [if_neg ht] at move ⊢
        exact fun c hc => ih (move c hc)

#print axioms narrow_fixed_zero
#print axioms safeZero_forget

/-- Chronological legal prefixes; wins stop extension before either player
may move again. The first move has last = none and therefore costs zero. -/
noncomputable def charge (h : Nat) (p : Player) (b : Board w)
    (last : Option (Fin w)) (c : Fin w) : Nat := by
  classical
  exact if toMove b = p ∧ Active h b last c then 1 else 0

inductive Prefix (h : Nat) (p : Player) : Board w → Option (Fin w) → Nat → Prop
  | start : Prefix h p (emptyBoard w) none 0
  | step {b last n c} :
      Prefix h p b last n →
      ¬ HasFour h b .black → ¬ HasFour h b .white →
      Legal h b c →
      (toMove b = p → coverMove h b last = some c) →
      Prefix h p (play b c (toMove b)) (some c) (n + charge h p b last c)

theorem prefix_valid {p : Player} {b : Board w} {last n}
    (path : Prefix h p b last n) : Valid h b := by
  induction path with
  | start => exact empty_valid _ _
  | step _ _ _ legal _ ih => exact play_valid ih legal

theorem prefix_zero {p : Player} {b : Board w} {last n}
    (path : Prefix h p b last n) : n = 0 := by
  classical
  induction path with
  | start => rfl
  | @step b last n c prev _ _ legal chosen ih =>
    have cost : charge h p b last c = 0 := by
      unfold charge
      by_cases turn : toMove b = p
      · have live : ¬ BoardFull h b := by
          intro full
          have := full c
          unfold Legal at legal
          omega
        obtain ⟨d, hd, _, zero⟩ := cover_spec (last := last) (prefix_valid prev) live
        have eq : d = c := Option.some.inj (hd.symm.trans (chosen turn))
        subst d
        simp [turn, zero]
      · simp [turn]
    simp [ih, cost]

theorem narrow_zero_history (w h : Nat) (hw : w ≤ 3) (p : Player) :
    (∀ k, SafeZero h p k none (emptyBoard w)) ∧
    (∀ (b : Board w) last n, Prefix h p b last n → n = 0) :=
  ⟨narrow_fixed_zero w h hw p, fun _ _ _ path => prefix_zero path⟩

#print axioms narrow_zero_history
abbrev Policy (w : Nat) := List (Fin w) → Board w → Option (Fin w)

def SafeWith (h : Nat) (p : Player) (f : Policy w) :
    Nat → List (Fin w) → Board w → Prop
  | 0, _, b => ¬ HasFour h b (opponent p)
  | k+1, hist, b =>
    ¬ HasFour h b (opponent p) ∧ (HasFour h b p ∨ BoardFull h b ∨
      if toMove b = p then ∃ c, f hist b = some c ∧ Legal h b c ∧
        SafeWith h p f k (c::hist) (play b c (toMove b))
      else ∀ c, Legal h b c → SafeWith h p f k (c::hist) (play b c (toMove b)))

inductive PlayPrefix (h : Nat) (p : Player) (f : Policy w) :
    List (Fin w) → Board w → Nat → Prop
  | nil : PlayPrefix h p f [] (emptyBoard w) 0
  | step {hist b n c} : PlayPrefix h p f hist b n →
      ¬ HasFour h b .black → ¬ HasFour h b .white → Legal h b c →
      (toMove b = p → f hist b = some c) →
      PlayPrefix h p f (c::hist) (play b c (toMove b)) (n+charge h p b hist.head? c)

def Achievable (w h : Nat) (p : Player) (budget : Nat) : Prop :=
  ∃ f : Policy w, (∀ k, SafeWith h p f k [] (emptyBoard w)) ∧
    ∀ hist b n, PlayPrefix h p f hist b n → n ≤ budget

private noncomputable def covering (h : Nat) : Policy w := fun hist b => coverMove h b hist.head?

private theorem safe_cover {p : Player} {b : Board w} {hist : List (Fin w)} {k : Nat}
    (safe : SafeZero h p k hist.head? b) : SafeWith h p (covering h) k hist b := by
  induction k generalizing hist b with
  | zero => exact safe
  | succ k ih =>
    refine ⟨safe.1,?_⟩
    rcases safe.2 with win | full | moves
    · exact Or.inl win
    · exact Or.inr (Or.inl full)
    apply Or.inr; apply Or.inr
    by_cases turn : toMove b = p
    · rw [if_pos turn] at moves ⊢
      obtain ⟨c,hc,legal,_,child⟩ := moves
      exact ⟨c,hc,legal,ih child⟩
    · rw [if_neg turn] at moves ⊢
      exact fun c hc => ih (moves c hc)

theorem narrow_finite_exact (w h : Nat) (hw : w ≤ 3) (p : Player) :
    Achievable w h p 0 ∧ ∀ n, Achievable w h p n → 0 ≤ n := by
  refine ⟨⟨covering h,fun k => safe_cover (narrow_fixed_zero w h hw p k),?_⟩,
    fun _ _ => Nat.zero_le _⟩
  intro hist b n path
  have old : Prefix h p b hist.head? n := by
    induction path with
    | nil => exact .start
    | step _ hb hw hc chosen ih => exact .step ih hb hw hc chosen
  exact Nat.le_of_eq (prefix_zero old)

#print axioms narrow_finite_exact
end Connect4.NarrowBoards.Cost
