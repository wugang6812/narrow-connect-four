import Connect4Proof.Basic

/-!
# Four columns: finite safety and partial black strategies

Paper: "窄棋盘重力四子棋的和棋策略" Theorem 4.1 — for every positive even height H,
White has a nonlosing strategy on the four-column empty board.

The white half, `white_nonloss_four_columns`, is complete. The black half
contains the completed PDstate and PD1 strategies and the PD0A waiting-phase
transitions. FourColumnsContinuation adds permanent defense and some exits.
FourColumnsFinal completes the finite empty-board draw theorem for all positive even heights.
The separate InfiniteNarrowBoards module proves the genuinely infinite case.

Framework (Board/SafeFor/IsDraw etc.) is the width-generic one introduced in
experiments/NarrowBoards.lean, copied with the w ≤ 3 specific lemmas removed.

Mathematical content (0-based stone index i = paper row − 1):
  column q (Black's first)    : Black stones only at i ≤ 1 or i odd
  column p = partner q        : Black stones only at i odd
  the two R columns           : Black stones only at i even
Phase 2 heights (White to reply): q,p odd; R even. After the one-time switch
(Black fills a P column f, White tops the other P column o): all columns even.
Line blocking, from the specs alone:
  vertical   : four consecutive indices contain an even index ≥ 2 in that
               column's own excluded class;
  horizontal : odd index rows are blocked by an R column, even rows by the
               p column (phase 2) or by f / o = p (phase 3);
  diagonals  : any four-column diagonal meets both R columns, whose indices
               differ by one, so one is odd — impossible for R.
No board enumeration, no new axioms, no sorry, no native evaluation.
-/

namespace Connect4.FourColumns

abbrev Board (w : Nat) := Fin w → List Player

variable {w h : Nat} {b : Board w} {c : Fin w} {p q : Player}

def emptyBoard (w : Nat) : Board w := fun _ => []

def Legal (h : Nat) (b : Board w) (c : Fin w) : Prop := (b c).length < h
def Valid (h : Nat) (b : Board w) : Prop := ∀ c, (b c).length ≤ h
def BoardFull (h : Nat) (b : Board w) : Prop := ∀ c, (b c).length = h

def play (b : Board w) (c : Fin w) (p : Player) : Board w :=
  Function.update b c (b c ++ [p])

def stone : List Player → Nat → Option Player
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, r + 1 => stone l r

theorem stone_none (l : List Player) (r : Nat) (hr : l.length ≤ r) :
    stone l r = none := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih =>
      cases r with
      | zero => simp at hr
      | succ r => exact ih r (by simpa using hr)

theorem stone_bound (l : List Player) (r : Nat) (p : Player)
    (hs : stone l r = some p) : r < l.length := by
  by_contra hn
  have he := stone_none l r (by omega)
  rw [he] at hs
  cases hs

theorem stone_append (l : List Player) (p : Player) (r : Nat) :
    stone (l ++ [p]) r =
      if r < l.length then stone l r else
        if r = l.length then some p else none := by
  induction l generalizing r with
  | nil => cases r <;> simp [stone]
  | cons a l ih =>
      cases r with
      | zero => simp [stone]
      | succ r => simpa [stone] using ih r

theorem stone_append_other (hpq : p ≠ q)
    (hs : stone (l ++ [p]) r = some q) : stone l r = some q := by
  by_cases hr : r < l.length
  · simpa [stone_append, hr] using hs
  · by_cases he : r = l.length
    · have hh : p = q := by simpa [stone_append, hr, he] using hs
      exact False.elim (hpq hh)
    · simp [stone_append, hr, he] at hs

def cellAtInt (h : Nat) (b : Board w) (x y : Int) : Option Player :=
  if hx : 0 ≤ x ∧ x < (w : Int) then
    if 0 ≤ y ∧ y < (h : Int) then
      stone (b ⟨x.toNat, by omega⟩) y.toNat
    else none
  else none

def HasFourDir (h : Nat) (b : Board w) (p : Player)
    (x y dx dy : Int) : Prop :=
  ∀ i : Fin 4,
    cellAtInt h b (x + (i : Int) * dx) (y + (i : Int) * dy) = some p

def HasFour (h : Nat) (b : Board w) (p : Player) : Prop :=
  (∃ x y : Int, HasFourDir h b p x y 0 1) ∨
  (∃ x y : Int, HasFourDir h b p x y 1 0) ∨
  (∃ x y : Int, HasFourDir h b p x y 1 1) ∨
  (∃ x y : Int, HasFourDir h b p x y 1 (-1))

theorem cellAtInt_some (hs : cellAtInt h b x y = some p) :
    ∃ c : Fin w, x = (c.val : Int) ∧ 0 ≤ y ∧ y < (h : Int) ∧
      stone (b c) y.toNat = some p := by
  by_cases hx : 0 ≤ x ∧ x < (w : Int)
  · by_cases hy : 0 ≤ y ∧ y < (h : Int)
    · refine ⟨⟨x.toNat, by omega⟩, ?_, hy.1, hy.2, ?_⟩
      · change x = (x.toNat : Int)
        omega
      · simpa [cellAtInt, hx, hy] using hs
    · simp [cellAtInt, hx, hy] at hs
  · simp [cellAtInt, hx] at hs

theorem play_eq (b : Board w) (c : Fin w) (p : Player) :
    play b c p c = b c ++ [p] := by simp [play]

theorem play_ne (b : Board w) (c d : Fin w) (p : Player) (hne : d ≠ c) :
    play b c p d = b d := by simp [play, Function.update, hne]

theorem play_valid (hv : Valid h b) (hc : Legal h b c) :
    Valid h (play b c p) := by
  intro d
  by_cases he : d = c
  · subst d
    rw [play_eq]
    have hh : (b c).length < h := hc
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [play_ne b c d p he]
    exact hv d

theorem exists_legal (hv : Valid h b) (hf : ¬ BoardFull h b) :
    ∃ c, Legal h b c := by
  classical
  by_contra hn
  apply hf
  intro c
  have hc : ¬ Legal h b c := fun hc => hn ⟨c, hc⟩
  have hh := hv c
  unfold Legal at hc
  omega

def totalStones (b : Board w) : Nat := ∑ c, (b c).length
def toMove (b : Board w) : Player :=
  if totalStones b % 2 = 0 then .black else .white

theorem player_ne_opponent (p : Player) : p ≠ opponent p := by
  cases p <;> simp [opponent]

theorem eq_opponent_of_ne (a p : Player) (hne : a ≠ p) : a = opponent p := by
  cases a <;> cases p <;> simp_all [opponent]

/-- Fixed-player safety, through k additional individual moves. -/
def SafeFor (h : Nat) (p : Player) : Nat → Board w → Prop
  | 0, b => ¬ HasFour h b (opponent p)
  | k + 1, b =>
      ¬ HasFour h b (opponent p) ∧
      (HasFour h b p ∨ BoardFull h b ∨
        (if toMove b = p then
          ∃ c, Legal h b c ∧ SafeFor h p k (play b c (toMove b))
        else
          ∀ c, Legal h b c → SafeFor h p k (play b c (toMove b))))

def CanAvoidLoss (h : Nat) (p : Player) (b : Board w) : Prop :=
  ∀ k : Nat, SafeFor h p k b

def IsDraw (h : Nat) (b : Board w) : Prop :=
  CanAvoidLoss h .black b ∧ CanAvoidLoss h .white b

/-! ## Column pairing on four columns -/

def partner (q : Fin 4) : Fin 4 :=
  ⟨if q.val % 2 = 0 then q.val + 1 else q.val - 1, by
    have hq := q.isLt
    split <;> omega⟩

theorem partner_val_eq (q : Fin 4) (h : q.val % 2 = 0) :
    (partner q).val = q.val + 1 := by
  simp only [partner, h, if_true]

theorem partner_val_ne (q : Fin 4) (h : q.val % 2 = 1) :
    (partner q).val = q.val - 1 := by
  have h' : ¬ (q.val % 2 = 0) := by omega
  simp only [partner, h', if_false]

theorem partner_ne (q : Fin 4) : partner q ≠ q := by
  intro he
  have hv : (partner q).val = q.val := by rw [he]
  have hq := q.isLt
  by_cases h : q.val % 2 = 0
  · rw [partner_val_eq q h] at hv
    omega
  · have h' : q.val % 2 = 1 := by omega
    rw [partner_val_ne q h'] at hv
    omega

theorem partner_invol (q : Fin 4) : partner (partner q) = q := by
  apply Fin.ext
  by_cases h : q.val % 2 = 0
  · have hp : (partner q).val = q.val + 1 := partner_val_eq q h
    have h1 : (partner q).val % 2 = 1 := by rw [hp]; omega
    have h2 := partner_val_ne (partner q) h1
    rw [h2, hp]
    omega
  · have hq : q.val % 2 = 1 := by omega
    have hp : (partner q).val = q.val - 1 := partner_val_ne q hq
    have h1 : (partner q).val % 2 = 0 := by rw [hp]; omega
    have h2 := partner_val_eq (partner q) h1
    rw [h2, hp]
    omega

def InP (q c : Fin 4) : Prop := c = q ∨ c = partner q

theorem not_inP_val (q : Fin 4) {c : Fin 4} (h : ¬ InP q c) :
    (q.val ≤ 1 ∧ 2 ≤ c.val) ∨ (2 ≤ q.val ∧ c.val ≤ 1) := by
  have hq := q.isLt
  have hc := c.isLt
  have h1 : c ≠ q := fun e => h (Or.inl e)
  have h2 : c ≠ partner q := fun e => h (Or.inr e)
  have hne : (partner q).val ≠ q.val := fun hv => partner_ne q (Fin.ext hv)
  by_cases hq1 : q.val ≤ 1
  · have hp : (partner q).val ≤ 1 := by
      by_cases e : q.val % 2 = 0
      · rw [partner_val_eq q e]; omega
      · have e' : q.val % 2 = 1 := by omega
        rw [partner_val_ne q e']; omega
    left
    by_cases cv : c.val = q.val
    · exact absurd (Fin.ext cv) h1
    · by_cases cp : c.val = (partner q).val
      · exact absurd (Fin.ext cp) h2
      · exact ⟨hq1, by omega⟩
  · have hp : 2 ≤ (partner q).val := by
      by_cases e : q.val % 2 = 0
      · rw [partner_val_eq q e]; omega
      · have e' : q.val % 2 = 1 := by omega
        rw [partner_val_ne q e']; omega
    right
    by_cases cv : c.val = q.val
    · exact absurd (Fin.ext cv) h1
    · by_cases cp : c.val = (partner q).val
      · exact absurd (Fin.ext cp) h2
      · exact ⟨by omega, by omega⟩

/-- The two columns outside P are adjacent: their values are k, k+1. -/
theorem R_adjacent (q : Fin 4) :
    ∃ k : Nat, k + 1 < 4 ∧ ∀ c : Fin 4, ¬ InP q c →
      (c.val = k ∨ c.val = k + 1) := by
  by_cases hq1 : q.val ≤ 1
  · refine ⟨2, by omega, ?_⟩
    intro c hc
    rcases not_inP_val q hc with ⟨_, hc2⟩ | ⟨_, _⟩
    · omega
    · omega
  · refine ⟨0, by omega, ?_⟩
    intro c hc
    rcases not_inP_val q hc with ⟨_, _⟩ | ⟨_, hc2⟩
    · omega
    · omega

/-! ## Black-stone row specifications (0-based index) -/

/-- R columns: Black stones only at even 0-based index (odd paper row). -/
def SOdd (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 0

/-- p column: Black stones only at odd 0-based index. -/
def SEven (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i % 2 = 1

/-- q column: Black stones only at index ≤ 1 or odd index. -/
def SQ (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i ≤ 1 ∨ i % 2 = 1

/-- Opened P column (phase 3): the only possible adjacent Black pair is 0,1. -/
def SOpen (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → stone l (i + 1) = some .black → i = 0

/-- Column top is not a Black stone. -/
def TopNB (l : List Player) : Prop :=
  ∀ i, stone l i = some .black → i + 1 ≠ l.length

theorem topNB_iff (l : List Player) : TopNB l ↔
    stone l (l.length - 1) ≠ some .black := by
  constructor
  · intro ht hs
    have hb := stone_bound l (l.length - 1) .black hs
    exact ht (l.length - 1) hs (by omega)
  · intro ht i hs he
    have h1 : l.length - 1 = i := by omega
    rw [h1] at ht
    exact ht hs

theorem topNB_append_white (l : List Player) : TopNB (l ++ [.white]) := by
  rw [topNB_iff]
  have hlen : (l ++ [Player.white]).length - 1 = l.length := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hlen]
  have hr : ¬ (l.length < l.length) := by omega
  simp [stone_append, hr]

theorem sOdd_append_white (hn : SOdd l) : SOdd (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sEven_append_white (hn : SEven l) : SEven (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sQ_append_white (hn : SQ l) : SQ (l ++ [.white]) :=
  fun i hs => hn i (stone_append_other (by decide) hs)

theorem sOpen_append_white (hn : SOpen l) : SOpen (l ++ [.white]) := by
  intro i h0 h1
  exact hn i (stone_append_other (by decide) h0)
    (stone_append_other (by decide) h1)

theorem sOdd_append_black (hn : SOdd l) (hlen : l.length % 2 = 0) :
    SOdd (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    simpa [stone_append, hr, hlen] using hs

theorem sEven_append_black (hn : SEven l) (hlen : l.length % 2 = 1) :
    SEven (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    simpa [stone_append, hr, hlen] using hs

theorem sQ_append_black (hn : SQ l) (hlen : l.length % 2 = 1) :
    SQ (l ++ [.black]) := by
  intro i hs
  by_cases hr : i < l.length
  · exact hn i (by simpa [stone_append, hr] using hs)
  · have he : i = l.length := by
      have hb := stone_bound _ i .black hs
      simp only [List.length_append, List.length_singleton] at hb
      omega
    subst i
    exact Or.inr (by simpa [stone_append, hr, hlen] using hs)

theorem sOpen_append_black (hn : SOpen l) (ht : TopNB l) :
    SOpen (l ++ [.black]) := by
  intro i h0 h1
  have hb : i + 1 < (l ++ [Player.black]).length := stone_bound _ _ _ h1
  simp only [List.length_append, List.length_singleton] at hb
  by_cases hr : i < l.length
  · by_cases hr1 : i + 1 < l.length
    · exact hn i (by simpa [stone_append, hr] using h0)
        (by simpa [stone_append, hr1] using h1)
    · rw [topNB_iff] at ht
      have hei : l.length - 1 = i := by omega
      rw [hei] at ht
      have hsa := stone_append l Player.black i
      rw [if_pos hr] at hsa
      rw [hsa] at h0
      exact (ht h0).elim
  · have he : i = l.length := by omega
    subst i
    simp [stone_append] at h1

theorem sEven_sOpen (hn : SEven l) : SOpen l := by
  intro i h0 h1
  have e0 := hn i h0
  have e1 := hn (i + 1) h1
  omega

theorem sQ_sOpen (hn : SQ l) : SOpen l := by
  intro i h0 h1
  rcases hn i h0 with hi | hi
  · rcases hn (i + 1) h1 with hj | hj <;> omega
  · rcases hn (i + 1) h1 with hj | hj <;> omega

/-! ## The geometric core: the row specifications block every Black four -/

/-- Converse pairing fact: the two columns with values k, k+1 avoid P. -/
theorem R_adjacent_back (q : Fin 4) :
    ∃ k : Nat, k + 1 < 4 ∧
      (∀ c : Fin 4, (c.val = k ∨ c.val = k + 1) → ¬ InP q c) := by
  by_cases hq1 : q.val ≤ 1
  · have hp : (partner q).val ≤ 1 := by
      by_cases e : q.val % 2 = 0
      · rw [partner_val_eq q e]; omega
      · have e' : q.val % 2 = 1 := by omega
        rw [partner_val_ne q e']; omega
    refine ⟨2, by omega, ?_⟩
    intro c hc hh
    rcases hh with e | e
    · have ev : c.val = q.val := by rw [e]
      rcases hc with h1 | h1 <;> omega
    · have ev : c.val = (partner q).val := by rw [e]
      rcases hc with h1 | h1 <;> omega
  · have hp : 2 ≤ (partner q).val := by
      by_cases e : q.val % 2 = 0
      · rw [partner_val_eq q e]; omega
      · have e' : q.val % 2 = 1 := by omega
        rw [partner_val_ne q e']; omega
    refine ⟨0, by omega, ?_⟩
    intro c hc hh
    rcases hh with e | e
    · have ev : c.val = q.val := by rw [e]
      rcases hc with h1 | h1 <;> omega
    · have ev : c.val = (partner q).val := by rw [e]
      rcases hc with h1 | h1 <;> omega

/-- Stones of a full-width line with dx = 1, stated per integer column. -/
private theorem line_stones {h : Nat} {b : Board 4} {x y dy : Int}
    (hd : HasFourDir h b .black x y 1 dy) (hx : x = 0) :
    ∀ j : Int, 0 ≤ j → j < 4 →
      ∃ n : Nat, (y + j * dy).toNat = n ∧ 0 ≤ y + j * dy ∧
        ∀ c : Fin 4, (c : Int) = j → stone (b c) n = some .black := by
  intro j hj1 hj2
  have hdi := hd ⟨j.toNat, by omega⟩
  obtain ⟨c, hxc, hyc, _, sc⟩ := cellAtInt_some hdi
  have h1 : (⟨j.toNat, by omega⟩ : Fin 4).val = j.toNat := rfl
  have hcoe : ((⟨j.toNat, by omega⟩ : Fin 4) : Int) = j := by
    rw [h1]
    exact Int.toNat_of_nonneg hj1
  rw [hcoe] at hxc hyc sc
  have hcv : c.val = j.toNat := by omega
  refine ⟨_, rfl, hyc, ?_⟩
  intro c' hc'
  have hce : c' = c := Fin.ext (by omega)
  rw [hce]
  exact sc

private theorem diag_parity (y : Int) (k : Nat) (n1 n2 : Nat)
    (hn1 : (y + (k : Int) * 1).toNat = n1) (hb1 : 0 ≤ y + (k : Int) * 1)
    (hn2 : (y + ((k : Int) + 1) * 1).toNat = n2) (hb2 : 0 ≤ y + ((k : Int) + 1) * 1)
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

private theorem diag_parity_neg (y : Int) (k : Nat) (n1 n2 : Nat)
    (hn1 : (y + (k : Int) * (-1)).toNat = n1) (hb1 : 0 ≤ y + (k : Int) * (-1))
    (hn2 : (y + ((k : Int) + 1) * (-1)).toNat = n2) (hb2 : 0 ≤ y + ((k : Int) + 1) * (-1))
    (p1 : n1 % 2 = 0) (p2 : n2 % 2 = 0) : False := by omega

/-- Phase 2: no Black four from the pairing specifications. -/
theorem noBlackFour_phase2 {h : Nat} {b : Board 4} {q : Fin 4}
    (hq : SQ (b q)) (hp : SEven (b (partner q)))
    (hr : ∀ c, ¬ InP q c → SOdd (b c)) : ¬ HasFour h b .black := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical
    have s0 : cellAtInt h b x y = some Player.black := by simpa using hd ⟨0, by decide⟩
    have s1 : cellAtInt h b x (y + 1) = some Player.black := by simpa using hd ⟨1, by decide⟩
    have s2 : cellAtInt h b x (y + 2) = some Player.black := by simpa using hd ⟨2, by decide⟩
    have s3 : cellAtInt h b x (y + 3) = some Player.black := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c1, hx1, hy1, _, t1⟩ := cellAtInt_some s1
    obtain ⟨c2, hx2, hy2, _, t2⟩ := cellAtInt_some s2
    obtain ⟨c3, hx3, hy3, _, t3⟩ := cellAtInt_some s3
    have e1 : c1 = c0 := Fin.ext (by omega)
    have e2 : c2 = c0 := Fin.ext (by omega)
    have e3 : c3 = c0 := Fin.ext (by omega)
    rw [e1] at t1
    rw [e2] at t2
    rw [e3] at t3
    have i1 : (y + 1).toNat = y.toNat + 1 := by omega
    have i2 : (y + 2).toNat = y.toNat + 2 := by omega
    have i3 : (y + 3).toNat = y.toNat + 3 := by omega
    rw [i1] at t1
    rw [i2] at t2
    rw [i3] at t3
    by_cases hq0 : c0 = q
    · subst hq0
      by_cases hn : y.toNat % 2 = 0
      · have := hq _ t2
        omega
      · have := hq _ t1
        omega
    · by_cases hp0 : c0 = partner q
      · subst hp0
        by_cases hn : y.toNat % 2 = 0
        · have := hp _ t0
          omega
        · have := hp _ t1
          omega
      · have hnotP : ¬ InP q c0 := by
          intro hh
          rcases hh with e | e
          · exact hq0 e
          · exact hp0 e
        have hR := hr c0 hnotP
        by_cases hn : y.toNat % 2 = 0
        · have := hR _ t1
          omega
        · have := hR _ t0
          omega
  · -- horizontal
    have s0 : cellAtInt h b x y = some Player.black := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b (x + 3) y = some Player.black := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hx0v : x = 0 := by omega
    have key := line_stones hd hx0v
    have hpv1 : (0:Int) ≤ ((partner q) : Int) := by
      have := (partner q).isLt
      omega
    have hpv2 : ((partner q) : Int) < 4 := by
      have := (partner q).isLt
      omega
    obtain ⟨np, hnp, _, hcp⟩ := key ((partner q) : Int) hpv1 hpv2
    have sp := hcp (partner q) rfl
    have pp := hp _ sp
    obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
    have hk1' : (0:Int) ≤ (k : Int) := by omega
    have hk4 : (k : Int) < 4 := by omega
    obtain ⟨nr, hnr, _, hcr⟩ := key (k : Int) hk1' hk4
    have sr := hcr ⟨k, by omega⟩ (by rfl)
    have hR := hr ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
    have pr := hR _ sr
    omega
  · -- rising diagonal
    have s0 := hd ⟨0, by decide⟩
    have s3 := hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hl0 : ((⟨0, by decide⟩ : Fin 4) : Int) = 0 := rfl
    have hl3 : ((⟨3, by decide⟩ : Fin 4) : Int) = 3 := rfl
    rw [hl0] at hx0
    rw [hl3] at hx3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key := line_stones hd hx0v
    obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
    have hk1' : (0:Int) ≤ (k : Int) := by omega
    have hk4 : (k : Int) < 4 := by omega
    have hk2' : (0:Int) ≤ (k + 1 : Int) := by omega
    have hk5 : (k + 1 : Int) < 4 := by omega
    obtain ⟨n1, hn1, hb1, hc1⟩ := key (k : Int) hk1' hk4
    obtain ⟨n2, hn2, hb2, hc2⟩ := key (k + 1 : Int) hk2' hk5
    have sr1 := hc1 ⟨k, by omega⟩ (by rfl)
    have sr2 := hc2 ⟨k + 1, by omega⟩ (by rfl)
    have hR1 := hr ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
    have hR2 := hr ⟨k + 1, by omega⟩ (hkB _ (Or.inr rfl))
    exact diag_parity y k n1 n2 hn1 hb1 hn2 hb2 (hR1 _ sr1) (hR2 _ sr2)
  · -- falling diagonal
    have s0 := hd ⟨0, by decide⟩
    have s3 := hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hl0 : ((⟨0, by decide⟩ : Fin 4) : Int) = 0 := rfl
    have hl3 : ((⟨3, by decide⟩ : Fin 4) : Int) = 3 := rfl
    rw [hl0] at hx0
    rw [hl3] at hx3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key := line_stones hd hx0v
    obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
    have hk1' : (0:Int) ≤ (k : Int) := by omega
    have hk4 : (k : Int) < 4 := by omega
    have hk2' : (0:Int) ≤ (k + 1 : Int) := by omega
    have hk5 : (k + 1 : Int) < 4 := by omega
    obtain ⟨n1, hn1, hb1, hc1⟩ := key (k : Int) hk1' hk4
    obtain ⟨n2, hn2, hb2, hc2⟩ := key (k + 1 : Int) hk2' hk5
    have sr1 := hc1 ⟨k, by omega⟩ (by rfl)
    have sr2 := hc2 ⟨k + 1, by omega⟩ (by rfl)
    have hR1 := hr ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
    have hR2 := hr ⟨k + 1, by omega⟩ (hkB _ (Or.inr rfl))
    exact diag_parity_neg y k n1 n2 hn1 hb1 hn2 hb2 (hR1 _ sr1) (hR2 _ sr2)

/-! ## Stage 1b: the phase machinery and White's nonloss strategy -/

def otherP (q f : Fin 4) : Fin 4 := if f = q then partner q else q

theorem otherP_props (q f : Fin 4) (hf : InP q f) :
    InP q (otherP q f) ∧ otherP q f ≠ f := by
  unfold otherP
  by_cases e : f = q
  · rw [if_pos e]
    exact ⟨Or.inr rfl, fun h => partner_ne q (by rw [h]; exact e)⟩
  · rw [if_neg e]
    exact ⟨Or.inl rfl, fun h => e h.symm⟩

theorem inP_other_or_self (q f c : Fin 4) (hf : InP q f) (hc : InP q c) (hne : c ≠ f) :
    c = otherP q f := by
  by_cases hf1 : f = q
  · rw [otherP, if_pos hf1]
    rcases hc with ec | ec
    · exact absurd (ec.trans hf1.symm) hne
    · exact ec
  · rcases hc with ec | ec
    · rw [otherP, if_neg hf1]
      exact ec
    · have hf2 : f = partner q := by
        rcases hf with ef | ef
        · exact absurd ef hf1
        · exact ef
      exact absurd (ec.trans hf2.symm) hne

theorem totalStones_empty (w : Nat) : totalStones (emptyBoard w) = 0 := by
  simp [totalStones, emptyBoard]

theorem totalStones_play' (b : Board w) (c : Fin w) (p : Player) :
    totalStones (play b c p) = totalStones b + 1 := by
  classical
  have key : ∀ d : Fin w, (play b c p d).length =
      (b d).length + (if d = c then 1 else 0) := by
    intro d
    by_cases he : d = c
    · subst d
      simp [play]
    · simp [play, Function.update, he]
  unfold totalStones
  rw [Finset.sum_congr rfl (fun d _ => key d), Finset.sum_add_distrib]
  simp

theorem toMove_empty (w : Nat) : toMove (emptyBoard w) = .black := by
  simp [toMove, totalStones_empty]

theorem toMove_play' (b : Board w) (c : Fin w) (p : Player) :
    toMove (play b c p) = opponent (toMove b) := by
  unfold toMove
  rw [totalStones_play']
  by_cases he : totalStones b % 2 = 0
  · have ho : (totalStones b + 1) % 2 = 1 := by omega
    simp [he, ho, opponent]
  · have ho : (totalStones b + 1) % 2 = 0 := by omega
    simp [he, ho, opponent]

theorem fin4_sum (f : Fin 4 → Nat) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} from by
    ext i; simp [Finset.mem_univ]; omega]
  simp [Finset.sum_insert, Finset.sum_singleton]
  omega

/-- Any four-in-a-row on four columns needs at least four stones. -/
theorem hasFour_minStones {h : Nat} {b : Board 4} {p : Player}
    (hf : HasFour h b p) : 4 ≤ totalStones b := by
  classical
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical: one column holds four stones
    have s0 : cellAtInt h b x y = some p := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b x (y + 3) = some p := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, _, _, _, t3⟩ := cellAtInt_some s3
    have hc : c3 = c0 := Fin.ext (by omega)
    rw [hc] at t3
    have i3 : (y + 3).toNat = y.toNat + 3 := by omega
    rw [i3] at t3
    have hb := stone_bound (b c0) (y.toNat + 3) p t3
    have hle : (b c0).length ≤ totalStones b := by
      unfold totalStones
      exact Finset.single_le_sum (f := fun i => (b i).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ c0)
    omega
  · -- full-width line: each of the four columns is nonempty
    have s0 : cellAtInt h b x y = some p := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b (x + 3) y = some p := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hle : ∀ i : Fin 4, 1 ≤ (b i).length := by
      intro i
      have hdi := hd i
      obtain ⟨ci, hxi, hyi, _, ti⟩ := cellAtInt_some hdi
      have hb := stone_bound (b ci) (y + (i : Int) * 0).toNat p ti
      have hci : ci = i := Fin.ext (by show ci.val = i.val; omega)
      rw [hci] at hb
      omega
    have hsum : totalStones b = (b (⟨0, by decide⟩ : Fin 4)).length +
        (b (⟨1, by decide⟩ : Fin 4)).length + (b (⟨2, by decide⟩ : Fin 4)).length +
        (b (⟨3, by decide⟩ : Fin 4)).length := by
      unfold totalStones
      rw [fin4_sum]
      rfl
    have h0 := hle ⟨0, by decide⟩
    have h1 := hle ⟨1, by decide⟩
    have h2 := hle ⟨2, by decide⟩
    have h3 := hle ⟨3, by decide⟩
    omega
  · -- rising diagonal
    have s0 : cellAtInt h b x y = some p := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b (x + 3) (y + 3) = some p := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hle : ∀ i : Fin 4, 1 ≤ (b i).length := by
      intro i
      have hdi := hd i
      obtain ⟨ci, hxi, hyi, _, ti⟩ := cellAtInt_some hdi
      have hb := stone_bound (b ci) (y + (i : Int) * 1).toNat p ti
      have hci : ci = i := Fin.ext (by show ci.val = i.val; omega)
      rw [hci] at hb
      omega
    have hsum : totalStones b = (b (⟨0, by decide⟩ : Fin 4)).length +
        (b (⟨1, by decide⟩ : Fin 4)).length + (b (⟨2, by decide⟩ : Fin 4)).length +
        (b (⟨3, by decide⟩ : Fin 4)).length := by
      unfold totalStones
      rw [fin4_sum]
      rfl
    have h0 := hle ⟨0, by decide⟩
    have h1 := hle ⟨1, by decide⟩
    have h2 := hle ⟨2, by decide⟩
    have h3 := hle ⟨3, by decide⟩
    omega
  · -- falling diagonal
    have s0 : cellAtInt h b x y = some p := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b (x + 3) (y + -3) = some p := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hle : ∀ i : Fin 4, 1 ≤ (b i).length := by
      intro i
      have hdi := hd i
      obtain ⟨ci, hxi, hyi, _, ti⟩ := cellAtInt_some hdi
      have hb := stone_bound (b ci) (y + (i : Int) * (-1)).toNat p ti
      have hci : ci = i := Fin.ext (by show ci.val = i.val; omega)
      rw [hci] at hb
      omega
    have hsum : totalStones b = (b (⟨0, by decide⟩ : Fin 4)).length +
        (b (⟨1, by decide⟩ : Fin 4)).length + (b (⟨2, by decide⟩ : Fin 4)).length +
        (b (⟨3, by decide⟩ : Fin 4)).length := by
      unfold totalStones
      rw [fin4_sum]
      rfl
    have h0 := hle ⟨0, by decide⟩
    have h1 := hle ⟨1, by decide⟩
    have h2 := hle ⟨2, by decide⟩
    have h3 := hle ⟨3, by decide⟩
    omega

/-! ## Phase-state predicates -/

def Spec2 (q : Fin 4) (b : Board 4) : Prop :=
  SQ (b q) ∧ SEven (b (partner q)) ∧ ∀ c, ¬ InP q c → SOdd (b c)

def Bnd2 (h : Nat) (q : Fin 4) (b : Board 4) : Prop :=
  Spec2 q b ∧ Valid h b ∧ (b q).length % 2 = 1 ∧ (b (partner q)).length % 2 = 1 ∧
  (∀ c, ¬ InP q c → (b c).length % 2 = 0) ∧ toMove b = .black

def Open2 (h : Nat) (q : Fin 4) (b : Board 4) (c : Fin 4) : Prop :=
  Spec2 q b ∧ Valid h b ∧
  (b q).length % 2 = (if q = c then 0 else 1) ∧
  (b (partner q)).length % 2 = (if partner q = c then 0 else 1) ∧
  (∀ d, ¬ InP q d → (b d).length % 2 = (if d = c then 1 else 0)) ∧ toMove b = .white

structure Spec3 (q f : Fin 4) (b : Board 4) : Prop where
  finP : InP q f
  rOdd : ∀ c, ¬ InP q c → SOdd (b c)
  keptQ : f = q → SQ (b q)
  keptP : f = partner q → SEven (b (partner q))
  openCol : SOpen (b (otherP q f))
  bottom : f = q → stone (b (otherP q f)) 0 ≠ some .black
  nonempty : 1 ≤ (b (otherP q f)).length

def Bnd3 (h : Nat) (q f : Fin 4) (b : Board 4) : Prop :=
  Spec3 q f b ∧ Valid h b ∧ TopNB (b (otherP q f)) ∧
  (b f).length = h ∧ (∀ c, (b c).length % 2 = 0) ∧ toMove b = .black

/-! ## Phase-3 geometric core -/

private theorem noBlackFour_phase3 {h : Nat} {b : Board 4} {q f : Fin 4}
    (hs : Spec3 q f b) : ¬ HasFour h b .black := by
  intro hw
  rcases hw with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical
    have s0 : cellAtInt h b x y = some Player.black := by simpa using hd ⟨0, by decide⟩
    have s1 : cellAtInt h b x (y + 1) = some Player.black := by simpa using hd ⟨1, by decide⟩
    have s2 : cellAtInt h b x (y + 2) = some Player.black := by simpa using hd ⟨2, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c1, hx1, hy1, _, t1⟩ := cellAtInt_some s1
    obtain ⟨c2, hx2, hy2, _, t2⟩ := cellAtInt_some s2
    have e1 : c1 = c0 := Fin.ext (by omega)
    have e2 : c2 = c0 := Fin.ext (by omega)
    rw [e1] at t1
    rw [e2] at t2
    have i1 : (y + 1).toNat = y.toNat + 1 := by omega
    have i2 : (y + 2).toNat = y.toNat + 2 := by omega
    rw [i1] at t1
    rw [i2] at t2
    by_cases hP : InP q c0
    · by_cases hf0 : c0 = f
      · rcases hs.finP with hfq | hfq
        · have hspec : SQ (b q) := hs.keptQ hfq
          have hcq : c0 = q := hf0.trans hfq
          rw [← hcq] at hspec
          by_cases hn : y.toNat % 2 = 0
          · have := hspec _ t2
            omega
          · have := hspec _ t1
            omega
        · have hspec : SEven (b (partner q)) := hs.keptP hfq
          have hcp : c0 = partner q := hf0.trans hfq
          rw [← hcp] at hspec
          by_cases hn : y.toNat % 2 = 0
          · have := hspec _ t0
            omega
          · have := hspec _ t1
            omega
      · have hco : c0 = otherP q f := inP_other_or_self q f c0 hs.finP hP hf0
        have hso : SOpen (b (otherP q f)) := hs.openCol
        rw [← hco] at hso
        have := hso _ t1 t2
        omega
    · have hR := hs.rOdd c0 hP
      by_cases hn : y.toNat % 2 = 0
      · have := hR _ t1
        omega
      · have := hR _ t0
        omega
  · -- horizontal
    have s0 : cellAtInt h b x y = some Player.black := by simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h b (x + 3) y = some Player.black := by simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have key := line_stones hd (by omega : x = 0)
    by_cases hn : y.toNat % 2 = 1
    · obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
      have hk1' : (0:Int) ≤ (k : Int) := by omega
      have hk4 : (k : Int) < 4 := by omega
      obtain ⟨nr, hnr, _, hcr⟩ := key (k : Int) hk1' hk4
      have sr := hcr ⟨k, by omega⟩ (by rfl)
      have hR := hs.rOdd ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
      have := hR _ sr
      omega
    · have hfp' : (0:Int) ≤ ((partner q) : Int) := by
        have := (partner q).isLt
        omega
      have hfp2 : ((partner q) : Int) < 4 := by
        have := (partner q).isLt
        omega
      obtain ⟨nf, hnf, _, hcf⟩ := key ((partner q) : Int) hfp' hfp2
      have sf : stone (b (partner q)) nf = some Player.black := hcf (partner q) rfl
      by_cases hfq : f = partner q
      · have hspec : SEven (b (partner q)) := hs.keptP hfq
        have := hspec _ sf
        omega
      · have hfq2 : f = q := by
          rcases hs.finP with e | e
          · exact e
          · exact absurd e hfq
        by_cases hn2 : y.toNat = 0
        · have ho0 : stone (b (partner q)) 0 ≠ some Player.black := by
            have hop : otherP q f = partner q := by
              unfold otherP
              rw [if_pos hfq2]
            intro hs0
            exact hs.bottom hfq2 (by rw [hop]; exact hs0)
          have hnf0 : nf = 0 := by omega
          rw [hnf0] at sf
          exact ho0 sf
        · have hq1 : (0:Int) ≤ ((q : Fin 4) : Int) := by
            have := q.isLt
            omega
          have hq2 : ((q : Fin 4) : Int) < 4 := by
            have := q.isLt
            omega
          obtain ⟨nq, hnq, _, hcq⟩ := key ((q : Fin 4) : Int) hq1 hq2
          have sq := hcq q rfl
          have hspec : SQ (b q) := hs.keptQ hfq2
          have := hspec _ sq
          omega
  · -- rising diagonal
    have s0 := hd ⟨0, by decide⟩
    have s3 := hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hl0 : ((⟨0, by decide⟩ : Fin 4) : Int) = 0 := rfl
    have hl3 : ((⟨3, by decide⟩ : Fin 4) : Int) = 3 := rfl
    rw [hl0] at hx0
    rw [hl3] at hx3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have key := line_stones hd (by omega : x = 0)
    obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
    have hk1' : (0:Int) ≤ (k : Int) := by omega
    have hk4 : (k : Int) < 4 := by omega
    have hk2' : (0:Int) ≤ (k + 1 : Int) := by omega
    have hk5 : (k + 1 : Int) < 4 := by omega
    obtain ⟨n1, hn1, hb1, hc1⟩ := key (k : Int) hk1' hk4
    obtain ⟨n2, hn2, hb2, hc2⟩ := key (k + 1 : Int) hk2' hk5
    have sr1 := hc1 ⟨k, by omega⟩ (by rfl)
    have sr2 := hc2 ⟨k + 1, by omega⟩ (by rfl)
    have hR1 := hs.rOdd ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
    have hR2 := hs.rOdd ⟨k + 1, by omega⟩ (hkB _ (Or.inr rfl))
    exact diag_parity y k n1 n2 hn1 hb1 hn2 hb2 (hR1 _ sr1) (hR2 _ sr2)
  · -- falling diagonal
    have s0 := hd ⟨0, by decide⟩
    have s3 := hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hl0 : ((⟨0, by decide⟩ : Fin 4) : Int) = 0 := rfl
    have hl3 : ((⟨3, by decide⟩ : Fin 4) : Int) = 3 := rfl
    rw [hl0] at hx0
    rw [hl3] at hx3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have key := line_stones hd (by omega : x = 0)
    obtain ⟨k, hk1, hkB⟩ := R_adjacent_back q
    have hk1' : (0:Int) ≤ (k : Int) := by omega
    have hk4 : (k : Int) < 4 := by omega
    have hk2' : (0:Int) ≤ (k + 1 : Int) := by omega
    have hk5 : (k + 1 : Int) < 4 := by omega
    obtain ⟨n1, hn1, hb1, hc1⟩ := key (k : Int) hk1' hk4
    obtain ⟨n2, hn2, hb2, hc2⟩ := key (k + 1 : Int) hk2' hk5
    have sr1 := hc1 ⟨k, by omega⟩ (by rfl)
    have sr2 := hc2 ⟨k + 1, by omega⟩ (by rfl)
    have hR1 := hs.rOdd ⟨k, by omega⟩ (hkB _ (Or.inl rfl))
    have hR2 := hs.rOdd ⟨k + 1, by omega⟩ (hkB _ (Or.inr rfl))
    exact diag_parity_neg y k n1 n2 hn1 hb1 hn2 hb2 (hR1 _ sr1) (hR2 _ sr2)

/-! ## The master induction for White's pairing strategy -/

def Open3 (h : Nat) (q f : Fin 4) (b : Board 4) (e : Fin 4) : Prop :=
  Spec3 q f b ∧ Valid h b ∧ (b f).length = h ∧
  (∀ c, (b c).length % 2 = (if c = e then 1 else 0)) ∧ toMove b = .white ∧
  (e = otherP q f ∨ TopNB (b (otherP q f)))

theorem inP_pair {q a b c : Fin 4} (ha : InP q a) (hb : InP q b)
    (hab : a ≠ b) (hc : InP q c) : c = a ∨ c = b := by
  rcases hc with e | e
  · by_cases haq : a = q
    · exact Or.inl (e.trans haq.symm)
    · have hap : a = partner q := by
        rcases ha with e2 | e2
        · exact absurd e2 haq
        · exact e2
      have hbq : b = q := by
        rcases hb with e2 | e2
        · exact e2
        · exact absurd (hap.symm ▸ e2.symm) hab
      exact Or.inr (e.trans hbq.symm)
  · by_cases hbq : b = q
    · rcases ha with e2 | e2
      · exact absurd (e2.trans hbq.symm) hab
      · exact Or.inl (e.trans e2.symm)
    · have hbp : b = partner q := by
        rcases hb with e2 | e2
        · exact absurd e2 hbq
        · exact e2
      rcases ha with e2 | e2
      · exact Or.inr (e.trans hbp.symm)
      · exact absurd (e2.trans hbp.symm) hab

private theorem white_pairing_aux (h : Nat) (hh : h % 2 = 0) :
    ∀ k : Nat, (∀ q b, Bnd2 h q b → SafeFor h .white k b) ∧
      (∀ q b c, Open2 h q b c → SafeFor h .white k b) ∧
      (∀ q f, InP q f → ∀ b, Bnd3 h q f b → SafeFor h .white k b) ∧
      (∀ q f, InP q f → ∀ b e, Open3 h q f b e → SafeFor h .white k b) := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q b hb
        exact noBlackFour_phase2 hb.1.1 hb.1.2.1 hb.1.2.2
      · intro q b c ho
        exact noBlackFour_phase2 ho.1.1 ho.1.2.1 ho.1.2.2
      · intro q f _ b hb3
        exact noBlackFour_phase3 hb3.1
      · intro q f _ b e ho3
        exact noBlackFour_phase3 ho3.1
  | succ k ih =>
      obtain ⟨A, B, C, D⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Bnd2: Black to move; every legal reply opens column e
        intro q b hb
        refine ⟨noBlackFour_phase2 hb.1.1 hb.1.2.1 hb.1.2.2, Or.inr (Or.inr ?_)⟩
        have htm : toMove b ≠ .white := by
          rw [hb.2.2.2.2.2]
          exact fun e => absurd e (by decide)
        rw [if_neg htm, hb.2.2.2.2.2]
        intro e he
        refine B q (play b e .black) e ⟨⟨?_, ?_, ?_⟩, play_valid hb.2.1 he,
          ?_, ?_, ⟨fun d hd => ?_, ?_⟩⟩
        · by_cases hqe : q = e
          · rw [hqe, play_eq]
            have hs1 := hb.1.1
            have hs2 := hb.2.2.1
            rw [hqe] at hs1 hs2
            exact sQ_append_black hs1 hs2
          · rw [play_ne b e q .black hqe]
            exact hb.1.1
        · by_cases hpe : partner q = e
          · rw [hpe, play_eq]
            have hs1 := hb.1.2.1
            have hs2 := hb.2.2.2.1
            rw [hpe] at hs1 hs2
            exact sEven_append_black hs1 hs2
          · rw [play_ne b e (partner q) .black hpe]
            exact hb.1.2.1
        · intro d hd
          by_cases hde : d = e
          · rw [hde, play_eq]
            have hs1 := hb.1.2.2 d hd
            have hs2 := hb.2.2.2.2.1 d hd
            rw [hde] at hs1 hs2
            exact sOdd_append_black hs1 hs2
          · rw [play_ne b e d .black hde]
            exact hb.1.2.2 d hd
        · by_cases hqe : q = e
          · rw [hqe, play_eq]
            simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
            have htr := hb.2.2.1
            rw [hqe] at htr
            omega
          · rw [play_ne b e q .black hqe, if_neg hqe]
            exact hb.2.2.1
        · by_cases hpe : partner q = e
          · rw [hpe, play_eq]
            simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
            have htr := hb.2.2.2.1
            rw [hpe] at htr
            omega
          · rw [play_ne b e (partner q) .black hpe, if_neg hpe]
            exact hb.2.2.2.1
        · by_cases hde : d = e
          · rw [hde, play_eq]
            simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
            have htr := hb.2.2.2.2.1 d hd
            rw [hde] at htr
            omega
          · rw [play_ne b e d .black hde, if_neg hde]
            exact hb.2.2.2.2.1 d hd
        · rw [toMove_play', hb.2.2.2.2.2]
          rfl
      · -- Open2: cap if legal, else switch to phase 3
        intro q b c ho
        refine ⟨noBlackFour_phase2 ho.1.1 ho.1.2.1 ho.1.2.2, Or.inr (Or.inr ?_)⟩
        rw [if_pos ho.2.2.2.2.2, ho.2.2.2.2.2]
        by_cases hc : Legal h b c
        · refine ⟨c, hc, A q (play b c .white) ⟨⟨?_, ?_, fun d hd => ?_⟩,
            play_valid ho.2.1 hc, ?_, ?_, ⟨fun d hd => ?_, ?_⟩⟩⟩
          · by_cases hq : q = c
            · rw [hq, play_eq]
              have hs1 := ho.1.1
              rw [hq] at hs1
              exact sQ_append_white hs1
            · rw [play_ne b c q .white hq]
              exact ho.1.1
          · by_cases hp : partner q = c
            · rw [hp, play_eq]
              have hs1 := ho.1.2.1
              rw [hp] at hs1
              exact sEven_append_white hs1
            · rw [play_ne b c (partner q) .white hp]
              exact ho.1.2.1
          · by_cases hd2 : d = c
            · rw [hd2, play_eq]
              have hs1 := ho.1.2.2 d hd
              rw [hd2] at hs1
              exact sOdd_append_white hs1
            · rw [play_ne b c d .white hd2]
              exact ho.1.2.2 d hd
          · by_cases hq : q = c
            · rw [hq, play_eq]
              simp only [List.length_append, List.length_singleton]
              have hqp := ho.2.2.1
              rw [if_pos hq] at hqp
              have htr := hqp
              rw [hq] at htr
              omega
            · rw [play_ne b c q .white hq]
              have hqp := ho.2.2.1
              rw [if_neg hq] at hqp
              exact hqp
          · by_cases hp : partner q = c
            · rw [hp, play_eq]
              simp only [List.length_append, List.length_singleton]
              have hpp := ho.2.2.2.1
              rw [if_pos hp] at hpp
              have htr := hpp
              rw [hp] at htr
              omega
            · rw [play_ne b c (partner q) .white hp]
              have hpp := ho.2.2.2.1
              rw [if_neg hp] at hpp
              exact hpp
          · by_cases hd2 : d = c
            · rw [hd2, play_eq]
              simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
              have hp2 := ho.2.2.2.2.1 d hd
              rw [hd2, if_pos rfl] at hp2
              omega
            · rw [play_ne b c d .white hd2]
              have hp2 := ho.2.2.2.2.1 d hd
              rw [if_neg hd2] at hp2
              exact hp2
          · rw [toMove_play', ho.2.2.2.2.2]
            rfl
        · have hfull : (b c).length = h := by
            have hv := ho.2.1 c
            by_contra hlt
            exact hc (by unfold Legal; omega)
          have hcP : InP q c := by
            by_contra hn
            have hp := ho.2.2.2.2.1 c hn
            rw [hfull, if_pos rfl] at hp
            omega
          obtain ⟨hoIn, hone⟩ := otherP_props q c hcP
          have hparC : (b c).length % 2 = 0 := by
            rcases hcP with e | e
            · have hq := ho.2.2.1
              rw [← e] at hq
              rw [if_pos rfl] at hq
              exact hq
            · have hp := ho.2.2.2.1
              rw [← e] at hp
              rw [if_pos rfl] at hp
              exact hp
          have hparO : (b (otherP q c)).length % 2 = 1 := by
            by_cases eo : otherP q c = q
            · have hq := ho.2.2.1
              rw [← eo] at hq
              rw [if_neg hone] at hq
              exact hq
            · have eop : otherP q c = partner q := by
                rcases hoIn with e | e
                · exact absurd e eo
                · exact e
              have hp := ho.2.2.2.1
              rw [← eop] at hp
              rw [if_neg hone] at hp
              exact hp
          have holeg : Legal h b (otherP q c) := by
            have hv := ho.2.1 (otherP q c)
            unfold Legal
            omega
          refine ⟨otherP q c, holeg, C q c hcP (play b (otherP q c) .white)
            ⟨⟨hcP, fun d hd => ?_, ?_, ?_, ?_, ?_, ?_⟩, play_valid ho.2.1 holeg,
            (by rw [play_eq]; exact topNB_append_white (b (otherP q c))), ?_, ⟨fun d => ?_, ?_⟩⟩⟩
          · rw [play_ne b (otherP q c) d .white (fun e => hd (by rw [e]; exact hoIn))]
            exact ho.1.2.2 d hd
          · intro hfc
            have hop : otherP q c = partner q := by rw [otherP, if_pos hfc]
            rw [hop, play_ne b (partner q) q .white (fun e => partner_ne q e.symm)]
            exact ho.1.1
          · intro hfc
            have hop : otherP q c = q := by
              rw [otherP, if_neg (fun e => partner_ne q (hfc.symm.trans e))]
            rw [hop, play_ne b q (partner q) .white (partner_ne q)]
            exact ho.1.2.1
          · by_cases hcq : c = q
            · rw [otherP, if_pos hcq, play_eq]
              exact sOpen_append_white (sEven_sOpen ho.1.2.1)
            · rw [otherP, if_neg hcq, play_eq]
              exact sOpen_append_white (sQ_sOpen ho.1.1)
          · intro hfc
            rw [otherP, if_pos hfc, play_eq]
            by_cases hl : (b (partner q)).length = 0
            · intro e
              rw [stone_append, if_neg (by omega : ¬ ((0:Nat) < (b (partner q)).length)), if_pos hl.symm] at e
              exact absurd e (by decide)
            · intro e
              rw [stone_append, if_pos (by omega : (0:Nat) < (b (partner q)).length)] at e
              exact absurd (ho.1.2.1 0 e) (by decide)
          · rw [play_eq]
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [play_ne b (otherP q c) c .white (fun e => hone e.symm)]
            exact hfull
          · by_cases hdo : d = otherP q c
            · rw [hdo, play_eq]
              simp only [List.length_append, List.length_singleton]
              omega
            · rw [play_ne b (otherP q c) d .white hdo]
              by_cases hdp : InP q d
              · have hdc : d = c := by
                  rcases inP_pair hcP hoIn (fun e => hone e.symm) hdp with e | e
                  · exact e
                  · exact absurd e hdo
                rw [hdc]
                exact hparC
              · have hp2 := ho.2.2.2.2.1 d hdp
                rw [if_neg (fun e => hdp (by rw [e]; exact hcP))] at hp2
                exact hp2
          · rw [toMove_play', ho.2.2.2.2.2]
            rfl
      · -- Bnd3: Black to move; every legal reply opens column e
        intro q f hfin b hb3
        refine ⟨noBlackFour_phase3 hb3.1, Or.inr (Or.inr ?_)⟩
        have htm : toMove b ≠ .white := by
          rw [hb3.2.2.2.2.2]
          exact fun e => absurd e (by decide)
        rw [if_neg htm, hb3.2.2.2.2.2]
        intro e he
        have hnef : e ≠ f := by
          intro hcon
          rw [hcon] at he
          unfold Legal at he
          rw [hb3.2.2.2.1] at he
          omega
        refine D q f hfin (play b e .black) e ⟨⟨hfin, fun d hd => ?_, ?_, ?_, ?_, ?_, ?_⟩,
          play_valid hb3.2.1 he, ?_, fun d => ?_, ?_, ?_⟩
        · by_cases hde : d = e
          · rw [hde, play_eq]
            have hs1 := hb3.1.rOdd d hd
            have hs2 := hb3.2.2.2.2.1 d
            rw [hde] at hs1 hs2
            exact sOdd_append_black hs1 hs2
          · rw [play_ne b e d .black hde]
            exact hb3.1.rOdd d hd
        · intro hfe
          rw [play_ne b e q .black (by
            intro hcon
            apply hnef
            rw [hfe]
            exact hcon.symm)]
          exact hb3.1.keptQ hfe
        · intro hfe
          rw [play_ne b e (partner q) .black (by
            intro hcon
            apply hnef
            rw [hfe]
            exact hcon.symm)]
          exact hb3.1.keptP hfe
        · by_cases hde : e = otherP q f
          · rw [hde, play_eq]
            exact sOpen_append_black hb3.1.openCol hb3.2.2.1
          · rw [play_ne b e (otherP q f) .black (fun hh => hde hh.symm)]
            exact hb3.1.openCol
        · intro hfe
          by_cases hde2 : e = otherP q f
          · rw [hde2, play_eq]
            intro st
            rw [stone_append, if_pos (by have := hb3.1.nonempty; omega : (0:Nat) < (b (otherP q f)).length)] at st
            exact hb3.1.bottom hfe st
          · rw [play_ne b e (otherP q f) .black (fun hh => hde2 hh.symm)]
            exact hb3.1.bottom hfe
        · by_cases hde : e = otherP q f
          · rw [hde, play_eq]
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [play_ne b e (otherP q f) .black (fun hh => hde hh.symm)]
            exact hb3.1.nonempty
        · rw [play_ne b e f .black (fun hh => hnef hh.symm)]
          exact hb3.2.2.2.1
        · by_cases hde : d = e
          · rw [hde, play_eq]
            simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
            have htr := hb3.2.2.2.2.1 d
            rw [hde] at htr
            omega
          · rw [play_ne b e d .black hde, if_neg hde]
            exact hb3.2.2.2.2.1 d
        · rw [toMove_play', hb3.2.2.2.2.2]
          rfl
        · by_cases hde : e = otherP q f
          · exact Or.inl hde
          · exact Or.inr (by
              rw [play_ne b e (otherP q f) .black (fun hh => hde hh.symm)]
              exact hb3.2.2.1)
      · -- Open3: White caps the opened column; always legal
        intro q f hfin b e ho3
        refine ⟨noBlackFour_phase3 ho3.1, Or.inr (Or.inr ?_)⟩
        rw [if_pos ho3.2.2.2.2.1, ho3.2.2.2.2.1]
        have hleg : Legal h b e := by
          have hv := ho3.2.1 e
          have hp := ho3.2.2.2.1 e
          rw [if_pos rfl] at hp
          unfold Legal
          omega
        have hnef : e ≠ f := by
          intro hcon
          rw [hcon] at hleg
          unfold Legal at hleg
          rw [ho3.2.2.1] at hleg
          omega
        refine ⟨e, hleg, C q f hfin (play b e .white) ⟨⟨hfin, fun d hd => ?_, ?_, ?_, ?_, ?_, ?_⟩,
          play_valid ho3.2.1 hleg, ?_, ?_, ⟨fun d => ?_, ?_⟩⟩⟩
        · by_cases hde : d = e
          · rw [hde, play_eq]
            have hs1 := ho3.1.rOdd d hd
            rw [hde] at hs1
            exact sOdd_append_white hs1
          · rw [play_ne b e d .white hde]
            exact ho3.1.rOdd d hd
        · intro hfe
          rw [play_ne b e q .white (by
            intro hcon
            apply hnef
            rw [hfe]
            exact hcon.symm)]
          exact ho3.1.keptQ hfe
        · intro hfe
          rw [play_ne b e (partner q) .white (by
            intro hcon
            apply hnef
            rw [hfe]
            exact hcon.symm)]
          exact ho3.1.keptP hfe
        · by_cases hde : e = otherP q f
          · rw [hde, play_eq]
            exact sOpen_append_white ho3.1.openCol
          · rw [play_ne b e (otherP q f) .white (fun hh => hde hh.symm)]
            exact ho3.1.openCol
        · intro hfe
          by_cases hde2 : e = otherP q f
          · rw [hde2, play_eq]
            intro st
            rw [stone_append, if_pos (by have := ho3.1.nonempty; omega : (0:Nat) < (b (otherP q f)).length)] at st
            exact ho3.1.bottom hfe st
          · rw [play_ne b e (otherP q f) .white (fun hh => hde2 hh.symm)]
            exact ho3.1.bottom hfe
        · by_cases hde : e = otherP q f
          · rw [hde, play_eq]
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [play_ne b e (otherP q f) .white (fun hh => hde hh.symm)]
            exact ho3.1.nonempty
        · by_cases hde : e = otherP q f
          · rw [hde, play_eq]
            exact topNB_append_white _
          · rw [play_ne b e (otherP q f) .white (fun hh => hde hh.symm)]
            rcases ho3.2.2.2.2.2 with ex | tn
            · exact absurd ex hde
            · exact tn
        · rw [play_ne b e f .white (fun hh => hnef hh.symm)]
          exact ho3.2.2.1
        · by_cases hde : d = e
          · rw [hde, play_eq]
            simp only [List.length_append, List.length_singleton, if_pos rfl, if_true]
            have htr := ho3.2.2.2.1 d
            rw [hde] at htr
            rw [if_pos rfl] at htr
            omega
          · rw [play_ne b e d .white hde]
            have hp2 := ho3.2.2.2.1 d
            rw [if_neg hde] at hp2
            exact hp2
        · rw [toMove_play', ho3.2.2.2.2.1]
          rfl

/-- The initial position of White's pairing strategy. -/
private theorem bnd2_entry (h : Nat) (q : Fin 4) (h2 : 2 ≤ h) :
    Bnd2 h q (play (play (emptyBoard 4) q .black) (partner q) .white) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hs
    cases i with
    | zero => exact Or.inl (by omega)
    | succ i => simp [play, emptyBoard, Function.update, stone, show q ≠ partner q from fun e => partner_ne q e.symm] at hs
  · intro i hs
    cases i with
    | zero => simp [play, emptyBoard, Function.update, stone, show q ≠ partner q from fun e => partner_ne q e.symm, show partner q ≠ q from partner_ne q] at hs
    | succ i => simp [play, emptyBoard, Function.update, stone, show q ≠ partner q from fun e => partner_ne q e.symm, show partner q ≠ q from partner_ne q] at hs
  · intro c hc
    intro i hs
    simp [play, emptyBoard, Function.update, stone, show c ≠ q from fun e => hc (Or.inl e), show c ≠ partner q from fun e => hc (Or.inr e)] at hs
  · unfold Valid
    intro d
    by_cases hdq : d = q
    · rw [hdq]
      simp [play, emptyBoard, Function.update, show q ≠ partner q from fun e => partner_ne q e.symm]
      omega
    · by_cases hdp : d = partner q
      · rw [hdp]
        simp [play, emptyBoard, Function.update, show partner q ≠ q from partner_ne q]
        omega
      · simp [play, emptyBoard, Function.update, hdq, hdp]
  · simp [play, emptyBoard, Function.update, show q ≠ partner q from fun e => partner_ne q e.symm, show partner q ≠ q from partner_ne q]
  · simp [play, emptyBoard, Function.update, show q ≠ partner q from fun e => partner_ne q e.symm, show partner q ≠ q from partner_ne q]
  · intro c hc
    by_cases hcp : c = partner q
    · exact absurd (Or.inr hcp) hc
    · rw [play_ne _ _ _ _ hcp]
      simp [play, emptyBoard, Function.update, show c ≠ q from fun e => hc (Or.inl e), emptyBoard]
  · unfold toMove
    rw [totalStones_play', totalStones_play', totalStones_empty]
    simp

/-- White's nonloss strategy on four columns, every positive even height. -/
theorem white_nonloss_four_columns {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .white (emptyBoard 4) := by
  intro k
  have e4 : totalStones (emptyBoard 4) = 0 := totalStones_empty 4
  match k with
  | 0 =>
      intro hw
      have hk := hasFour_minStones hw
      rw [e4] at hk
      omega
  | 1 =>
      refine ⟨fun hw => ?_, Or.inr (Or.inr ?_)⟩
      · have hk := hasFour_minStones hw
        rw [e4] at hk
        omega
      · rw [toMove_empty]
        intro q hq
        intro hw
        have hk := hasFour_minStones hw
        rw [totalStones_play', e4] at hk
        omega
  | (k + 2) =>
      refine ⟨fun hw => ?_, Or.inr (Or.inr ?_)⟩
      · have hk := hasFour_minStones hw
        rw [e4] at hk
        omega
      · rw [toMove_empty, if_neg (fun e => absurd e (by decide))]
        intro q hq
        refine ⟨fun hw => ?_, Or.inr (Or.inr ?_)⟩
        · have hk := hasFour_minStones hw
          rw [totalStones_play', e4] at hk
          omega
        · have htm : toMove (play (emptyBoard 4) q .black) = .white := by
            rw [toMove_play', toMove_empty]
            rfl
          rw [htm, if_pos rfl]
          have hpleg : Legal h (play (emptyBoard 4) q .black) (partner q) := by
            unfold Legal
            rw [play_ne _ _ _ _ (partner_ne q)]
            unfold Legal at hq
            have hn : (emptyBoard 4 (partner q)).length = 0 := by
              simp [emptyBoard]
            rw [hn]
            omega
          exact ⟨partner q, hpleg,
            (white_pairing_aux h hh k).1 q _ (bnd2_entry h q h2)⟩

#print axioms white_nonloss_four_columns

/-! ## Stage 2: Black's half — supported-stone machinery -/

def TopBlack (l : List Player) : Prop :=
  l.length = 0 ∨ stone l (l.length - 1) = some .black

def WSup (l : List Player) : Prop :=
  ∀ i, stone l i = some .white → 1 ≤ i → stone l (i - 1) = some .black

theorem topBlack_append_black (l : List Player) : TopBlack (l ++ [Player.black]) := by
  right
  have hlen : (l ++ [Player.black]).length - 1 = l.length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hlen, stone_append, if_neg (by omega), if_pos rfl]

theorem wsup_append_black (hs : WSup l) : WSup (l ++ [Player.black]) := by
  intro i hw hi
  have hb : i < (l ++ [Player.black]).length := stone_bound _ i _ hw
  simp only [List.length_append, List.length_singleton] at hb
  by_cases hex : i = l.length
  · rw [stone_append, if_neg (by omega), if_pos hex] at hw
    exact absurd hw (by decide)
  have hw' : stone l i = some .white := by
    rw [stone_append, if_pos (by omega)] at hw; exact hw
  have hs0 : stone l (i - 1) = some .black := hs i hw' hi
  rw [stone_append, if_pos (by omega : i - 1 < l.length)]
  exact hs0

theorem wsup_append_white (hs : WSup l) (ht : TopBlack l) :
    WSup (l ++ [Player.white]) := by
  intro i hw hi
  by_cases he : i = l.length
  · rcases ht with h0 | hb
    · cases l with
      | nil => rw [he] at hi; simp at hi
      | cons a l => simp at h0
    · rw [he, stone_append, if_pos (by
          have hlb := stone_bound l (l.length - 1) Player.black hb
          omega)]
      exact hb
  · have hlt : i < l.length := by
      have hb : i < (l ++ [Player.white]).length := stone_bound _ i _ hw
      simp only [List.length_append, List.length_singleton] at hb
      omega
    have hw' : stone l i = some .white := by
      rw [stone_append, if_pos (by omega : i < l.length)] at hw
      exact hw
    have hs0 : stone l (i - 1) = some .black := hs i hw' hi
    rw [stone_append, if_pos (by omega : i - 1 < l.length)]
    exact hs0

theorem stone_old_play (b : Board 4) (c : Fin 4) (p : Player) (d : Fin 4) (i : Nat)
    (hlt : i < (b d).length) : stone (play b c p d) i = stone (b d) i := by
  by_cases h : d = c
  · subst h
    rw [play_eq, stone_append, if_pos hlt]
  · rw [play_ne b c d p h]

/-- The supported-descent safety core: if every White stone is Black-supported
(or bottom, with bottom lines blocked by fixed stones), White's freshly played
stone cannot complete a four — otherwise shifting the line down one row gives a
Black four that already existed. -/
private theorem white_line_cell {h : Nat} {b1 : Board 4} {x y dy : Int}
    (hd : HasFourDir h b1 .white x y 1 dy) (hx : x = 0) (j : Nat) (hj : j < 4) :
    stone (b1 ⟨j, by omega⟩) (y + (j : Int) * dy).toNat = some .white := by
  have hdi := hd ⟨j, hj⟩
  have hicoe : ((⟨j, hj⟩ : Fin 4) : Int) = (j : Int) := rfl
  obtain ⟨cj, hxc, hyc, hyh, sc⟩ := cellAtInt_some hdi
  rw [hicoe] at hxc
  have hcj : cj = ⟨j, by omega⟩ := Fin.ext (by have := cj.isLt; omega)
  rw [hcj] at sc
  exact sc

private theorem cellAtInt_mk {h : Nat} {b : Board 4} {X Y : Int} (col : Fin 4)
    (hcol : (col : Int) = X) (hX1 : 0 ≤ X) (hX2 : X < (4 : Int))
    (hY1 : 0 ≤ Y) (hY2 : Y < (h : Int)) :
    cellAtInt h b X Y = stone (b col) Y.toNat := by
  have hval : X.toNat = col.val := by omega
  simp only [cellAtInt]
  split
  · split
    · exact congrArg (fun cc : Fin 4 => stone (b cc) Y.toNat) (Fin.ext hval)
    · rename_i hy
      exact absurd ⟨hY1, hY2⟩ hy
  · rename_i hx
    exact absurd ⟨hX1, hX2⟩ hx

theorem noWhiteFour_descent {h : Nat} {b : Board 4} {c : Fin 4}
    (hsup : ∀ d : Fin 4, WSup (b d))
    (htop : TopBlack (b c))
    (fb0 : stone (b ⟨0, by decide⟩) 0 = some .black)
    (hfbl : stone (b ⟨0, by decide⟩) 3 = some .black ∨ stone (b ⟨1, by decide⟩) 2 = some .black ∨
      stone (b ⟨2, by decide⟩) 1 = some .black ∨ stone (b ⟨3, by decide⟩) 0 = some .black)
    (hnw : ¬ HasFour h b .white) (hnb : ¬ HasFour h b .black) :
    ¬ HasFour h (play b c .white) .white := by
  intro hw
  have hnew : stone (play b c .white c) (b c).length = some .white := by
    rw [play_eq, stone_append, if_neg (by omega), if_pos rfl]
  have hsup1 : ∀ d : Fin 4, WSup (play b c .white d) := by
    intro d
    by_cases h : d = c
    · rw [h, play_eq]
      exact wsup_append_white (hsup c) htop
    · rw [play_ne b c d .white h]
      exact hsup d
  rcases hw with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s1 : cellAtInt h (play b c .white) x (y + 1) = some .white := by
      simpa using hd ⟨1, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    obtain ⟨c1, hx1, hy1, _, t1⟩ := cellAtInt_some s1
    have e1 : c1 = c0 := Fin.ext (by omega)
    rw [e1] at t1
    have i1 : (y + 1).toNat = y.toNat + 1 := by omega
    rw [i1] at t1
    have hsupp := hsup1 c0 (y.toNat + 1) t1 (by omega)
    have hnorm : y.toNat + 1 - 1 = y.toNat := by omega
    rw [hnorm] at hsupp
    rw [hsupp] at t0
    exact absurd t0 (by decide)
  · -- horizontal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) y = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) y.toNat = some .white := by
      intro j
      have hz : y + (j.val : Int) * 0 = y := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [hz] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hn0 : y.toNat = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hn0] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · by_cases hmn : (b c).length = y.toNat
      · have hshift : ∀ j : Fin 4, stone (b j) (y.toNat - 1) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              rcases htop with h0 | hb
              · rw [h0] at hmn; omega
              · exact hb
            rw [← hcj, ← hmn]
            exact htop'
          · have hold : stone (b j) y.toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : y.toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            exact hsup j y.toNat hold (by omega)
        refine hnb (Or.inr (Or.inl ⟨0, ((y.toNat - 1 : Int)), ?_⟩))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show ((y.toNat - 1 : Int)) + (i.val : Int) * 0 = (y.toNat - 1 : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y.toNat - 1 : Int)) (by omega : ((y.toNat - 1 : Int)) < (h : Int))]
        rw [show ((y.toNat - 1 : Int)).toNat = y.toNat - 1 from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inl ⟨0, y, ?_⟩))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show y + (i.val : Int) * 0 = y from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega) hy0 hyh0]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : y.toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : y.toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound
  · -- rising diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y + 3) = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int)).toNat = some .white := by
      intro j
      have h1 : y + (j.val : Int) * 1 = y + (j.val : Int) := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [h1] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy0c : y = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hy0c, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hk0
      simp only [Int.mul_one, Int.add_zero, Int.toNat_zero] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · have hy1 : (1:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y + (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y + (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              rcases htop with h0 | hb
              · rw [h0] at hmn
                omega
              · exact hb
            rw [← hcj]
            have hrow : (y + (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y + (j.val : Int) := by omega
            rw [show (y + (j.val : Int) - 1).toNat = (y + (j.val : Int)).toNat - 1 from by omega]
            exact hsup j (y + (j.val : Int)).toNat hold (by omega)
        refine hnb (Or.inr (Or.inr (Or.inl ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * 1 = y - 1 + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 + (i.val : Int))) (by omega : (y - 1 + (i.val : Int)) < (h : Int))]
        rw [show (y - 1 + (i.val : Int)).toNat = (y + (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inl ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show y + (i.val : Int) * 1 = y + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega) (by omega)
          (by omega : y + (i.val : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound
  · -- falling diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y - 3) = some .white := by
      have h3 := hd ⟨3, by decide⟩
      rw [show ((⟨3, by decide⟩ : Fin 4) : Int) = 3 from rfl] at h3
      have hbr : y + 3 * (-1 : Int) = y - 3 := by omega
      rw [hbr] at h3
      exact h3
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
      intro j
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy3 : y - 3 = 0
    · rcases hfbl with fb | fb | fb | fb
      · have hlen : 3 < (b ⟨0, by decide⟩).length := stone_bound _ 3 _ fb
        have hb1c : stone (play b c .white ⟨0, by decide⟩) 3 = some .black := by
          rw [stone_old_play _ _ _ _ _ hlen]; exact fb
        have hk0 := key ⟨0, by decide⟩
        rw [show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hk0
        have hn0 : (y + (0 : Int) * (-1 : Int)).toNat = 3 := by omega
        rw [hn0] at hk0
        rw [hb1c] at hk0
        exact absurd hk0 (by decide)
      · have hlen : 2 < (b ⟨1, by decide⟩).length := stone_bound _ 2 _ fb
        have hb1c : stone (play b c .white ⟨1, by decide⟩) 2 = some .black := by
          rw [stone_old_play _ _ _ _ _ hlen]; exact fb
        have hk1 := key ⟨1, by decide⟩
        rw [show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hk1
        have hn1 : (y + (1 : Int) * (-1 : Int)).toNat = 2 := by omega
        rw [hn1] at hk1
        rw [hb1c] at hk1
        exact absurd hk1 (by decide)
      · have hlen : 1 < (b ⟨2, by decide⟩).length := stone_bound _ 1 _ fb
        have hb1c : stone (play b c .white ⟨2, by decide⟩) 1 = some .black := by
          rw [stone_old_play _ _ _ _ _ hlen]; exact fb
        have hk2 := key ⟨2, by decide⟩
        rw [show ((⟨2, by decide⟩ : Fin 4) : Int) = 2 from rfl] at hk2
        have hn2 : (y + (2 : Int) * (-1 : Int)).toNat = 1 := by omega
        rw [hn2] at hk2
        rw [hb1c] at hk2
        exact absurd hk2 (by decide)
      · have hlen : 0 < (b ⟨3, by decide⟩).length := stone_bound _ 0 _ fb
        have hb1c : stone (play b c .white ⟨3, by decide⟩) 0 = some .black := by
          rw [stone_old_play _ _ _ _ _ hlen]; exact fb
        have hk3 := key ⟨3, by decide⟩
        rw [show ((⟨3, by decide⟩ : Fin 4) : Int) = 3 from rfl] at hk3
        have hn3 : (y + (3 : Int) * (-1 : Int)).toNat = 0 := by omega
        rw [hn3] at hk3
        rw [hb1c] at hk3
        exact absurd hk3 (by decide)
    · have hy4 : (4:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y - (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y - (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              rcases htop with h0 | hb
              · rw [h0] at hmn
                omega
              · exact hb
            rw [← hcj]
            have hrow : (y - (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int) * (-1 : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y - (j.val : Int) := by omega
            rw [show (y - (j.val : Int) - 1).toNat = (y + (j.val : Int) * (-1 : Int)).toNat - 1 from by omega]
            exact hsup j (y + (j.val : Int) * (-1 : Int)).toNat hold (by omega)
        refine hnb (Or.inr (Or.inr (Or.inr ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * (-1 : Int) = y - 1 - (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 - (i.val : Int))) (by omega : (y - 1 - (i.val : Int)) < (h : Int))]
        rw [show (y - 1 - (i.val : Int)).toNat = (y - (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inr ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ y + (i.val : Int) * (-1 : Int))
          (by omega : y + (i.val : Int) * (-1 : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound

/-! ## M2: Black's permanent-defense state machine -/

theorem cellAtInt_play_eq {h : Nat} {b : Board 4} {c : Fin 4} {q p : Player}
    (hpq : q ≠ p) {X Y : Int}
    (hcell : cellAtInt h (play b c q) X Y = some p) : cellAtInt h b X Y = some p := by
  obtain ⟨col, hX, hy1, hy2, hs⟩ := cellAtInt_some hcell
  have hcol4 : X < ((4 : Nat) : Int) := by
    have h4 := col.isLt
    have hX4 : X = (col : Int) := hX
    omega
  rw [cellAtInt_mk col hX.symm (by omega) (by omega) hy1 hy2]
  by_cases hcc : col = c
  · rw [hcc, play_eq, stone_append] at hs
    rw [hcc]
    by_cases hlt : Y.toNat < (b c).length
    · rw [if_pos hlt] at hs
      exact hs
    · rw [if_neg hlt] at hs
      by_cases heq : Y.toNat = (b c).length
      · rw [if_pos heq] at hs
        exact absurd hs (by intro hcon; exact hpq (Option.some.inj hcon))
      · rw [if_neg heq] at hs
        exact absurd hs (by intro hcon; exact absurd hcon (by simp))
  · rw [play_ne b c col q hcc] at hs
    exact hs

theorem hasFour_play_other {h : Nat} {b : Board 4} {c : Fin 4} {q p : Player}
    (hpq : q ≠ p) (hn : ¬ HasFour h b p) : ¬ HasFour h (play b c q) p := by
  intro hw
  apply hn
  rcases hw with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · exact Or.inl ⟨x, y, fun i => cellAtInt_play_eq hpq (hd i)⟩
  · exact Or.inr (Or.inl ⟨x, y, fun i => cellAtInt_play_eq hpq (hd i)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, fun i => cellAtInt_play_eq hpq (hd i)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, fun i => cellAtInt_play_eq hpq (hd i)⟩))

structure PDstate (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup : ∀ d : Fin 4, WSup (b d)
  htop : ∀ d : Fin 4, Legal h b d → TopBlack (b d)
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fbl : stone (b ⟨0, by decide⟩) 3 = some .black ∨ stone (b ⟨1, by decide⟩) 2 = some .black ∨
    stone (b ⟨2, by decide⟩) 1 = some .black ∨ stone (b ⟨3, by decide⟩) 0 = some .black
  hnw : ¬ HasFour h b .white

structure Wstate (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup : ∀ d : Fin 4, WSup (b d)
  htopO : ∀ d : Fin 4, d ≠ c → Legal h b d → TopBlack (b d)
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fbl : stone (b ⟨0, by decide⟩) 3 = some .black ∨ stone (b ⟨1, by decide⟩) 2 = some .black ∨
    stone (b ⟨2, by decide⟩) 1 = some .black ∨ stone (b ⟨3, by decide⟩) 0 = some .black
  hnw : ¬ HasFour h b .white

theorem pd_to_wstate {h : Nat} {b : Board 4} (hp : PDstate h b) (c : Fin 4)
    (hc : Legal h b c) (hnb : ¬ HasFour h b .black) : Wstate h (play b c .white) c := by
  refine ⟨play_valid hp.hv hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toMove_play', hp.htm]
    rfl
  · intro d
    by_cases hde : d = c
    · rw [hde, play_eq]
      exact wsup_append_white (hp.hsup c) (hp.htop c hc)
    · rw [play_ne b c d .white hde]
      exact hp.hsup d
  · intro d hdd hdl
    rw [play_ne b c d .white hdd]
    refine hp.htop d ?_
    unfold Legal at hdl
    unfold Legal
    have hlen : (play b c .white d).length = (b d).length := by
      rw [play_ne b c d .white hdd]
    omega
  · rw [stone_old_play b c .white ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hp.fb0
      omega)]
    exact hp.fb0
  · rcases hp.fbl with fb | fb | fb | fb
    · refine Or.inl ?_
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 3 _ fb)]
      exact fb
    · refine Or.inr (Or.inl ?_)
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 2 _ fb)]
      exact fb
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 1 _ fb)]
      exact fb
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 0 _ fb)]
      exact fb
  · exact noWhiteFour_descent hp.hsup (hp.htop c hc) hp.fb0 hp.fbl hp.hnw hnb

theorem wstate_reply {h : Nat} {b : Board 4} {c e : Fin 4} (hw : Wstate h b c)
    (he : Legal h b e) (hce : e = c ∨ ¬ Legal h b c) : PDstate h (play b e .black) := by
  refine ⟨play_valid hw.hv he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toMove_play', hw.htm]
    rfl
  · intro d
    by_cases hde : d = e
    · rw [hde, play_eq]
      exact wsup_append_black (hw.hsup e)
    · rw [play_ne b e d .black hde]
      exact hw.hsup d
  · intro d hd
    by_cases hde : d = e
    · rw [hde, play_eq]
      exact topBlack_append_black _
    · rw [play_ne b e d .black hde]
      have hd0 : Legal h b d := by
        unfold Legal at hd
        unfold Legal
        have hlen : (play b e .black d).length = (b d).length := by
          rw [play_ne b e d .black hde]
        omega
      by_cases hdc : d = c
      · rcases hce with hec | hnc
        · exact absurd (hdc.trans hec.symm) hde
        · rw [hdc] at hd0
          exact absurd hd0 hnc
      · exact hw.htopO d hdc hd0
  · rw [stone_old_play b e .black ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hw.fb0
      omega)]
    exact hw.fb0
  · rcases hw.fbl with fb | fb | fb | fb
    · refine Or.inl ?_
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 3 _ fb)]
      exact fb
    · refine Or.inr (Or.inl ?_)
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 2 _ fb)]
      exact fb
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 1 _ fb)]
      exact fb
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [stone_old_play _ _ _ _ _ (stone_bound _ 0 _ fb)]
      exact fb
  · exact hasFour_play_other (by decide) hw.hnw

private theorem pd_pairing_aux (h : Nat) :
    ∀ k : Nat, (∀ b, PDstate h b → SafeFor h .black k b) ∧
      (∀ b c, Wstate h b c → SafeFor h .black k b) := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro b hp
        exact hp.hnw
      · intro b c hw
        exact hw.hnw
  | succ k ih =>
      refine ⟨?_, ?_⟩
      · intro b hp
        refine ⟨hp.hnw, ?_⟩
        by_cases hbf : HasFour h b .black
        · exact Or.inl hbf
        · refine Or.inr (Or.inr ?_)
          rw [if_neg (by rw [hp.htm]; exact fun e => absurd e (by decide)), hp.htm]
          intro c hc
          exact ih.2 _ c (pd_to_wstate hp c hc hbf)
      · intro b c hw
        refine ⟨hw.hnw, ?_⟩
        by_cases hbf : HasFour h b .black
        · exact Or.inl hbf
        · by_cases hfull : BoardFull h b
          · exact Or.inr (Or.inl hfull)
          · refine Or.inr (Or.inr ?_)
            rw [if_pos hw.htm, hw.htm]
            by_cases hc : Legal h b c
            · exact ⟨c, hc, ih.1 _ (wstate_reply hw hc (Or.inl rfl))⟩
            · obtain ⟨e, he⟩ := exists_legal hw.hv hfull
              exact ⟨e, he, ih.1 _ (wstate_reply hw he (Or.inr hc))⟩

/-! ## M3 (part 1): direct PD entry for White reply column 2 (paper 5.2) -/

theorem pd_state_w2 {h : Nat} {b : Board 4}
    (hcols : b 0 = [Player.black] ∧ b 1 = [] ∧
      b 2 = [Player.white, Player.black] ∧ b 3 = [])
    (h2 : 2 ≤ h) : PDstate h b := by
  obtain ⟨h0, h1, h2c, h3⟩ := hcols
  have hts : totalStones b = 3 := by
    unfold totalStones
    rw [fin4_sum, h0, h1, h2c, h3]
    simp
  have hval : ∀ d : Fin 4, d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by
    intro d
    have hn := d.isLt
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Valid
    intro d
    rcases hval d with hv | hv | hv | hv
    · rw [show d = 0 from Fin.ext hv, h0]; simp; omega
    · rw [show d = 1 from Fin.ext hv, h1]; simp
    · rw [show d = 2 from Fin.ext hv, h2c]; simp; omega
    · rw [show d = 3 from Fin.ext hv, h3]; simp
  · unfold toMove
    rw [hts]
    simp
  · intro d
    rcases hval d with hv | hv | hv | hv
    · rw [show d = 0 from Fin.ext hv, h0]
      intro i hw
      cases i <;> simp [stone] at hw
    · rw [show d = 1 from Fin.ext hv, h1]
      intro i hw
      cases i <;> simp [stone] at hw
    · rw [show d = 2 from Fin.ext hv, h2c]
      intro i hw hi
      cases i with
      | zero => omega
      | succ i =>
          rw [show stone [Player.white, Player.black] (i + 1) = stone [Player.black] i from rfl] at hw
          cases i with
          | zero => simp [stone] at hw
          | succ j =>
              rw [show stone [Player.black] (j + 1) = none from rfl] at hw
              simp at hw
    · rw [show d = 3 from Fin.ext hv, h3]
      intro i hw
      cases i <;> simp [stone] at hw
  · intro d hd
    rcases hval d with hv | hv | hv | hv
    · have hd0 : d = 0 := Fin.ext hv
      rw [hd0] at hd
      unfold Legal at hd
      rw [h0] at hd
      simp at hd
      rw [hd0]
      unfold TopBlack
      rw [h0]
      right
      exact rfl
    · have hd1 : d = 1 := Fin.ext hv
      rw [hd1] at hd
      unfold Legal at hd
      rw [h1] at hd
      simp at hd
      rw [hd1]
      unfold TopBlack
      rw [h1]
      left
      exact rfl
    · have hd2 : d = 2 := Fin.ext hv
      rw [hd2] at hd
      unfold Legal at hd
      rw [h2c] at hd
      simp at hd
      rw [hd2]
      unfold TopBlack
      rw [h2c]
      right
      exact rfl
    · have hd3 : d = 3 := Fin.ext hv
      rw [hd3] at hd
      unfold Legal at hd
      rw [h3] at hd
      simp at hd
      rw [hd3]
      unfold TopBlack
      rw [h3]
      left
      exact rfl
  · rw [show (⟨0, by decide⟩ : Fin 4) = 0 from rfl, h0]
    simp [stone]
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl, h2c]
    simp [stone]
  · intro hw
    have hk := hasFour_minStones hw
    rw [hts] at hk
    omega

theorem black_second_w2 {h : Nat} (h2 : 2 ≤ h) :
    PDstate h (play (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨2, by decide⟩ .white)
      ⟨2, by decide⟩ .black) := by
  refine pd_state_w2 ?_ h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = ⟨0, by decide⟩ from rfl]
    have he : (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨0, by decide⟩ = [Player.black] := rfl
    have hne1 : (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨2, by decide⟩ .white)
        ⟨0, by decide⟩ = [Player.black] := by
      rw [play_ne _ _ _ _ (by decide)]
      exact he
    have hne2 : (play (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨2, by decide⟩ .white)
        ⟨2, by decide⟩ .black) ⟨0, by decide⟩ = [Player.black] := by
      rw [play_ne _ _ _ _ (by decide)]
      exact hne1
    exact hne2
  · rw [show (1 : Fin 4) = ⟨1, by decide⟩ from rfl]
    rfl
  · rw [show (2 : Fin 4) = ⟨2, by decide⟩ from rfl]
    have he : (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨2, by decide⟩ .white)
        ⟨2, by decide⟩ = [Player.white] := rfl
    rw [play_eq, he]
    rfl
  · rw [show (3 : Fin 4) = ⟨3, by decide⟩ from rfl]
    rfl

/-! ## M3 (part 2): PD1 — permanent defense with a static exception cell at (1,1),
entry for White reply column 1 (paper 5.1). Fixed blockers (0,0) and (0,1) handle
every in-board line through the exception; column 1 keeps either a black top or
length 1 (the waiting shape [W]). -/

structure PD1 (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup1 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (d = ⟨1, by decide⟩ ∧ i = 1)
  h1bot : stone (b ⟨1, by decide⟩) 0 = some .white
  h1pat : (b ⟨1, by decide⟩).length = 1 ∨
    (stone (b ⟨1, by decide⟩) 1 = some .white ∧
      (TopBlack (b ⟨1, by decide⟩) ∨ h ≤ (b ⟨1, by decide⟩).length))
  htop1 : ∀ d : Fin 4, Legal h b d → d ≠ ⟨1, by decide⟩ → TopBlack (b d)
  fbD : stone (b ⟨1, by decide⟩) 2 = some .black ∨ (b ⟨2, by decide⟩).length = 0 ∨
    stone (b ⟨2, by decide⟩) 0 = some .white
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fb01 : stone (b ⟨0, by decide⟩) 1 = some .black
  hnw : ¬ HasFour h b .white
  hAeven : (b ⟨1, by decide⟩).length = 1 →
    ∀ d : Fin 4, d ≠ ⟨1, by decide⟩ → (b d).length % 2 = 0

structure W1 (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup1 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (d = ⟨1, by decide⟩ ∧ i = 1)
  h1bot : stone (b ⟨1, by decide⟩) 0 = some .white
  h1patW : (b ⟨1, by decide⟩).length = 1 ∨ stone (b ⟨1, by decide⟩) 1 = some .white
  h1tf : TopBlack (b ⟨1, by decide⟩) ∨ h ≤ (b ⟨1, by decide⟩).length ∨
    c = ⟨1, by decide⟩ ∨ (b ⟨1, by decide⟩).length = 1
  htopO : ∀ d : Fin 4, d ≠ c → Legal h b d → d ≠ ⟨1, by decide⟩ → TopBlack (b d)
  fbD : stone (b ⟨1, by decide⟩) 2 = some .black ∨ (b ⟨2, by decide⟩).length = 0 ∨
    stone (b ⟨2, by decide⟩) 0 = some .white
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fb01 : stone (b ⟨0, by decide⟩) 1 = some .black
  hnw : ¬ HasFour h b .white
  hAevenW : (b ⟨1, by decide⟩).length = 1 →
    ∀ d : Fin 4, d ≠ ⟨1, by decide⟩ → d ≠ c → (b d).length % 2 = 0
  hcodd : (b ⟨1, by decide⟩).length = 1 → c ≠ ⟨1, by decide⟩ ∧ (b c).length % 2 = 1

theorem wsup1_append_black {l : List Player}
    (hs : ∀ i, stone l i = some .white → 1 ≤ i →
      stone l (i - 1) = some .black ∨ i = 1) :
    ∀ i, stone (l ++ [Player.black]) i = some .white → 1 ≤ i →
      stone (l ++ [Player.black]) (i - 1) = some .black ∨ i = 1 := by
  intro i hw hi
  have hb : i < (l ++ [Player.black]).length := stone_bound _ i _ hw
  simp only [List.length_append, List.length_singleton] at hb
  by_cases hex : i = l.length
  · rw [stone_append, if_neg (by omega), if_pos hex] at hw
    exact absurd hw (by decide)
  have hw' : stone l i = some .white := by
    rw [stone_append, if_pos (by omega)] at hw
    exact hw
  rcases hs i hw' hi with hsup | hex2
  · exact Or.inl (by
      rw [stone_append, if_pos (by omega : i - 1 < l.length)]
      exact hsup)
  · exact Or.inr hex2

theorem wsup1_append_white {l : List Player} (hnn : 1 ≤ l.length)
    (hb : stone l (l.length - 1) = some .black)
    (hs : ∀ i, stone l i = some .white → 1 ≤ i →
      stone l (i - 1) = some .black ∨ i = 1) :
    ∀ i, stone (l ++ [Player.white]) i = some .white → 1 ≤ i →
      stone (l ++ [Player.white]) (i - 1) = some .black ∨ i = 1 := by
  intro i hw hi
  have hbb : i < (l ++ [Player.white]).length := stone_bound _ i _ hw
  simp only [List.length_append, List.length_singleton] at hbb
  by_cases he : i = l.length
  · rw [he] at ⊢ hi
    exact Or.inl (by
      rw [stone_append, if_pos (by omega : l.length - 1 < l.length)]
      exact hb)
  have hw' : stone l i = some .white := by
    rw [stone_append, if_pos (by omega : i < l.length)] at hw
    exact hw
  rcases hs i hw' hi with hsup | hex
  · exact Or.inl (by
      rw [stone_append, if_pos (by omega : i - 1 < l.length)]
      exact hsup)
  · rw [hex] at hi
    omega

/-! ## M3 (part 2b): PD1 safety core and state machine -/

theorem hsup1_play {b : Board 4} {c : Fin 4}
    (hsup1 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
      stone (b d) (i - 1) = some .black ∨ (d = ⟨1, by decide⟩ ∧ i = 1))
    (hc1w : c = ⟨1, by decide⟩ → TopBlack (b ⟨1, by decide⟩) ∨ (b ⟨1, by decide⟩) = [Player.white])
    (htopc : c ≠ ⟨1, by decide⟩ → TopBlack (b c)) :
    ∀ d : Fin 4, ∀ i, stone (play b c .white d) i = some .white → 1 ≤ i →
      stone (play b c .white d) (i - 1) = some .black ∨ (d = ⟨1, by decide⟩ ∧ i = 1) := by
  intro d i hw2 hi
  by_cases hdc : d = c
  · rw [hdc] at hw2
    rw [play_eq] at hw2
    rw [hdc, play_eq]
    by_cases hlen0 : (b c).length = 0
    · -- fresh stone is the only stone; no white at i >= 1
      have hbb : i < (b c).length + 1 := by
        have := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
        simp only [List.length_append, List.length_singleton] at this
        omega
      omega
    · by_cases hwait : c = ⟨1, by decide⟩ ∧ (b c).length = 1
      · -- waiting shape: fresh stone lands exactly at the exception cell
        have hbb : i < (b c).length + 1 := by
          have := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
          simp only [List.length_append, List.length_singleton] at this
          omega
        rcases Nat.lt_or_ge i (b c).length with hilt | hge
        · have hltm : i - 1 < (b c).length := by omega
          rw [stone_append, if_pos hltm]
          have hw2' : stone (b c) i = some .white := by
            rw [stone_append, if_pos hilt] at hw2
            exact hw2
          rcases hsup1 c i hw2' hi with hsup | hex
          · exact Or.inl hsup
          · exact Or.inr hex
        · have hi1 : i = 1 := by omega
          exact Or.inr ⟨hwait.1, hi1⟩
      · have hpos : 1 ≤ (b c).length := by omega
        have hbtop : stone (b c) ((b c).length - 1) = some .black := by
          by_cases hc1 : c = ⟨1, by decide⟩
          · have hne : ¬((b c) = [Player.white]) := by
              intro heq
              have h1 : (b c).length = 1 := by rw [heq]; rfl
              exact hwait ⟨hc1, h1⟩
            rcases hc1w hc1 with hb | hlist
            · rcases hb with h0 | h2
              · rw [← hc1] at h0
                exact absurd h0 (by omega)
              · rw [hc1]
                exact h2
            · rw [hc1] at hne
              exact absurd hlist hne
          · rcases htopc hc1 with h0 | h2
            · exact absurd h0 (by omega)
            · exact h2
        have hbb : i < (b c).length + 1 := by
          have hsb := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
          simp only [List.length_append, List.length_singleton] at hsb
          omega
        rcases Nat.lt_or_ge i (b c).length with hilt | hge
        · have hw2' : stone (b c) i = some .white := by
            rw [stone_append, if_pos hilt] at hw2
            exact hw2
          rcases hsup1 c i hw2' hi with hsup | hex
          · refine Or.inl ?_
            rw [stone_append, if_pos (by omega : i - 1 < (b c).length)]
            exact hsup
          · exact Or.inr hex
        · have hie : i = (b c).length := by omega
          rw [hie]
          refine Or.inl ?_
          rw [stone_append, if_pos (by omega : (b c).length - 1 < (b c).length)]
          exact hbtop
  · rw [play_ne b c d .white hdc] at hw2
    rw [play_ne b c d .white hdc]
    exact hsup1 d i hw2 hi


theorem noWhiteFour_descent1 {h : Nat} {b : Board 4} {c : Fin 4}
    (hsup1 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
      stone (b d) (i - 1) = some .black ∨ (d = ⟨1, by decide⟩ ∧ i = 1))
    (hc1w : c = ⟨1, by decide⟩ → TopBlack (b ⟨1, by decide⟩) ∨ (b ⟨1, by decide⟩) = [Player.white])
    (htopc : c ≠ ⟨1, by decide⟩ → TopBlack (b c))
    (fb0 : stone (b ⟨0, by decide⟩) 0 = some .black)
    (fb01 : stone (b ⟨0, by decide⟩) 1 = some .black)
    (fbD : stone (play b c .white ⟨1, by decide⟩) 2 = some .black ∨
      stone (play b c .white ⟨2, by decide⟩) 1 ≠ some .white)
    (hnw : ¬ HasFour h b .white) (hnb : ¬ HasFour h b .black) :
    ¬ HasFour h (play b c .white) .white := by
  intro hw
  have hsup1' := hsup1_play hsup1 hc1w htopc
  rcases hw with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    obtain ⟨c0, hx0, hy0, _, _⟩ := cellAtInt_some s0
    have s1 : cellAtInt h (play b c .white) x (y + 1) = some .white := by
      simpa using hd ⟨1, by decide⟩
    have s2 : cellAtInt h (play b c .white) x (y + 2) = some .white := by
      simpa using hd ⟨2, by decide⟩
    obtain ⟨c1, hx1, hy1, _, t1⟩ := cellAtInt_some s1
    obtain ⟨c2, hx2, hy2, _, t2⟩ := cellAtInt_some s2
    have e2 : c2 = c1 := Fin.ext (by omega)
    rw [e2] at t2
    have i2 : (y + 2).toNat = y.toNat + 2 := by omega
    rw [i2] at t2
    have i1 : (y + 1).toNat = y.toNat + 1 := by omega
    rw [i1] at t1
    rcases hsup1' c1 (y.toNat + 2) t2 (by omega) with hsupp | hex
    · have hnorm : y.toNat + 2 - 1 = y.toNat + 1 := by omega
      rw [hnorm] at hsupp
      rw [hsupp] at t1
      exact absurd t1 (by decide)
    · exact absurd hex.2 (by omega)
  · -- horizontal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) y = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) y.toNat = some .white := by
      intro j
      have hz : y + (j.val : Int) * 0 = y := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [hz] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hn0 : y.toNat = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hn0] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · by_cases hn1 : y.toNat = 1
      · have hb1len : 1 < (b ⟨0, by decide⟩).length := stone_bound _ 1 _ fb01
        have hb1c : stone (play b c .white ⟨0, by decide⟩) 1 = some .black := by
          rw [stone_old_play _ _ _ _ _ hb1len]
          exact fb01
        have hk0 := key ⟨0, by decide⟩
        rw [hn1] at hk0
        rw [hb1c] at hk0
        exact absurd hk0 (by decide)
      · have hy2 : 2 ≤ y.toNat := by omega
        by_cases hmn : (b c).length = y.toNat
        · have hshift : ∀ j : Fin 4, stone (b j) (y.toNat - 1) = some .black := by
            intro j
            by_cases hcj : c = j
            · have htop' : stone (b c) ((b c).length - 1) = some .black := by
                by_cases hc1 : c = ⟨1, by decide⟩
                · rw [hc1] at hmn ⊢
                  rcases hc1w hc1 with hb | hlist
                  · rcases hb with h0 | hb'
                    · exact absurd h0 (by omega)
                    · exact hb'
                  · have h1l : (b ⟨1, by decide⟩).length = 1 := by rw [hlist]; rfl
                    omega
                · rcases htopc hc1 with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
              rw [← hcj, ← hmn]
              exact htop'
            · have hold : stone (b j) y.toNat = some .white := by
                have hk := key j
                rw [stone_old_play _ _ _ _ _ ?_] at hk
                · exact hk
                · have hlen : (play b c .white j).length = (b j).length := by
                    rw [play_ne b c j .white (fun e => hcj e.symm)]
                  have hkbound : y.toNat < (play b c .white j).length :=
                    stone_bound _ _ _ hk
                  rw [hlen] at hkbound
                  exact hkbound
              rcases hsup1 j y.toNat hold (by omega) with hsup | hex
              · exact hsup
              · exact absurd hex.2 (by omega)
          refine hnb (Or.inr (Or.inl ⟨0, ((y.toNat - 1 : Int)), ?_⟩))
          intro i
          rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
              show ((y.toNat - 1 : Int)) + (i.val : Int) * 0 = (y.toNat - 1 : Int) from by omega]
          rw [cellAtInt_mk i rfl (by omega) (by omega)
            (by omega : (0:Int) ≤ (y.toNat - 1 : Int)) (by omega : ((y.toNat - 1 : Int)) < (h : Int))]
          rw [show ((y.toNat - 1 : Int)).toNat = y.toNat - 1 from by omega]
          exact hshift i
        · refine hnw (Or.inr (Or.inl ⟨0, y, ?_⟩))
          intro i
          rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
              show y + (i.val : Int) * 0 = y from by omega]
          rw [cellAtInt_mk i rfl (by omega) (by omega) hy0 hyh0]
          have hk := key i
          rw [stone_old_play _ _ _ _ _ ?_] at hk
          · exact hk
          · by_cases he : i = c
            · subst he
              have hkbound : y.toNat < (play b i .white i).length := stone_bound _ _ _ hk
              have hlen2 : (play b i .white i).length = (b i).length + 1 := by
                simp [play, Function.update, List.length_append]
              omega
            · have hlen : (play b c .white i).length = (b i).length := by
                rw [play_ne b c i .white he]
              have hkbound : y.toNat < (play b c .white i).length := stone_bound _ _ _ hk
              rw [hlen] at hkbound
              exact hkbound
  · -- rising diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y + 3) = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int)).toNat = some .white := by
      intro j
      have h1 : y + (j.val : Int) * 1 = y + (j.val : Int) := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [h1] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy0c : y = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hy0c, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hk0
      simp only [Int.mul_one, Int.add_zero, Int.toNat_zero] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · have hy1 : (1:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y + (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y + (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              by_cases hc1 : c = ⟨1, by decide⟩
              · rw [hc1, show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hmn
                rw [hc1]
                rcases hc1w hc1 with hb | hlist
                · rcases hb with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
                · have h1l : (b ⟨1, by decide⟩).length = 1 := by rw [hlist]; rfl
                  omega
              · rcases htopc hc1 with h0 | hb'
                · exact absurd h0 (by omega)
                · exact hb'
            rw [← hcj]
            have hrow : (y + (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y + (j.val : Int) := by omega
            rw [show (y + (j.val : Int) - 1).toNat = (y + (j.val : Int)).toNat - 1 from by omega]
            rcases hsup1 j (y + (j.val : Int)).toNat hold (by omega) with hsup | hex
            · exact hsup
            · have hex2 : (y + (j.val : Int)).toNat = 1 := hex.2
              rw [hex.1, show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hex2
              omega
        refine hnb (Or.inr (Or.inr (Or.inl ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * 1 = y - 1 + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 + (i.val : Int))) (by omega : (y - 1 + (i.val : Int)) < (h : Int))]
        rw [show (y - 1 + (i.val : Int)).toNat = (y + (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inl ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show y + (i.val : Int) * 1 = y + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega) (by omega)
          (by omega : y + (i.val : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound
  · -- falling diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y - 3) = some .white := by
      have h3 := hd ⟨3, by decide⟩
      rw [show ((⟨3, by decide⟩ : Fin 4) : Int) = 3 from rfl] at h3
      have hbr : y + 3 * (-1 : Int) = y - 3 := by omega
      rw [hbr] at h3
      exact h3
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
      intro j
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy3 : y - 3 = 0
    · rcases fbD with h12 | h21
      · have hk1 := key ⟨1, by decide⟩
        rw [show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hk1
        have hn1 : (y + (1 : Int) * (-1 : Int)).toNat = 2 := by omega
        rw [hn1] at hk1
        rw [h12] at hk1
        exact absurd hk1 (by decide)
      · have hk2 := key ⟨2, by decide⟩
        rw [show ((⟨2, by decide⟩ : Fin 4) : Int) = 2 from rfl] at hk2
        have hn2 : (y + (2 : Int) * (-1 : Int)).toNat = 1 := by omega
        rw [hn2] at hk2
        exact absurd hk2 h21
    · have hy4 : (4:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y - (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y - (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              by_cases hc1 : c = ⟨1, by decide⟩
              · rw [hc1, show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hmn
                rw [hc1]
                rcases hc1w hc1 with hb | hlist
                · rcases hb with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
                · have h1l : (b ⟨1, by decide⟩).length = 1 := by rw [hlist]; rfl
                  omega
              · rcases htopc hc1 with h0 | hb'
                · exact absurd h0 (by omega)
                · exact hb'
            rw [← hcj]
            have hrow : (y - (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int) * (-1 : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y - (j.val : Int) := by omega
            rw [show (y - (j.val : Int) - 1).toNat = (y + (j.val : Int) * (-1 : Int)).toNat - 1 from by omega]
            rcases hsup1 j (y + (j.val : Int) * (-1 : Int)).toNat hold (by omega) with hsup | hex
            · exact hsup
            · have hex2 : (y + (j.val : Int) * (-1 : Int)).toNat = 1 := hex.2
              rw [hex.1, show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hex2
              omega
        refine hnb (Or.inr (Or.inr (Or.inr ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * (-1 : Int) = y - 1 - (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 - (i.val : Int))) (by omega : (y - 1 - (i.val : Int)) < (h : Int))]
        rw [show (y - 1 - (i.val : Int)).toNat = (y - (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inr ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ y + (i.val : Int) * (-1 : Int))
          (by omega : y + (i.val : Int) * (-1 : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound


/-! ## M3 (part 2d): white-move transfer PD1 -> W1 -/

theorem pd1_to_w1 {h : Nat} {b : Board 4} {c : Fin 4} (hp : PD1 h b)
    (hc : Legal h b c) (hnb : ¬ HasFour h b .black) : W1 h (play b c .white) c := by
  have hc1w : c = ⟨1, by decide⟩ →
      TopBlack (b ⟨1, by decide⟩) ∨ (b ⟨1, by decide⟩) = [Player.white] := by
    intro hc1
    rcases hp.h1pat with hlen1 | hsecond
    · right
      cases hh : (b ⟨1, by decide⟩) with
      | nil =>
        rw [hh] at hlen1
        simp at hlen1
      | cons x xs =>
        cases xs with
        | nil =>
          have h1b := hp.h1bot
          rw [hh] at h1b
          cases x with
          | black => simp [stone] at h1b
          | white => rfl
        | cons y ys =>
          rw [hh] at hlen1
          simp at hlen1
    · rcases hsecond.2 with htb | hfull
      · exact Or.inl htb
      · exfalso
        rw [hc1] at hc
        unfold Legal at hc
        omega
  have htopc : c ≠ ⟨1, by decide⟩ → TopBlack (b c) := hp.htop1 c hc
  have fbDnew : stone (play b c .white ⟨1, by decide⟩) 2 = some .black ∨
      stone (play b c .white ⟨2, by decide⟩) 1 ≠ some .white := by
    rcases hp.fbD with h12 | hc2a | hc2b
    · refine Or.inl ?_
      by_cases hc1 : c = ⟨1, by decide⟩
      · have h2len : 2 < (b ⟨1, by decide⟩).length := stone_bound _ 2 _ h12
        rw [hc1, stone_old_play _ _ _ _ _ (by omega)]
        exact h12
      · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
        exact h12
    · refine Or.inr ?_
      by_cases hc2c : c = ⟨2, by decide⟩
      · rw [hc2c, play_eq, stone_append, if_neg (by omega), if_neg (by rw [hc2a]; omega)]
        simp
      · rw [play_ne b c ⟨2, by decide⟩ .white (fun e => hc2c e.symm)]
        rw [stone_none (b ⟨2, by decide⟩) 1 (by omega)]
        simp
    · refine Or.inr ?_
      by_cases hc2c : c = ⟨2, by decide⟩
      · rw [hc2c]
        by_cases hL1 : (b ⟨2, by decide⟩).length = 1
        · exfalso
          have htb := htopc (by rw [hc2c]; decide)
          rw [hc2c] at htb
          rcases htb with h0 | htopB
          · rw [hL1] at h0
            omega
          · rw [hL1] at htopB
            simp only [Nat.sub_self] at htopB
            exact absurd htopB (by rw [hc2b]; decide)
        · have h20len : 1 < (b ⟨2, by decide⟩).length := by
            have := stone_bound (b ⟨2, by decide⟩) 0 Player.white hc2b
            omega
          rw [stone_old_play _ _ _ _ _ h20len]
          intro h21w
          rcases hp.hsup1 ⟨2, by decide⟩ 1 h21w (by omega) with hB | hex
          · rw [hB] at hc2b
            exact absurd hc2b (by decide)
          · exact absurd hex.1 (by decide)
      · rw [play_ne b c ⟨2, by decide⟩ .white (fun e => hc2c e.symm)]
        intro h21w
        rcases hp.hsup1 ⟨2, by decide⟩ 1 h21w (by omega) with hB | hex
        · rw [hB] at hc2b
          exact absurd hc2b (by decide)
        · exact absurd hex.1 (by decide)
  refine ⟨play_valid hp.hv hc, ?_, hsup1_play hp.hsup1 hc1w htopc, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    noWhiteFour_descent1 hp.hsup1 hc1w htopc hp.fb0 hp.fb01 fbDnew hp.hnw hnb, ?_, ?_⟩
  · rw [toMove_play', hp.htm]
    rfl
  · by_cases hc1 : c = ⟨1, by decide⟩
    · have h1len : 0 < (b ⟨1, by decide⟩).length := stone_bound _ 0 _ hp.h1bot
      rw [hc1, stone_old_play _ _ _ _ _ h1len]
      exact hp.h1bot
    · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
      exact hp.h1bot
  · rcases hp.h1pat with hlen1 | hsecond
    · by_cases hc1 : c = ⟨1, by decide⟩
      · right
        rw [hc1, play_eq, stone_append, if_neg (by omega), if_pos (by rw [hlen1])]
      · left
        rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
        exact hlen1
    · right
      by_cases hc1 : c = ⟨1, by decide⟩
      · have h11len : 1 < (b ⟨1, by decide⟩).length := stone_bound _ 1 _ hsecond.1
        rw [hc1, stone_old_play _ _ _ _ _ (by omega)]
        exact hsecond.1
      · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
        exact hsecond.1
  · by_cases hc1 : c = ⟨1, by decide⟩
    · exact Or.inr (Or.inr (Or.inl hc1))
    · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
      rcases hp.h1pat with hlen1 | hsecond
      · exact Or.inr (Or.inr (Or.inr hlen1))
      · rcases hsecond.2 with htb | hfull
        · exact Or.inl htb
        · exact Or.inr (Or.inl hfull)
  · intro d hdd hdl hd1
    rw [play_ne b c d .white hdd]
    refine hp.htop1 d ?_ hd1
    unfold Legal at hdl
    unfold Legal
    have hlen : (play b c .white d).length = (b d).length := by
      rw [play_ne b c d .white hdd]
    omega
  · rcases hp.fbD with h12 | hc2a | hc2b
    · refine Or.inl ?_
      by_cases hc1 : c = ⟨1, by decide⟩
      · have h2len : 2 < (b ⟨1, by decide⟩).length := stone_bound _ 2 _ h12
        rw [hc1, stone_old_play _ _ _ _ _ (by omega)]
        exact h12
      · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
        exact h12
    · by_cases hc2c : c = ⟨2, by decide⟩
      · refine Or.inr (Or.inr ?_)
        rw [hc2c, play_eq, stone_append, if_neg (by omega), if_pos (by rw [hc2a])]
      · refine Or.inr (Or.inl ?_)
        rw [play_ne b c ⟨2, by decide⟩ .white (fun e => hc2c e.symm)]
        exact hc2a
    · by_cases hc2c : c = ⟨2, by decide⟩
      · refine Or.inr (Or.inr ?_)
        have h0len : 0 < (b ⟨2, by decide⟩).length := stone_bound _ 0 _ hc2b
        rw [hc2c, stone_old_play _ _ _ _ _ h0len]
        exact hc2b
      · refine Or.inr (Or.inr ?_)
        rw [play_ne b c ⟨2, by decide⟩ .white (fun e => hc2c e.symm)]
        exact hc2b
  · rw [stone_old_play b c .white ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hp.fb0
      omega)]
    exact hp.fb0
  · rw [stone_old_play b c .white ⟨0, by decide⟩ 1 (by
      have := stone_bound (b ⟨0, by decide⟩) 1 Player.black hp.fb01
      omega)]
    exact hp.fb01
  · intro hlen1' d hd1 hdc
    by_cases hc1 : c = ⟨1, by decide⟩
    · exfalso
      rw [hc1, play_eq] at hlen1'
      simp only [List.length_append, List.length_singleton] at hlen1'
      have h0len : 0 < (b ⟨1, by decide⟩).length := stone_bound _ 0 _ hp.h1bot
      omega
    · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)] at hlen1'
      rw [play_ne b c d .white hdc]
      exact hp.hAeven hlen1' d hd1
  · intro hlen1'
    by_cases hc1 : c = ⟨1, by decide⟩
    · exfalso
      rw [hc1, play_eq] at hlen1'
      simp only [List.length_append, List.length_singleton] at hlen1'
      have h0len : 0 < (b ⟨1, by decide⟩).length := stone_bound _ 0 _ hp.h1bot
      omega
    · refine ⟨hc1, ?_⟩
      have hlen1 : (b ⟨1, by decide⟩).length = 1 := by
        rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)] at hlen1'
        exact hlen1'
      rw [play_eq]
      simp only [List.length_append, List.length_singleton]
      have hev := hp.hAeven hlen1 c hc1
      omega
/-! ## M3 (part 2e): black reply W1 -> PD1 (cover or fallback) -/

theorem stone_none_inv (l : List Player) (r : Nat) (h : stone l r = none) : l.length ≤ r := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
    cases r with
    | zero => simp [stone] at h
    | succ r =>
      have ihl := ih r h
      simp only [List.length_cons]
      omega

theorem w1_reply {h : Nat} {b : Board 4} {c e : Fin 4} (hw : W1 h b c)
    (he : Legal h b e) (hce : e = c ∨ ¬ Legal h b c) (hh : h % 2 = 0) (h4 : 4 ≤ h) :
    PD1 h (play b e .black) := by
  have hcfull : ¬ Legal h b c → (b c).length = h := by
    intro hnc
    unfold Legal at hnc
    have hvc := hw.hv c
    omega
  have hphaseB : (b ⟨1, by decide⟩).length ≠ 1 → e ≠ ⟨1, by decide⟩ →
      stone (b ⟨1, by decide⟩) 2 = some .black := by
    intro hn1 he1
    rcases hw.h1patW with hlen1 | h11
    · exact absurd hlen1 hn1
    · have h2nw : ¬ stone (b ⟨1, by decide⟩) 2 = some .white := by
        intro h2w
        rcases hw.hsup1 ⟨1, by decide⟩ 2 h2w (by omega) with hB | hex
        · rw [hB] at h11
          exact absurd h11 (by decide)
        · omega
      have h11len : 1 < (b ⟨1, by decide⟩).length := stone_bound _ 1 _ h11
      by_cases hlen2 : (b ⟨1, by decide⟩).length = 2
      · exfalso
        have hntb : ¬ TopBlack (b ⟨1, by decide⟩) := by
          unfold TopBlack
          rw [hlen2]
          intro hcc
          rcases hcc with h0 | htop
          · omega
          · rw [show (2:Nat) - 1 = 1 from rfl] at htop
            rw [htop] at h11
            exact absurd h11 (by decide)
        have hnf : ¬ h ≤ (b ⟨1, by decide⟩).length := by omega
        have hne1 : (b ⟨1, by decide⟩).length ≠ 1 := by omega
        rcases hw.h1tf with htb | hf | hcc | hl1
        · exact absurd htb hntb
        · exact absurd hf hnf
        · rcases hce with hec | hnc
          · exact absurd (hec.trans hcc) he1
          · have hfc := hcfull hnc
            rw [hcc] at hfc
            omega
        · exact absurd hl1 hne1
      · have hlen3 : 2 < (b ⟨1, by decide⟩).length := by omega
        by_cases h2w : stone (b ⟨1, by decide⟩) 2 = some .white
        · exact absurd h2w h2nw
        · cases hst : stone (b ⟨1, by decide⟩) 2 with
          | none =>
            exfalso
            have := stone_none_inv _ _ hst
            omega
          | some p =>
            cases p with
            | black => rfl
            | white => exact absurd hst h2nw
  refine ⟨play_valid hw.hv he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hasFour_play_other (by decide) hw.hnw, ?_⟩
  · rw [toMove_play', hw.htm]
    rfl
  · intro d i hw2 hi
    by_cases hde : d = e
    · rw [hde, play_eq] at hw2
      rw [hde, play_eq]
      have hbb : i < (b e).length + 1 := by
        have hsb := stone_bound ((b e) ++ [Player.black]) i Player.white hw2
        simp only [List.length_append, List.length_singleton] at hsb
        omega
      by_cases hie : i = (b e).length
      · rw [hie] at hw2
        rw [stone_append, if_neg (by omega), if_pos rfl] at hw2
        exact absurd hw2 (by decide)
      have hw2' : stone (b e) i = some .white := by
        rw [stone_append, if_pos (by omega : i < (b e).length)] at hw2
        exact hw2
      rcases hw.hsup1 e i hw2' hi with hsup | hex
      · refine Or.inl ?_
        rw [stone_append, if_pos (by omega : i - 1 < (b e).length)]
        exact hsup
      · exact Or.inr hex
    · rw [play_ne b e d .black hde] at hw2
      rw [play_ne b e d .black hde]
      exact hw.hsup1 d i hw2 hi
  · by_cases he1 : e = ⟨1, by decide⟩
    · have h1len : 0 < (b ⟨1, by decide⟩).length := stone_bound _ 0 _ hw.h1bot
      rw [he1, stone_old_play _ _ _ _ _ h1len]
      exact hw.h1bot
    · rw [play_ne b e ⟨1, by decide⟩ .black (fun hd => he1 hd.symm)]
      exact hw.h1bot
  · by_cases he1 : e = ⟨1, by decide⟩
    · right
      rcases hw.h1patW with hlen1 | h11
      · exfalso
        have hc1ne := (hw.hcodd hlen1).1
        rcases hce with hec | hnc
        · exact absurd (by rw [← hec]; exact he1) hc1ne
        · have hpar := (hw.hcodd hlen1).2
          have hfc := hcfull hnc
          omega
      · have h11len : 1 < (b ⟨1, by decide⟩).length := stone_bound _ 1 _ h11
        rw [he1, play_eq]
        refine ⟨?_, Or.inl (topBlack_append_black _)⟩
        rw [stone_append, if_pos (by omega)]
        exact h11
    · rw [play_ne b e ⟨1, by decide⟩ .black (fun hd => he1 hd.symm)]
      rcases hw.h1patW with hlen1 | h11
      · exact Or.inl hlen1
      · refine Or.inr ⟨h11, ?_⟩
        rcases hw.h1tf with htb | hf | hcc | hl1
        · exact Or.inl htb
        · exact Or.inr hf
        · rcases hce with hec | hnc
          · exact absurd (hec.trans hcc) he1
          · have hfc := hcfull hnc
            rw [hcc] at hfc
            exact Or.inr (le_of_eq hfc.symm)
        · have h11len : 1 < (b ⟨1, by decide⟩).length := stone_bound _ 1 _ h11
          omega
  · intro d hl hd1
    by_cases hde : d = e
    · rw [hde, play_eq]
      exact topBlack_append_black _
    · rw [play_ne b e d .black hde]
      have hd0 : Legal h b d := by
        unfold Legal at hl
        unfold Legal
        have hlen : (play b e .black d).length = (b d).length := by
          rw [play_ne b e d .black hde]
        omega
      by_cases hdc : d = c
      · rcases hce with hec | hnc
        · exact absurd (hdc.trans hec.symm) hde
        · rw [hdc] at hd0
          exact absurd hd0 hnc
      · exact hw.htopO d hdc hd0 hd1
  · rcases hw.fbD with h12 | hc2a | hc2b
    · refine Or.inl ?_
      by_cases he1 : e = ⟨1, by decide⟩
      · have h2len : 2 < (b ⟨1, by decide⟩).length := stone_bound _ 2 _ h12
        rw [he1, stone_old_play _ _ _ _ _ (by omega)]
        exact h12
      · rw [play_ne b e ⟨1, by decide⟩ .black (fun hd => he1 hd.symm)]
        exact h12
    · by_cases he2 : e = ⟨2, by decide⟩
      · refine Or.inl ?_
        rw [play_ne b e ⟨1, by decide⟩ .black (fun hd => absurd (hd.trans he2) (by decide))]
        exact hphaseB (by
          intro hlen1
          exfalso
          rcases hce with hec | hnc
          · have hcc : c = ⟨2, by decide⟩ := (he2.symm.trans hec).symm
            have hpar := (hw.hcodd hlen1).2
            rw [hcc] at hpar
            omega
          · have hpar := (hw.hcodd hlen1).2
            have hfc := hcfull hnc
            omega) (fun hd => absurd (hd.symm.trans he2) (by decide))
      · refine Or.inr (Or.inl ?_)
        rw [play_ne b e ⟨2, by decide⟩ .black (fun hd => he2 hd.symm)]
        exact hc2a
    · by_cases he2 : e = ⟨2, by decide⟩
      · refine Or.inr (Or.inr ?_)
        have h0len : 0 < (b ⟨2, by decide⟩).length := stone_bound _ 0 _ hc2b
        rw [he2, stone_old_play _ _ _ _ _ h0len]
        exact hc2b
      · refine Or.inr (Or.inr ?_)
        rw [play_ne b e ⟨2, by decide⟩ .black (fun hd => he2 hd.symm)]
        exact hc2b
  · rw [stone_old_play b e .black ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hw.fb0
      omega)]
    exact hw.fb0
  · rw [stone_old_play b e .black ⟨0, by decide⟩ 1 (by
      have := stone_bound (b ⟨0, by decide⟩) 1 Player.black hw.fb01
      omega)]
    exact hw.fb01
  · intro hlen1' d hd1
    by_cases he1 : e = ⟨1, by decide⟩
    · exfalso
      rw [he1, play_eq] at hlen1'
      simp only [List.length_append, List.length_singleton] at hlen1'
      have h1len : 0 < (b ⟨1, by decide⟩).length := stone_bound _ 0 _ hw.h1bot
      omega
    · rw [play_ne b e ⟨1, by decide⟩ .black (fun hd => he1 hd.symm)] at hlen1'
      by_cases hdc : d = c
      · rcases hce with hec | hnc
        · rw [hdc, hec, play_eq]
          simp only [List.length_append, List.length_singleton]
          have hpar := (hw.hcodd hlen1').2
          omega
        · exfalso
          have hpar := (hw.hcodd hlen1').2
          have hfc := hcfull hnc
          omega
      · rcases hce with hec | hnc
        · rw [play_ne b e d .black (fun hd => hdc (by rw [hd, hec]))]
          exact hw.hAevenW hlen1' d hd1 hdc
        · exfalso
          have hpar := (hw.hcodd hlen1').2
          have hfc := hcfull hnc
          omega

/-! ## M3 (part 2f): PD1 main induction and the W1 entry (paper 5.1) -/

private theorem pd1_pairing_aux (h : Nat) (hh : h % 2 = 0) (h4 : 4 ≤ h) :
    ∀ k : Nat, (∀ b, PD1 h b → SafeFor h .black k b) ∧
      (∀ b c, W1 h b c → SafeFor h .black k b) := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro b hp
        exact hp.hnw
      · intro b c hw
        exact hw.hnw
  | succ k ih =>
      refine ⟨?_, ?_⟩
      · intro b hp
        refine ⟨hp.hnw, ?_⟩
        by_cases hbf : HasFour h b .black
        · exact Or.inl hbf
        · refine Or.inr (Or.inr ?_)
          rw [if_neg (by rw [hp.htm]; exact fun e => absurd e (by decide)), hp.htm]
          intro c hc
          exact ih.2 _ c (pd1_to_w1 hp hc hbf)
      · intro b c hw
        refine ⟨hw.hnw, ?_⟩
        by_cases hbf : HasFour h b .black
        · exact Or.inl hbf
        · by_cases hfull : BoardFull h b
          · exact Or.inr (Or.inl hfull)
          · refine Or.inr (Or.inr ?_)
            rw [if_pos hw.htm, hw.htm]
            by_cases hc : Legal h b c
            · exact ⟨c, hc, ih.1 _ (w1_reply hw hc (Or.inl rfl) hh h4)⟩
            · obtain ⟨e, he⟩ := exists_legal hw.hv hfull
              exact ⟨e, he, ih.1 _ (w1_reply hw he (Or.inr hc) hh h4)⟩

theorem pd_state_w1 {h : Nat} {b : Board 4}
    (hcols : b 0 = [Player.black, Player.black] ∧ b 1 = [Player.white] ∧
      b 2 = [] ∧ b 3 = [])
    (h2 : 2 ≤ h) : PD1 h b := by
  obtain ⟨h0, h1, h2c, h3⟩ := hcols
  have hts : totalStones b = 3 := by
    unfold totalStones
    rw [fin4_sum, h0, h1, h2c, h3]
    simp
  have hval : ∀ d : Fin 4, d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by
    intro d
    have hn := d.isLt
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Valid
    intro d
    rcases hval d with hv | hv | hv | hv
    · rw [show d = 0 from Fin.ext hv, h0]; simp; omega
    · rw [show d = 1 from Fin.ext hv, h1]; simp; omega
    · rw [show d = 2 from Fin.ext hv, h2c]; simp
    · rw [show d = 3 from Fin.ext hv, h3]; simp
  · unfold toMove
    rw [hts]
    simp
  · intro d i hw hi
    rcases hval d with hv | hv | hv | hv
    · rw [show d = 0 from Fin.ext hv, h0] at hw
      cases i with
      | zero => simp [stone] at hw
      | succ i =>
          rw [show stone [Player.black, Player.black] (i + 1) = stone [Player.black] i from rfl] at hw
          cases i with
          | zero => simp [stone] at hw
          | succ j =>
              rw [show stone [Player.black] (j + 1) = none from rfl] at hw
              simp at hw
    · rw [show d = 1 from Fin.ext hv, h1] at hw
      cases i with
      | zero => omega
      | succ i => cases i <;> simp [stone] at hw
    · rw [show d = 2 from Fin.ext hv, h2c] at hw
      cases i <;> simp [stone] at hw
    · rw [show d = 3 from Fin.ext hv, h3] at hw
      cases i <;> simp [stone] at hw
  · rw [show (⟨1, by decide⟩ : Fin 4) = 1 from rfl, h1]
    rfl
  · left
    rw [show (⟨1, by decide⟩ : Fin 4) = 1 from rfl, h1]
    rfl
  · intro d hd hd1
    rcases hval d with hv | hv | hv | hv
    · have hd0 : d = 0 := Fin.ext hv
      rw [hd0] at hd
      unfold Legal at hd
      rw [h0] at hd
      simp at hd
      rw [hd0]
      unfold TopBlack
      rw [h0]
      right
      rfl
    · exact absurd ((Fin.ext hv).trans rfl) hd1
    · have hd2 : d = 2 := Fin.ext hv
      rw [hd2] at hd
      unfold Legal at hd
      rw [h2c] at hd
      simp at hd
      rw [hd2]
      unfold TopBlack
      rw [h2c]
      left
      rfl
    · have hd3 : d = 3 := Fin.ext hv
      rw [hd3] at hd
      unfold Legal at hd
      rw [h3] at hd
      simp at hd
      rw [hd3]
      unfold TopBlack
      rw [h3]
      left
      rfl
  · refine Or.inr (Or.inl ?_)
    rw [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl, h2c]
    rfl
  · rw [show (⟨0, by decide⟩ : Fin 4) = 0 from rfl, h0]
    simp [stone]
  · rw [show (⟨0, by decide⟩ : Fin 4) = 0 from rfl, h0]
    simp [stone]
  · intro hw
    have hk := hasFour_minStones hw
    rw [hts] at hk
    omega
  · intro hlen1 d hd1
    rcases hval d with hv | hv | hv | hv
    · rw [show d = 0 from Fin.ext hv, h0]
      rfl
    · exact absurd ((Fin.ext hv).trans rfl) hd1
    · rw [show d = 2 from Fin.ext hv, h2c]
      rfl
    · rw [show d = 3 from Fin.ext hv, h3]
      rfl

theorem black_second_w1 {h : Nat} (h2 : 2 ≤ h) :
    PD1 h (play (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨1, by decide⟩ .white)
      ⟨0, by decide⟩ .black) := by
  refine pd_state_w1 ?_ h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = ⟨0, by decide⟩ from rfl]
    have he : (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨0, by decide⟩ = [Player.black] := rfl
    have hne1 : (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨1, by decide⟩ .white)
        ⟨0, by decide⟩ = [Player.black] := by
      rw [play_ne _ _ _ _ (by decide)]
      exact he
    have hne2 : (play (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨1, by decide⟩ .white)
        ⟨0, by decide⟩ .black) ⟨0, by decide⟩ = [Player.black, Player.black] := by
      rw [play_eq, hne1]
      rfl
    exact hne2
  · rw [show (1 : Fin 4) = ⟨1, by decide⟩ from rfl]
    have he : (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨1, by decide⟩ .white)
        ⟨1, by decide⟩ = [Player.white] := rfl
    have hne2 : (play (play (play (emptyBoard 4) ⟨0, by decide⟩ .black) ⟨1, by decide⟩ .white)
        ⟨0, by decide⟩ .black) ⟨1, by decide⟩ = [Player.white] := by
      rw [play_ne _ _ _ _ (by decide)]
      exact he
    exact hne2
  · rw [show (2 : Fin 4) = ⟨2, by decide⟩ from rfl]
    rfl
  · rw [show (3 : Fin 4) = ⟨3, by decide⟩ from rfl]
    rfl

/-! ## M3 (part 3): PD0 safety core — exception cell (0,2), paper section 5.2 -/

theorem hsup0_play {b : Board 4} {c : Fin 4}
    (hsup0 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
      stone (b d) (i - 1) = some .black ∨ (d = ⟨0, by decide⟩ ∧ i = 2))
    (hc0w : c = ⟨0, by decide⟩ → TopBlack (b ⟨0, by decide⟩) ∨
      (b ⟨0, by decide⟩) = [Player.black, Player.white])
    (htopc : c ≠ ⟨0, by decide⟩ → TopBlack (b c)) :
    ∀ d : Fin 4, ∀ i, stone (play b c .white d) i = some .white → 1 ≤ i →
      stone (play b c .white d) (i - 1) = some .black ∨ (d = ⟨0, by decide⟩ ∧ i = 2) := by
  intro d i hw2 hi
  by_cases hdc : d = c
  · rw [hdc] at hw2
    rw [play_eq] at hw2
    rw [hdc, play_eq]
    by_cases hlen0 : (b c).length = 0
    · -- fresh stone is the only stone; no white at i >= 1
      have hbb : i < (b c).length + 1 := by
        have := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
        simp only [List.length_append, List.length_singleton] at this
        omega
      omega
    · by_cases hwait : c = ⟨0, by decide⟩ ∧ (b c).length = 2
      · -- waiting shape: fresh stone lands exactly at the exception cell
        have hbb : i < (b c).length + 1 := by
          have := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
          simp only [List.length_append, List.length_singleton] at this
          omega
        rcases Nat.lt_or_ge i (b c).length with hilt | hge
        · have hltm : i - 1 < (b c).length := by omega
          rw [stone_append, if_pos hltm]
          have hw2' : stone (b c) i = some .white := by
            rw [stone_append, if_pos hilt] at hw2
            exact hw2
          rcases hsup0 c i hw2' hi with hsup | hex
          · exact Or.inl hsup
          · exact Or.inr hex
        · have hi2 : i = 2 := by omega
          exact Or.inr ⟨hwait.1, hi2⟩
      · have hpos : 1 ≤ (b c).length := by omega
        have hbtop : stone (b c) ((b c).length - 1) = some .black := by
          by_cases hc0 : c = ⟨0, by decide⟩
          · have hne : ¬((b c) = [Player.black, Player.white]) := by
              intro heq
              have h2 : (b c).length = 2 := by rw [heq]; rfl
              exact hwait ⟨hc0, h2⟩
            rcases hc0w hc0 with hb | hlist
            · rcases hb with h0 | h2
              · rw [← hc0] at h0
                exact absurd h0 (by omega)
              · rw [hc0]
                exact h2
            · rw [hc0] at hne
              exact absurd hlist hne
          · rcases htopc hc0 with h0 | h2
            · exact absurd h0 (by omega)
            · exact h2
        have hbb : i < (b c).length + 1 := by
          have hsb := stone_bound ((b c) ++ [Player.white]) i Player.white hw2
          simp only [List.length_append, List.length_singleton] at hsb
          omega
        rcases Nat.lt_or_ge i (b c).length with hilt | hge
        · have hw2' : stone (b c) i = some .white := by
            rw [stone_append, if_pos hilt] at hw2
            exact hw2
          rcases hsup0 c i hw2' hi with hsup | hex
          · refine Or.inl ?_
            rw [stone_append, if_pos (by omega : i - 1 < (b c).length)]
            exact hsup
          · exact Or.inr hex
        · have hie : i = (b c).length := by omega
          rw [hie]
          refine Or.inl ?_
          rw [stone_append, if_pos (by omega : (b c).length - 1 < (b c).length)]
          exact hbtop
  · rw [play_ne b c d .white hdc] at hw2
    rw [play_ne b c d .white hdc]
    exact hsup0 d i hw2 hi

theorem noWhiteFour_descent0 {h : Nat} {b : Board 4} {c : Fin 4}
    (hsup0 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
      stone (b d) (i - 1) = some .black ∨ (d = ⟨0, by decide⟩ ∧ i = 2))
    (hc0w : c = ⟨0, by decide⟩ → TopBlack (b ⟨0, by decide⟩) ∨
      (b ⟨0, by decide⟩) = [Player.black, Player.white])
    (htopc : c ≠ ⟨0, by decide⟩ → TopBlack (b c))
    (fb0 : stone (b ⟨0, by decide⟩) 0 = some .black)
    (fb30 : stone (b ⟨3, by decide⟩) 0 = some .black)
    (fb13 : stone (play b c .white ⟨1, by decide⟩) 3 ≠ some .white ∨
      stone (play b c .white ⟨2, by decide⟩) 4 ≠ some .white)
    (fb32 : stone (play b c .white ⟨3, by decide⟩) 2 ≠ some .white)
    (hnw : ¬ HasFour h b .white) (hnb : ¬ HasFour h b .black) :
    ¬ HasFour h (play b c .white) .white := by
  intro hw
  have hsup0' := hsup0_play hsup0 hc0w htopc
  rcases hw with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · -- vertical
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    obtain ⟨c0, hx0, hy0, _, t0⟩ := cellAtInt_some s0
    have s2 : cellAtInt h (play b c .white) x (y + 2) = some .white := by
      simpa using hd ⟨2, by decide⟩
    obtain ⟨c2, hx2, hy2, _, t2⟩ := cellAtInt_some s2
    have e2 : c2 = c0 := Fin.ext (by omega)
    rw [e2] at t2
    have i2 : (y + 2).toNat = y.toNat + 2 := by omega
    rw [i2] at t2
    have s1 : cellAtInt h (play b c .white) x (y + 1) = some .white := by
      simpa using hd ⟨1, by decide⟩
    obtain ⟨c1, hx1, hy1, _, t1⟩ := cellAtInt_some s1
    have e1 : c1 = c0 := Fin.ext (by omega)
    rw [e1] at t1
    have i1 : (y + 1).toNat = y.toNat + 1 := by omega
    rw [i1] at t1
    rcases hsup0' c0 (y.toNat + 2) t2 (by omega) with hsupp | hex
    · have hnorm : y.toNat + 2 - 1 = y.toNat + 1 := by omega
      rw [hnorm] at hsupp
      rw [hsupp] at t1
      exact absurd t1 (by decide)
    · have hy0z : y.toNat = 0 := by omega
      rw [hex.1, hy0z] at t0
      have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      rw [stone_old_play b c .white ⟨0, by decide⟩ 0 hb0len, fb0] at t0
      exact absurd t0 (by decide)
  · -- horizontal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) y = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) y.toNat = some .white := by
      intro j
      have hz : y + (j.val : Int) * 0 = y := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [hz] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hn0 : y.toNat = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hn0] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · have hy1 : 1 ≤ y.toNat := by omega
      by_cases hmn : (b c).length = y.toNat
      · have hshift : ∀ j : Fin 4, stone (b j) (y.toNat - 1) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              by_cases hc0c : c = ⟨0, by decide⟩
              · rw [hc0c] at hmn ⊢
                rcases hc0w hc0c with hb | hlist
                · rcases hb with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
                · have h2l : (b ⟨0, by decide⟩).length = 2 := by rw [hlist]; rfl
                  have hk3 := key ⟨3, by decide⟩
                  have hn2 : y.toNat = 2 := by omega
                  rw [hn2] at hk3
                  exact absurd hk3 fb32
              · rcases htopc hc0c with h0 | hb'
                · exact absurd h0 (by omega)
                · exact hb'
            rw [← hcj, ← hmn]
            exact htop'
          · have hold : stone (b j) y.toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : y.toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            rcases hsup0 j y.toNat hold (by omega) with hsup | hex
            · exact hsup
            · have hk3 := key ⟨3, by decide⟩
              rw [hex.2] at hk3
              exact absurd hk3 fb32
        refine hnb (Or.inr (Or.inl ⟨0, ((y.toNat - 1 : Int)), ?_⟩))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show ((y.toNat - 1 : Int)) + (i.val : Int) * 0 = (y.toNat - 1 : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y.toNat - 1 : Int)) (by omega : ((y.toNat - 1 : Int)) < (h : Int))]
        rw [show ((y.toNat - 1 : Int)).toNat = y.toNat - 1 from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inl ⟨0, y, ?_⟩))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show y + (i.val : Int) * 0 = y from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega) hy0 hyh0]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : y.toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : y.toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound
  · -- rising diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y + 3) = some .white := by
      simpa using hd ⟨3, by decide⟩
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int)).toNat = some .white := by
      intro j
      have h1 : y + (j.val : Int) * 1 = y + (j.val : Int) := by omega
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [h1] at hc
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy0c : y = 0
    · have hb0len : 0 < (b ⟨0, by decide⟩).length := stone_bound _ 0 _ fb0
      have hb0b1 : stone (play b c .white ⟨0, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb0len]
        exact fb0
      have hk0 := key ⟨0, by decide⟩
      rw [hy0c, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hk0
      simp only [Int.mul_one, Int.add_zero, Int.toNat_zero] at hk0
      rw [hb0b1] at hk0
      exact absurd hk0 (by decide)
    · have hy1 : (1:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y + (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y + (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              by_cases hc0c : c = ⟨0, by decide⟩
              · rw [hc0c, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hmn
                rw [hc0c]
                rcases hc0w hc0c with hb | hlist
                · rcases hb with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
                · have h2l : (b ⟨0, by decide⟩).length = 2 := by rw [hlist]; rfl
                  have hk1 := key ⟨1, by decide⟩
                  rw [show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hk1
                  have hn13 : (y + (1 : Int)).toNat = 3 := by omega
                  rw [hn13] at hk1
                  rcases fb13 with h13 | h24
                  · exact absurd hk1 h13
                  · have hk2 := key ⟨2, by decide⟩
                    rw [show ((⟨2, by decide⟩ : Fin 4) : Int) = 2 from rfl] at hk2
                    have hn24 : (y + (2 : Int)).toNat = 4 := by omega
                    rw [hn24] at hk2
                    exact absurd hk2 h24
              · rcases htopc hc0c with h0 | hb'
                · exact absurd h0 (by omega)
                · exact hb'
            rw [← hcj]
            have hrow : (y + (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y + (j.val : Int) := by omega
            rw [show (y + (j.val : Int) - 1).toNat = (y + (j.val : Int)).toNat - 1 from by omega]
            rcases hsup0 j (y + (j.val : Int)).toNat hold (by omega) with hsup | hex
            · exact hsup
            · have hex2 : (y + (j.val : Int)).toNat = 2 := hex.2
              rw [hex.1, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hex2
              simp only [Int.add_zero] at hex2
              have hk1 := key ⟨1, by decide⟩
              rw [show ((⟨1, by decide⟩ : Fin 4) : Int) = 1 from rfl] at hk1
              have hn13 : (y + (1 : Int)).toNat = 3 := by omega
              rw [hn13] at hk1
              rcases fb13 with h13 | h24
              · exact absurd hk1 h13
              · have hk2 := key ⟨2, by decide⟩
                rw [show ((⟨2, by decide⟩ : Fin 4) : Int) = 2 from rfl] at hk2
                have hn24 : (y + (2 : Int)).toNat = 4 := by omega
                rw [hn24] at hk2
                exact absurd hk2 h24
        refine hnb (Or.inr (Or.inr (Or.inl ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * 1 = y - 1 + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 + (i.val : Int))) (by omega : (y - 1 + (i.val : Int)) < (h : Int))]
        rw [show (y - 1 + (i.val : Int)).toNat = (y + (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inl ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show y + (i.val : Int) * 1 = y + (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega) (by omega)
          (by omega : y + (i.val : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound
  · -- falling diagonal
    have s0 : cellAtInt h (play b c .white) x y = some .white := by
      simpa using hd ⟨0, by decide⟩
    have s3 : cellAtInt h (play b c .white) (x + 3) (y - 3) = some .white := by
      have h3 := hd ⟨3, by decide⟩
      rw [show ((⟨3, by decide⟩ : Fin 4) : Int) = 3 from rfl] at h3
      have hbr : y + 3 * (-1 : Int) = y - 3 := by omega
      rw [hbr] at h3
      exact h3
    obtain ⟨c0, hx0, hy0, hyh0, t0⟩ := cellAtInt_some s0
    obtain ⟨c3, hx3, _, hyh3, _⟩ := cellAtInt_some s3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx0v : x = 0 := by omega
    have key : ∀ j : Fin 4, stone (play b c .white j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
      intro j
      have hc := white_line_cell hd hx0v j.val j.isLt
      rw [show j = ⟨j.val, j.isLt⟩ from Fin.ext rfl]
      exact hc
    by_cases hy3 : y - 3 = 0
    · have hb3len : 0 < (b ⟨3, by decide⟩).length := stone_bound _ 0 _ fb30
      have hb3c : stone (play b c .white ⟨3, by decide⟩) 0 = some .black := by
        rw [stone_old_play _ _ _ _ _ hb3len]
        exact fb30
      have hk3 := key ⟨3, by decide⟩
      rw [show ((⟨3, by decide⟩ : Fin 4) : Int) = 3 from rfl] at hk3
      have hn3 : (y + (3 : Int) * (-1 : Int)).toNat = 0 := by omega
      rw [hn3] at hk3
      rw [hb3c] at hk3
      exact absurd hk3 (by decide)
    · have hy4 : (4:Int) ≤ y := by omega
      by_cases hmn : (b c).length = (y - (c.val : Int)).toNat
      · have hshift : ∀ j : Fin 4, stone (b j) ((y - (j.val : Int) - 1).toNat) = some .black := by
          intro j
          by_cases hcj : c = j
          · have htop' : stone (b c) ((b c).length - 1) = some .black := by
              by_cases hc0c : c = ⟨0, by decide⟩
              · rw [hc0c, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hmn
                rw [hc0c]
                rcases hc0w hc0c with hb | hlist
                · rcases hb with h0 | hb'
                  · exact absurd h0 (by omega)
                  · exact hb'
                · have h2l : (b ⟨0, by decide⟩).length = 2 := by rw [hlist]; rfl
                  omega
              · rcases htopc hc0c with h0 | hb'
                · exact absurd h0 (by omega)
                · exact hb'
            rw [← hcj]
            have hrow : (y - (c.val : Int) - 1).toNat = (b c).length - 1 := by omega
            rw [hrow]
            exact htop'
          · have hold : stone (b j) (y + (j.val : Int) * (-1 : Int)).toNat = some .white := by
              have hk := key j
              rw [stone_old_play _ _ _ _ _ ?_] at hk
              · exact hk
              · have hlen : (play b c .white j).length = (b j).length := by
                  rw [play_ne b c j .white (fun e => hcj e.symm)]
                have hkbound : (y + (j.val : Int) * (-1 : Int)).toNat < (play b c .white j).length :=
                  stone_bound _ _ _ hk
                rw [hlen] at hkbound
                exact hkbound
            have hpos : 0 ≤ y - (j.val : Int) := by omega
            rw [show (y - (j.val : Int) - 1).toNat = (y + (j.val : Int) * (-1 : Int)).toNat - 1 from by omega]
            rcases hsup0 j (y + (j.val : Int) * (-1 : Int)).toNat hold (by omega) with hsup | hex
            · exact hsup
            · have hex2 : (y + (j.val : Int) * (-1 : Int)).toNat = 2 := hex.2
              rw [hex.1, show ((⟨0, by decide⟩ : Fin 4) : Int) = 0 from rfl] at hex2
              omega
        refine hnb (Or.inr (Or.inr (Or.inr ⟨0, ((y - 1 : Int)), ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega,
            show (y - 1) + (i.val : Int) * (-1 : Int) = y - 1 - (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ (y - 1 - (i.val : Int))) (by omega : (y - 1 - (i.val : Int)) < (h : Int))]
        rw [show (y - 1 - (i.val : Int)).toNat = (y - (i.val : Int) - 1).toNat from by omega]
        exact hshift i
      · refine hnw (Or.inr (Or.inr (Or.inr ⟨0, y, ?_⟩)))
        intro i
        rw [show (0:Int) + (i.val : Int) * 1 = (i.val : Int) from by omega]
        rw [cellAtInt_mk i rfl (by omega) (by omega)
          (by omega : (0:Int) ≤ y + (i.val : Int) * (-1 : Int))
          (by omega : y + (i.val : Int) * (-1 : Int) < (h : Int))]
        have hk := key i
        rw [stone_old_play _ _ _ _ _ ?_] at hk
        · exact hk
        · by_cases he : i = c
          · subst he
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b i .white i).length := stone_bound _ _ _ hk
            have hlen2 : (play b i .white i).length = (b i).length + 1 := by
              simp [play, Function.update, List.length_append]
            omega
          · have hlen : (play b c .white i).length = (b i).length := by
              rw [play_ne b c i .white he]
            have hkbound : (y + (i.val : Int) * (-1 : Int)).toNat < (play b c .white i).length := stone_bound _ _ _ hk
            rw [hlen] at hkbound
            exact hkbound

/-! ## M3 (part 3b): machine A (waiting phase) for paper 5.2 — even columns 0/1/2,
odd-or-full column 3, cover always legal, white can only fill column 3. -/

structure PD0A (h : Nat) (b : Board 4) : Prop where
  hv : Valid h b
  htm : toMove b = .white
  hsup0 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (d = ⟨0, by decide⟩ ∧ i = 2)
  h0pat : TopBlack (b ⟨0, by decide⟩) ∨ (b ⟨0, by decide⟩) = [Player.black, Player.white]
  htop0 : ∀ d : Fin 4, d ≠ ⟨0, by decide⟩ → Legal h b d → TopBlack (b d)
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fb30 : stone (b ⟨3, by decide⟩) 0 = some .black
  fb32 : stone (b ⟨3, by decide⟩) 2 ≠ some .white
  hc0 : (b ⟨0, by decide⟩).length % 2 = 0
  hc1 : (b ⟨1, by decide⟩).length % 2 = 0
  hc2 : (b ⟨2, by decide⟩).length % 2 = 0
  hc3 : (b ⟨3, by decide⟩).length % 2 = 1 ∨ h ≤ (b ⟨3, by decide⟩).length
  fb13 : stone (b ⟨1, by decide⟩) 3 ≠ some .white
  hnw : ¬ HasFour h b .white

structure W0A (h : Nat) (b : Board 4) (c : Fin 4) : Prop where
  hv : Valid h b
  htm : toMove b = .black
  hsup0 : ∀ d : Fin 4, ∀ i, stone (b d) i = some .white → 1 ≤ i →
    stone (b d) (i - 1) = some .black ∨ (d = ⟨0, by decide⟩ ∧ i = 2)
  h0tf : TopBlack (b ⟨0, by decide⟩) ∨ (b ⟨0, by decide⟩) = [Player.black, Player.white] ∨
    c = ⟨0, by decide⟩
  htopO : ∀ d : Fin 4, d ≠ c → Legal h b d → d ≠ ⟨0, by decide⟩ → TopBlack (b d)
  fb0 : stone (b ⟨0, by decide⟩) 0 = some .black
  fb30 : stone (b ⟨3, by decide⟩) 0 = some .black
  fb32 : stone (b ⟨3, by decide⟩) 2 ≠ some .white
  hc0W : c ≠ ⟨0, by decide⟩ → (b ⟨0, by decide⟩).length % 2 = 0
  hc0o : c = ⟨0, by decide⟩ → (b ⟨0, by decide⟩).length % 2 = 1
  hc1W : c ≠ ⟨1, by decide⟩ → (b ⟨1, by decide⟩).length % 2 = 0
  hc1o : c = ⟨1, by decide⟩ → (b ⟨1, by decide⟩).length % 2 = 1
  hc2W : c ≠ ⟨2, by decide⟩ → (b ⟨2, by decide⟩).length % 2 = 0
  hc2o : c = ⟨2, by decide⟩ → (b ⟨2, by decide⟩).length % 2 = 1
  hc3W : c ≠ ⟨3, by decide⟩ → ((b ⟨3, by decide⟩).length % 2 = 1 ∨ h ≤ (b ⟨3, by decide⟩).length)
  hc3o : c = ⟨3, by decide⟩ → (b ⟨3, by decide⟩).length % 2 = 0
  fb13 : stone (b ⟨1, by decide⟩) 3 ≠ some .white
  hnw : ¬ HasFour h b .white

theorem pd0a_to_w0a {h : Nat} {b : Board 4} {c : Fin 4} (hp : PD0A h b)
    (hc : Legal h b c) (hnb : ¬ HasFour h b .black) : W0A h (play b c .white) c := by
  have hc0w : c = ⟨0, by decide⟩ → TopBlack (b ⟨0, by decide⟩) ∨
      (b ⟨0, by decide⟩) = [Player.black, Player.white] := fun _ => hp.h0pat
  have htopc : c ≠ ⟨0, by decide⟩ → TopBlack (b c) := fun hne => hp.htop0 c hne hc
  have fb13new : stone (play b c .white ⟨1, by decide⟩) 3 ≠ some .white ∨
      stone (play b c .white ⟨2, by decide⟩) 4 ≠ some .white := by
    left
    by_cases hc1 : c = ⟨1, by decide⟩
    · rw [hc1, play_eq]
      have hpar := hp.hc1
      by_cases h3lt : 3 < (b ⟨1, by decide⟩).length
      · rw [stone_append, if_pos h3lt]
        exact hp.fb13
      · rw [stone_append, if_neg (by omega), if_neg (by omega)]
        simp
    · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
      exact hp.fb13
  have fb32new : stone (play b c .white ⟨3, by decide⟩) 2 ≠ some .white := by
    by_cases hc3c : c = ⟨3, by decide⟩
    · rw [hc3c, play_eq]
      rcases hp.hc3 with hpar | hfull
      · by_cases h2lt : 2 < (b ⟨3, by decide⟩).length
        · rw [stone_append, if_pos h2lt]
          exact hp.fb32
        · rw [stone_append, if_neg (by omega), if_neg (by omega)]
          simp
      · exfalso
        unfold Legal at hc
        have hlen3 : (b c).length = (b ⟨3, by decide⟩).length :=
          congrArg (fun l => l.length) (congrArg b hc3c)
        omega
    · rw [play_ne b c ⟨3, by decide⟩ .white (fun e => hc3c e.symm)]
      exact hp.fb32
  refine ⟨play_valid hp.hv hc, ?_, hsup0_play hp.hsup0 hc0w htopc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_,
    noWhiteFour_descent0 hp.hsup0 hc0w htopc hp.fb0 hp.fb30 fb13new fb32new hp.hnw hnb⟩
  · rw [toMove_play', hp.htm]
    rfl
  · by_cases hc0c : c = ⟨0, by decide⟩
    · exact Or.inr (Or.inr hc0c)
    · rw [play_ne b c ⟨0, by decide⟩ .white (fun e => hc0c e.symm)]
      rcases hp.h0pat with htb | hbw
      · exact Or.inl htb
      · exact Or.inr (Or.inl hbw)
  · intro d hdd hdl hd0
    rw [play_ne b c d .white hdd]
    refine hp.htop0 d hd0 ?_
    unfold Legal at hdl
    unfold Legal
    have hlen : (play b c .white d).length = (b d).length := by
      rw [play_ne b c d .white hdd]
    omega
  · rw [stone_old_play b c .white ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hp.fb0
      omega)]
    exact hp.fb0
  · rw [stone_old_play b c .white ⟨3, by decide⟩ 0 (by
      have := stone_bound (b ⟨3, by decide⟩) 0 Player.black hp.fb30
      omega)]
    exact hp.fb30
  · exact fb32new
  · intro hc0c
    rw [play_ne b c ⟨0, by decide⟩ .white (fun e => hc0c e.symm)]
    exact hp.hc0
  · intro hc0c
    rw [hc0c, play_eq]
    simp only [List.length_append, List.length_singleton]
    have hpar := hp.hc0
    omega
  · intro hc1c
    rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1c e.symm)]
    exact hp.hc1
  · intro hc1c
    rw [hc1c, play_eq]
    simp only [List.length_append, List.length_singleton]
    have hpar := hp.hc1
    omega
  · intro hc2c
    rw [play_ne b c ⟨2, by decide⟩ .white (fun e => hc2c e.symm)]
    exact hp.hc2
  · intro hc2c
    rw [hc2c, play_eq]
    simp only [List.length_append, List.length_singleton]
    have hpar := hp.hc2
    omega
  · intro hc3c
    rcases hp.hc3 with hpar | hfull
    · rw [play_ne b c ⟨3, by decide⟩ .white (fun e => hc3c e.symm)]
      exact Or.inl hpar
    · rw [play_ne b c ⟨3, by decide⟩ .white (fun e => hc3c e.symm)]
      exact Or.inr hfull
  · intro hc3c
    have hpar : (b c).length % 2 = 1 ∨ h ≤ (b c).length := by
      rcases hp.hc3 with hpar | hfull
      · exact Or.inl (by rw [hc3c]; exact hpar)
      · exact Or.inr (by rw [hc3c]; exact hfull)
    have hlen : (play b c .white ⟨3, by decide⟩).length = (b c).length + 1 := by
      rw [hc3c, play_eq]
      simp only [List.length_append, List.length_singleton]
    rw [hlen]
    rcases hpar with hpar | hfull
    · omega
    · exfalso
      unfold Legal at hc
      omega
  · by_cases hc1 : c = ⟨1, by decide⟩
    · have hfb13c : stone (b c) 3 ≠ some .white := by rw [hc1]; exact hp.fb13
      have hparc : (b c).length % 2 = 0 := by rw [hc1]; exact hp.hc1
      have hcol : play b c .white ⟨1, by decide⟩ = (b c) ++ [Player.white] := by
        rw [hc1, play_eq]
      rw [hcol]
      by_cases h3lt : 3 < (b c).length
      · rw [stone_append, if_pos h3lt]
        exact hfb13c
      · rw [stone_append, if_neg (by omega), if_neg (by omega)]
        simp
    · rw [play_ne b c ⟨1, by decide⟩ .white (fun e => hc1 e.symm)]
      exact hp.fb13

/-! ## M3 (part 3c): machine A black reply (cover always legal in the waiting phase) -/

theorem w0a_reply {h : Nat} {b : Board 4} {c : Fin 4} (hw : W0A h b c)
    (hcov : Legal h b c) : PD0A h (play b c .black) := by
  refine ⟨play_valid hw.hv hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hasFour_play_other (by decide) hw.hnw⟩
  · rw [toMove_play', hw.htm]
    rfl
  · intro d i hw2 hi
    by_cases hde : d = c
    · rw [hde, play_eq] at hw2
      rw [hde, play_eq]
      have hbb : i < (b c).length + 1 := by
        have hsb := stone_bound ((b c) ++ [Player.black]) i Player.white hw2
        simp only [List.length_append, List.length_singleton] at hsb
        omega
      by_cases hie : i = (b c).length
      · rw [hie] at hw2
        rw [stone_append, if_neg (by omega), if_pos rfl] at hw2
        exact absurd hw2 (by decide)
      have hw2' : stone (b c) i = some .white := by
        rw [stone_append, if_pos (by omega : i < (b c).length)] at hw2
        exact hw2
      rcases hw.hsup0 c i hw2' hi with hsup | hex
      · refine Or.inl ?_
        rw [stone_append, if_pos (by omega : i - 1 < (b c).length)]
        exact hsup
      · exact Or.inr hex
    · rw [play_ne b c d .black hde] at hw2
      rw [play_ne b c d .black hde]
      exact hw.hsup0 d i hw2 hi
  · by_cases hc0c : c = ⟨0, by decide⟩
    · rw [show play b c .black ⟨0, by decide⟩ = (b c) ++ [Player.black] from by
        rw [show c = ⟨0, by decide⟩ from hc0c, play_eq]]
      exact Or.inl (topBlack_append_black _)
    · rw [play_ne b c ⟨0, by decide⟩ .black (fun e => hc0c e.symm)]
      rcases hw.h0tf with htb | hbw | hcc
      · exact Or.inl htb
      · exact Or.inr hbw
      · exact absurd hcc hc0c
  · intro d hd0 hl
    by_cases hde : d = c
    · rw [hde, play_eq]
      exact topBlack_append_black _
    · rw [play_ne b c d .black hde]
      have hd0' : Legal h b d := by
        unfold Legal at hl
        unfold Legal
        have hlen : (play b c .black d).length = (b d).length := by
          rw [play_ne b c d .black hde]
        omega
      exact hw.htopO d hde hd0' hd0
  · rw [stone_old_play b c .black ⟨0, by decide⟩ 0 (by
      have := stone_bound (b ⟨0, by decide⟩) 0 Player.black hw.fb0
      omega)]
    exact hw.fb0
  · rw [stone_old_play b c .black ⟨3, by decide⟩ 0 (by
      have := stone_bound (b ⟨3, by decide⟩) 0 Player.black hw.fb30
      omega)]
    exact hw.fb30
  · by_cases hc3c : c = ⟨3, by decide⟩
    · have hcol : play b c .black ⟨3, by decide⟩ = (b c) ++ [Player.black] := by
        rw [show c = ⟨3, by decide⟩ from hc3c, play_eq]
      rw [hcol, stone_append]
      have hfb32c : stone (b c) 2 ≠ some .white := by
        rw [show c = ⟨3, by decide⟩ from hc3c]
        exact hw.fb32
      by_cases h2lt : 2 < (b c).length
      · rw [if_pos h2lt]
        exact hfb32c
      · rw [if_neg h2lt]
        by_cases h2e : 2 = (b c).length
        · rw [if_pos h2e]
          exact (by decide : some Player.black ≠ some Player.white)
        · rw [if_neg h2e]
          simp
    · rw [play_ne b c ⟨3, by decide⟩ .black (fun e => hc3c e.symm)]
      exact hw.fb32
  · by_cases hc0c : c = ⟨0, by decide⟩
    · have hpar : (b c).length % 2 = 1 := by
        rw [show c = ⟨0, by decide⟩ from hc0c]
        exact hw.hc0o hc0c
      have hlen : (play b c .black ⟨0, by decide⟩).length = (b c).length + 1 := by
        rw [show c = ⟨0, by decide⟩ from hc0c, play_eq]
        simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega
    · rw [play_ne b c ⟨0, by decide⟩ .black (fun e => hc0c e.symm)]
      exact hw.hc0W hc0c
  · by_cases hc1c : c = ⟨1, by decide⟩
    · have hpar : (b c).length % 2 = 1 := by
        rw [show c = ⟨1, by decide⟩ from hc1c]
        exact hw.hc1o hc1c
      have hlen : (play b c .black ⟨1, by decide⟩).length = (b c).length + 1 := by
        rw [show c = ⟨1, by decide⟩ from hc1c, play_eq]
        simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega
    · rw [play_ne b c ⟨1, by decide⟩ .black (fun e => hc1c e.symm)]
      exact hw.hc1W hc1c
  · by_cases hc2c : c = ⟨2, by decide⟩
    · have hpar : (b c).length % 2 = 1 := by
        rw [show c = ⟨2, by decide⟩ from hc2c]
        exact hw.hc2o hc2c
      have hlen : (play b c .black ⟨2, by decide⟩).length = (b c).length + 1 := by
        rw [show c = ⟨2, by decide⟩ from hc2c, play_eq]
        simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega
    · rw [play_ne b c ⟨2, by decide⟩ .black (fun e => hc2c e.symm)]
      exact hw.hc2W hc2c
  · by_cases hc3c : c = ⟨3, by decide⟩
    · have hpar : (b c).length % 2 = 0 := by
        rw [show c = ⟨3, by decide⟩ from hc3c]
        exact hw.hc3o hc3c
      have hlen : (play b c .black ⟨3, by decide⟩).length = (b c).length + 1 := by
        rw [show c = ⟨3, by decide⟩ from hc3c, play_eq]
        simp only [List.length_append, List.length_singleton]
      rw [hlen]
      exact Or.inl (by omega)
    · rw [play_ne b c ⟨3, by decide⟩ .black (fun e => hc3c e.symm)]
      exact hw.hc3W hc3c
  · by_cases hc1c : c = ⟨1, by decide⟩
    · have hcol : play b c .black ⟨1, by decide⟩ = (b c) ++ [Player.black] := by
        rw [show c = ⟨1, by decide⟩ from hc1c, play_eq]
      rw [hcol, stone_append]
      have hfb13c : stone (b c) 3 ≠ some .white := by
        rw [show c = ⟨1, by decide⟩ from hc1c]
        exact hw.fb13
      by_cases h3lt : 3 < (b c).length
      · rw [if_pos h3lt]
        exact hfb13c
      · rw [if_neg h3lt]
        by_cases h3e : 3 = (b c).length
        · rw [if_pos h3e]
          exact (by decide : some Player.black ≠ some Player.white)
        · rw [if_neg h3e]
          simp
    · rw [play_ne b c ⟨1, by decide⟩ .black (fun e => hc1c e.symm)]
      exact hw.fb13

/-- Public interface to the completed support-descent strategy. -/
theorem pd_state_safe {h : Nat} {b : Board 4} (hp : PDstate h b) :
    CanAvoidLoss h .black b := fun k => (pd_pairing_aux h k).1 b hp

/-- Public interface to the completed exceptional-cell strategy for column 1. -/
theorem pd1_state_safe {h : Nat} {b : Board 4} (hh : h % 2 = 0) (h4 : 4 ≤ h)
    (hp : PD1 h b) : CanAvoidLoss h .black b :=
  fun k => (pd1_pairing_aux h hh h4 k).1 b hp

end Connect4.FourColumns
