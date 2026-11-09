import Connect4Proof.Basic

/-!
# Gravity Connect Four on one, two, or three columns

Standalone experiment for the uploaded Connect4Proof project.
Save OUTSIDE Connect4Proof/, for example experiments/NarrowBoards.lean.
Run from the project root: lake env lean experiments/NarrowBoards.lean

STATUS: source supplied for local compilation; not compiled by the author here.
No finite board enumeration, new axioms, admitted proofs, or native evaluation.

The original Basic.lean fixes width = 7 and height = 6. Consequently its Board
and WinningWithin cannot state this theorem. This namespace generalizes the
board dimensions and defines an explicit, one-ply, fixed-player safety game.
Player and opponent are REUSED from Basic.lean.

Semantic correspondence with Basic.lean:
  Board w             <-> Board: bottom-first lists, one list per column
  Legal h             <-> Legal: length < height
  play                <-> play: Function.update and append [player]
  stone / cellAtInt h <-> cellAt / cellAtInt: bounded bottom-up cell lookup
  HasFourDir h        <-> HasFourDir: SAME integer coordinates and directions
  HasFour h           <-> HasFour: vertical, horizontal, both diagonals
  totalStones/toMove  <-> totalStones/toMove: Black on even parity
  BoardFull h/Valid h <-> BoardFull/Valid: every column full / no overflow

SafeFor h p k b means p can prevent the opponent winning through k MORE PLIES.
At p's turn it requires a legal choice; at the opponent's turn it covers EVERY
legal choice. A previous opponent win is always rejected, even on a full board.
An own win or a full board ends play. The zero horizon only asserts current
safety; CanAvoidLoss quantifies over ALL horizons, not just horizon zero.
Legal moves decrease remaining, so horizon w*h already covers every actual
game from empty. Both players' CanAvoidLoss is our definition of IsDraw.

Invariant: the opponent has no vertically adjacent pair; additionally, every
nonfull column has a top stone different from the opponent (or is empty).
After an opponent move only its column can need repair. Cover it if legal;
if full, no repair is needed. Any legal move by the defender then suffices.

The geometry is NOT replaced by a vertical-only win condition: the original
four directions remain in HasFour; hasFour_false_of_noPairs proves the reduction.
-/

namespace Connect4.NarrowBoards

abbrev Board (w : Nat) := Fin w → List Player

variable {w h : Nat} {b : Board w} {c : Fin w} {p q : Player}
  {l : List Player} {r : Nat} {x y dy : Int}

def emptyBoard (w : Nat) : Board w := fun _ => []

def Legal (h : Nat) (b : Board w) (c : Fin w) : Prop := (b c).length < h
def Valid (h : Nat) (b : Board w) : Prop := ∀ c, (b c).length ≤ h
def BoardFull (h : Nat) (b : Board w) : Prop := ∀ c, (b c).length = h

def play (b : Board w) (c : Fin w) (p : Player) : Board w :=
  Function.update b c (b c ++ [p])

/-- Elementary list lookup, avoiding dependence on version-specific get? lemmas. -/
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
      | succ r =>
          exact ih r (by simpa using hr)

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
  | nil =>
      cases r <;> simp [stone]
  | cons a l ih =>
      cases r with
      | zero => simp [stone]
      | succ r => simpa [stone] using ih r

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

/-- No vertically adjacent stones of the specified player anywhere in this list. -/
def NoPair (p : Player) (l : List Player) : Prop :=
  ∀ r, stone l r = some p → stone l (r + 1) ≠ some p

def NoPairs (p : Player) (b : Board w) : Prop := ∀ c, NoPair p (b c)

theorem no_direction_one (hw : w ≤ 3)
    (hd : HasFourDir h b p x y 1 dy) : False := by
  have h0 : cellAtInt h b x y = some p := by
    simpa using hd (⟨0, by decide⟩ : Fin 4)
  have h3 := hd (⟨3, by decide⟩ : Fin 4)
  have h3' : cellAtInt h b (x + 3) (y + 3 * dy) = some p := by
    simpa using h3
  obtain ⟨c0, hx0, _, _, _⟩ := cellAtInt_some h0
  obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some h3'
  have hc0 := c0.isLt
  have hc3 := c3.isLt
  omega

theorem hasFour_false_of_noPairs (hw : w ≤ 3) (hn : NoPairs p b) :
    ¬ HasFour h b p := by
  intro hf
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · have h0 : cellAtInt h b x y = some p := by
      simpa using hd (⟨0, by decide⟩ : Fin 4)
    have h1 : cellAtInt h b x (y + 1) = some p := by
      simpa using hd (⟨1, by decide⟩ : Fin 4)
    obtain ⟨c0, hx0, hy0, _, hs0⟩ := cellAtInt_some h0
    obtain ⟨c1, hx1, _, _, hs1⟩ := cellAtInt_some h1
    have hc : c1 = c0 := by
      apply Fin.ext
      omega
    have hy : (y + 1).toNat = y.toNat + 1 := by omega
    rw [hc, hy] at hs1
    exact hn c0 y.toNat hs0 hs1
  · exact no_direction_one hw hd
  · exact no_direction_one hw hd
  · exact no_direction_one hw hd

theorem stone_append_other (hpq : p ≠ q)
    (hs : stone (l ++ [p]) r = some q) : stone l r = some q := by
  by_cases hr : r < l.length
  · simpa [stone_append, hr] using hs
  · by_cases he : r = l.length
    · have hh : p = q := by simpa [stone_append, hr, he] using hs
      exact False.elim (hpq hh)
    · simp [stone_append, hr, he] at hs

theorem noPair_append_other (hpq : p ≠ q) (hn : NoPair q l) :
    NoPair q (l ++ [p]) := by
  intro r h0 h1
  exact hn r (stone_append_other hpq h0) (stone_append_other hpq h1)

theorem noPair_append_self (hn : NoPair q l)
    (ht : stone l (l.length - 1) ≠ some q) : NoPair q (l ++ [q]) := by
  intro r h0 h1
  have hb := stone_bound (l ++ [q]) (r + 1) q h1
  simp only [List.length_append, List.length_singleton] at hb
  have hr : r < l.length := by omega
  have h0' : stone l r = some q := by
    simpa [stone_append, hr] using h0
  by_cases hr1 : r + 1 < l.length
  · have h1' : stone l (r + 1) = some q := by
      simpa [stone_append, hr1] using h1
    exact hn r h0' h1'
  · have he : r = l.length - 1 := by
      omega
    exact ht (he ▸ h0')

def TopBlocked (q : Player) (l : List Player) : Prop :=
  stone l (l.length - 1) ≠ some q

def Protected (h : Nat) (q : Player) (b : Board w) : Prop :=
  NoPairs q b ∧ ∀ c, Legal h b c → TopBlocked q (b c)

/-- Only the named column may have an exposed opponent stone at its top. -/
def OpenAt (h : Nat) (q : Player) (b : Board w) (c : Fin w) : Prop :=
  NoPairs q b ∧ ∀ d, d ≠ c → Legal h b d → TopBlocked q (b d)

theorem topBlocked_append_other (hpq : p ≠ q) (l : List Player) :
    TopBlocked q (l ++ [p]) := by
  simp [TopBlocked, stone_append, hpq]

theorem play_eq (b : Board w) (c : Fin w) (p : Player) :
    play b c p c = b c ++ [p] := by simp [play]

theorem play_ne (b : Board w) (c d : Fin w) (p : Player) (hne : d ≠ c) :
    play b c p d = b d := by simp [play, Function.update, hne]

theorem protected_open (hb : Protected h q b) (c : Fin w) : OpenAt h q b c :=
  ⟨hb.1, fun d _ hd => hb.2 d hd⟩

theorem open_cover (hb : OpenAt h q b c) (hpq : p ≠ q) :
    Protected h q (play b c p) := by
  constructor
  · intro d
    by_cases he : d = c
    · subst d
      rw [play_eq]
      exact noPair_append_other hpq (hb.1 c)
    · rw [play_ne b c d p he]
      exact hb.1 d
  · intro d hd
    by_cases he : d = c
    · subst d
      rw [play_eq]
      exact topBlocked_append_other hpq (b c)
    · have hd' : Legal h b d := by
        simpa only [Legal, play_ne b c d p he] using hd
      rw [play_ne b c d p he]
      exact hb.2 d he hd'

theorem protected_play_other (hb : Protected h q b) (hpq : p ≠ q)
    (c : Fin w) : Protected h q (play b c p) :=
  open_cover (protected_open hb c) hpq

theorem protected_play_self (hb : Protected h q b) (hc : Legal h b c) :
    OpenAt h q (play b c q) c := by
  constructor
  · intro d
    by_cases he : d = c
    · subst d
      rw [play_eq]
      exact noPair_append_self (hb.1 c) (hb.2 c hc)
    · rw [play_ne b c d q he]
      exact hb.1 d
  · intro d he hd
    have hd' : Legal h b d := by
      simpa only [Legal, play_ne b c d q he] using hd
    rw [play_ne b c d q he]
    exact hb.2 d hd'

theorem open_closed (hb : OpenAt h q b c) (hc : ¬ Legal h b c) :
    Protected h q b := by
  refine ⟨hb.1, ?_⟩
  intro d hd
  by_cases he : d = c
  · subst d
    exact False.elim (hc hd)
  · exact hb.2 d he hd

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
def remaining (h : Nat) (b : Board w) : Nat := w * h - totalStones b

theorem totalStones_play (b : Board w) (c : Fin w) (p : Player) :
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

theorem toMove_play (b : Board w) (c : Fin w) (p : Player) :
    toMove (play b c p) = opponent (toMove b) := by
  unfold toMove
  rw [totalStones_play]
  by_cases he : totalStones b % 2 = 0
  · have ho : (totalStones b + 1) % 2 = 1 := by omega
    simp [he, ho, opponent]
  · have ho : (totalStones b + 1) % 2 = 0 := by omega
    simp [he, ho, opponent]

theorem valid_totalStones (hv : Valid h b) : totalStones b ≤ w * h := by
  calc
    totalStones b ≤ ∑ _c : Fin w, h := Finset.sum_le_sum (fun c _ => hv c)
    _ = w * h := by simp

theorem remaining_play_lt (hv : Valid h b) (hc : Legal h b c) :
    remaining h (play b c p) < remaining h b := by
  have hv' : Valid h (play b c p) := play_valid hv hc
  have hb := valid_totalStones hv'
  rw [totalStones_play] at hb
  unfold remaining
  rw [totalStones_play]
  omega

theorem remaining_zero_iff_full (hv : Valid h b) :
    remaining h b = 0 ↔ BoardFull h b := by
  constructor
  · intro hz
    by_contra hf
    obtain ⟨c, hc⟩ := exists_legal hv hf
    have hh := remaining_play_lt (p := Player.black) hv hc
    omega
  · intro hf
    have he : totalStones b = w * h := by
      unfold totalStones
      calc
        (∑ c, (b c).length) = ∑ _c : Fin w, h :=
          Finset.sum_congr rfl (fun c _ => hf c)
        _ = w * h := by simp
    simp [remaining, he]

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

/-- Both players have a strategy preventing the other player's win. -/
def IsDraw (h : Nat) (b : Board w) : Prop :=
  CanAvoidLoss h .black b ∧ CanAvoidLoss h .white b

theorem player_ne_opponent (p : Player) : p ≠ opponent p := by
  cases p <;> simp [opponent]

theorem eq_opponent_of_ne (a p : Player) (hne : a ≠ p) : a = opponent p := by
  cases a <;> cases p <;> simp_all [opponent]

/-- Fixed-player forced win in at most k further plies, with genuine terminal guards.
    The nonfull guard prevents the opponent's universal move condition being vacuous. -/
def WinFor (h : Nat) (p : Player) : Nat → Board w → Prop
  | 0, b => HasFour h b p ∧ ¬ HasFour h b (opponent p)
  | k + 1, b =>
      ¬ HasFour h b (opponent p) ∧
      (HasFour h b p ∨
        (¬ BoardFull h b ∧
          (if toMove b = p then
            ∃ c, Legal h b c ∧ WinFor h p k (play b c (toMove b))
          else
            ∀ c, Legal h b c → WinFor h p k (play b c (toMove b)))))

theorem safe_excludes_opponent_win (hs : SafeFor h p k b) :
    ¬ WinFor h (opponent p) k b := by
  induction k generalizing b with
  | zero =>
      intro hw
      exact hs hw.1
  | succ k ih =>
      intro hw
      rcases hw.2 with hwin | ⟨hnf, hwmove⟩
      · exact hs.1 hwin
      · rcases hs.2 with hwin | hfull | hsmove
        · exact hw.1 (by simpa only [opponent_involutive] using hwin)
        · exact hnf hfull
        · by_cases ht : toMove b = p
          · have hto : toMove b ≠ opponent p := by
              rw [ht]
              exact player_ne_opponent p
            rw [if_pos ht] at hsmove
            rw [if_neg hto] at hwmove
            obtain ⟨c, hc, hchild⟩ := hsmove
            exact ih (b := play b c (toMove b)) hchild (hwmove c hc)
          · have hto : toMove b = opponent p := eq_opponent_of_ne _ _ ht
            rw [if_neg ht] at hsmove
            rw [if_pos hto] at hwmove
            obtain ⟨c, hc, hchild⟩ := hwmove
            exact ih (b := play b c (toMove b)) (hsmove c hc) hchild

theorem draw_excludes_forced_wins (hd : IsDraw h b) :
    (¬ ∃ k, WinFor h Player.black k b) ∧
    (¬ ∃ k, WinFor h Player.white k b) := by
  constructor
  · rintro ⟨k, hk⟩
    exact safe_excludes_opponent_win (hd.2 k) hk
  · rintro ⟨k, hk⟩
    exact safe_excludes_opponent_win (hd.1 k) hk

/-- Induct simultaneously on protected states and states needing one repair. -/
theorem safety_induction (hw : w ≤ 3) (h : Nat) (p : Player) (k : Nat) :
    (∀ b : Board w, Valid h b → Protected h (opponent p) b → SafeFor h p k b) ∧
    (∀ (b : Board w) (c : Fin w), Valid h b →
      OpenAt h (opponent p) b c → toMove b = p → SafeFor h p k b) := by
  induction k with
  | zero =>
      constructor
      · intro b _ hb
        exact hasFour_false_of_noPairs hw hb.1
      · intro b c _ hb _
        exact hasFour_false_of_noPairs hw hb.1
  | succ k ih =>
      constructor
      · intro b hv hb
        refine ⟨hasFour_false_of_noPairs hw hb.1, Or.inr ?_⟩
        by_cases hf : BoardFull h b
        · exact Or.inl hf
        · apply Or.inr
          by_cases ht : toMove b = p
          · rw [if_pos ht]
            obtain ⟨c, hc⟩ := exists_legal hv hf
            refine ⟨c, hc, ?_⟩
            rw [ht]
            exact ih.1 _ (play_valid hv hc)
              (protected_play_other hb (player_ne_opponent p) c)
          · rw [if_neg ht]
            intro c hc
            have ht' : toMove b = opponent p := eq_opponent_of_ne _ _ ht
            apply ih.2 (play b c (toMove b)) c (play_valid hv hc)
            · rw [ht']
              exact protected_play_self hb hc
            · rw [toMove_play, ht', opponent_involutive]
      · intro b c hv hb ht
        refine ⟨hasFour_false_of_noPairs hw hb.1, Or.inr ?_⟩
        by_cases hf : BoardFull h b
        · exact Or.inl hf
        · apply Or.inr
          rw [if_pos ht]
          by_cases hc : Legal h b c
          · refine ⟨c, hc, ?_⟩
            rw [ht]
            exact ih.1 _ (play_valid hv hc) (open_cover hb (player_ne_opponent p))
          · have hb' := open_closed hb hc
            obtain ⟨d, hd⟩ := exists_legal hv hf
            refine ⟨d, hd, ?_⟩
            rw [ht]
            exact ih.1 _ (play_valid hv hd)
              (protected_play_other hb' (player_ne_opponent p) d)

theorem empty_valid (w h : Nat) : Valid h (emptyBoard w) := by
  intro c
  simp [emptyBoard]

theorem empty_protected (w h : Nat) (q : Player) : Protected h q (emptyBoard w) := by
  constructor
  · intro c r hr
    simp [emptyBoard, stone] at hr
  · intro c _
    simp [TopBlocked, emptyBoard, stone]

/-- The main theorem: every height, and any width at most three. -/
theorem narrow_empty_isDraw (w h : Nat) (hw : w ≤ 3) : IsDraw h (emptyBoard w) := by
  constructor
  · intro k
    exact (safety_induction hw h .black k).1 _
      (empty_valid w h) (empty_protected w h _)
  · intro k
    exact (safety_induction hw h .white k).1 _
      (empty_valid w h) (empty_protected w h _)

theorem one_column_draw (h : Nat) : IsDraw h (emptyBoard 1) :=
  narrow_empty_isDraw 1 h (by decide)

theorem two_columns_draw (h : Nat) : IsDraw h (emptyBoard 2) :=
  narrow_empty_isDraw 2 h (by decide)

theorem three_columns_draw (h : Nat) : IsDraw h (emptyBoard 3) :=
  narrow_empty_isDraw 3 h (by decide)

/-- In particular neither player can force a win, at ANY finite depth. -/
theorem narrow_neither_player_wins (w h : Nat) (hw : w ≤ 3) :
    (¬ ∃ k, WinFor h Player.black k (emptyBoard w)) ∧
    (¬ ∃ k, WinFor h Player.white k (emptyBoard w)) :=
  draw_excludes_forced_wins (narrow_empty_isDraw w h hw)

/-- An explicit full-game horizon; this is w*h plies, not a fixed search depth. -/
theorem narrow_full_horizon (w h : Nat) (hw : w ≤ 3) (p : Player) :
    SafeFor h p (w * h) (emptyBoard w) := by
  cases p with
  | black => exact (narrow_empty_isDraw w h hw).1 (w * h)
  | white => exact (narrow_empty_isDraw w h hw).2 (w * h)

-- These are theorem applications, not million-row board computations.
example : IsDraw 4 (emptyBoard 3) := three_columns_draw 4
example : IsDraw 1000000 (emptyBoard 3) := three_columns_draw 1000000

-- Zero-height boards are correctly treated as already full.
example : IsDraw 0 (emptyBoard 3) := three_columns_draw 0

-- Horizontal wins really are present in the generic geometry at width four.
-- This fixture is a geometric board, not a claim of reachability from empty.
example : HasFour 1 (fun _ : Fin 4 => [Player.black]) Player.black := by
  refine Or.inr (Or.inl ⟨0, 0, ?_⟩)
  intro i
  have hi : 0 ≤ (i.val : Int) ∧ (i.val : Int) < (4 : Int) := by
    have hh := i.isLt
    omega
  simpa [cellAtInt, hi, stone]

-- A board already containing an opponent four is rejected at EVERY horizon.
theorem previous_win_rejected (hf : HasFour h b (opponent p)) (k : Nat) :
    ¬ SafeFor h p k b := by
  cases k with
  | zero => exact fun hs => hs hf
  | succ k => exact fun hs => hs.1 hf

#print axioms narrow_empty_isDraw
#print axioms one_column_draw
#print axioms two_columns_draw
#print axioms three_columns_draw
#print axioms narrow_full_horizon
#print axioms narrow_neither_player_wins
#print axioms remaining_play_lt

end Connect4.NarrowBoards
