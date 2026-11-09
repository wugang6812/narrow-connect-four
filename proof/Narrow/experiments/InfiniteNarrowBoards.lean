import experiments.FourColumns
import Mathlib.Tactic.FinCases

/-!
An actual unbounded-height game. Every column is always legal; there is no
full-board terminal. Strategies are single functions of the entire reversed
move history, chosen BEFORE the number of future moves is quantified.
-/
namespace Connect4.InfiniteNarrowBoards
open FourColumns
export FourColumns (emptyBoard play stone toMove cellAtInt play_eq play_ne
  stone_append stone_append_other player_ne_opponent toMove_play' toMove_empty
  cellAtInt_some hasFour_minStones totalStones_play' totalStones_empty)

abbrev Board (w : Nat) := FourColumns.Board w
abbrev Strategy (w : Nat) := List (Fin w) → Fin w

/-- A four-in-a-row has a finite witness, without a fixed upper boundary. -/
def HasFour (b : Board w) (p : Player) : Prop := ∃ h, FourColumns.HasFour h b p

/-- Safety under one fixed strategy; an existing opponent win is always rejected. -/
def SafeUsing (p : Player) (s : Strategy w) : Nat → List (Fin w) → Board w → Prop
  | 0, _, b => ¬ HasFour b (opponent p)
  | k + 1, hist, b =>
    ¬ HasFour b (opponent p) ∧
      (HasFour b p ∨
        if toMove b = p then
          SafeUsing p s k (s hist :: hist) (play b (s hist) (toMove b))
        else ∀ c, SafeUsing p s k (c :: hist) (play b c (toMove b)))

def CanAvoidLoss (p : Player) (b : Board w) : Prop :=
  ∃ s : Strategy w, ∀ k, SafeUsing p s k [] b

def IsDraw (b : Board w) : Prop := CanAvoidLoss .black b ∧ CanAvoidLoss .white b

def Paint (p : Player) (f : Fin w → Nat → Prop) (b : Board w) : Prop :=
  ∀ d i, stone (b d) i = some (opponent p) → f d i

def Parity (r : Fin w → Nat) (b : Board w) : Prop :=
  ∀ d, (b d).length % 2 = r d

theorem paint_defender {p : Player} {f : Fin w → Nat → Prop} {b : Board w}
    (hp : Paint p f b) (c : Fin w) : Paint p f (play b c p) := by
  intro d i hs
  by_cases hd : d = c
  · subst d
    rw [play_eq] at hs
    exact hp c i (stone_append_other (player_ne_opponent p) hs)
  · exact hp d i (by simpa only [play_ne b c d p hd] using hs)

theorem paint_opponent {p : Player} {f : Fin w → Nat → Prop} {r : Fin w → Nat}
    {b : Board w} (hp : Paint p f b) (hr : Parity r b)
    (ha : ∀ d i, i % 2 = r d → f d i) (c : Fin w) :
    Paint p f (play b c (opponent p)) := by
  intro d i hs
  by_cases hd : d = c
  · subst d
    rw [play_eq, stone_append] at hs
    split at hs
    · exact hp c i hs
    · split at hs
      · rename_i he
        subst i
        exact ha c _ (hr c)
      · cases hs
  · exact hp d i (by simpa only [play_ne b c d _ hd] using hs)

theorem parity_pair {r : Fin w → Nat} {b : Board w} (hr : Parity r b)
    (c : Fin w) (p q : Player) : Parity r (play (play b c p) c q) := by
  intro d
  by_cases hd : d = c
  · subst d
    rw [play_eq, play_eq]
    simp only [List.length_append, List.length_singleton]
    have := hr c
    omega
  · simpa only [play_ne _ c d q hd, play_ne _ c d p hd] using hr d

/-- Generic same-column defense. The admissible history condition handles the
    exceptional first response without allowing the strategy to depend on k. -/
theorem pairing (p : Player) (s : Strategy w) (ok : List (Fin w) → Prop)
    (cover : ∀ c hist, ok hist → s (c :: hist) = c)
    (closed : ∀ c hist, ok hist → ok (c :: c :: hist))
    (f : Fin w → Nat → Prop) (r : Fin w → Nat)
    (admit : ∀ d i, i % 2 = r d → f d i)
    (sound : ∀ b, Paint p f b → ¬ HasFour b (opponent p)) (k : Nat) :
    (∀ b hist, ok hist → Paint p f b → Parity r b → toMove b = opponent p →
      SafeUsing p s k hist b) ∧
    (∀ b hist c, ok hist → Paint p f b → Parity r b → toMove b = opponent p →
      SafeUsing p s k (c :: hist) (play b c (opponent p))) := by
  induction k with
  | zero =>
    exact ⟨fun b _ _ hp _ _ => sound b hp,
      fun _ _ c _ hp hr _ => sound _ (paint_opponent hp hr admit c)⟩
  | succ k ih =>
    constructor
    · intro b hist ho hp hr ht
      refine ⟨sound b hp, Or.inr ?_⟩
      rw [if_neg (by rw [ht]; exact Ne.symm (player_ne_opponent p)), ht]
      exact fun c => ih.2 b hist c ho hp hr ht
    · intro b hist c ho hp hr ht
      have hp' := paint_opponent hp hr admit c
      have ht' : toMove (play b c (opponent p)) = p := by
        rw [toMove_play', ht, opponent_involutive]
      refine ⟨sound _ hp', Or.inr ?_⟩
      rw [if_pos ht', cover c hist ho, ht']
      apply ih.1 _ _ (closed c hist ho) (paint_defender hp' c) (parity_pair hr c _ _)
      rw [toMove_play', ht']

/-! The black strategy: first column 0, then copy the opponent's last column. -/
def blackStrategy : Strategy 4
  | [] => 0
  | c :: _ => c

def blackParity (c : Fin 4) : Nat := if c = 0 then 1 else 0

private theorem line_cell {h : Nat} {b : Board 4} {p : Player} {x y dy : Int}
    (hd : FourColumns.HasFourDir h b p x y 1 dy) (d : Fin 4) :
    0 ≤ y + (d : Int) * dy ∧
      stone (b d) (y + (d : Int) * dy).toNat = some p := by
  have hs0 : cellAtInt h b x y = some p := by simpa using hd 0
  have hs3 : cellAtInt h b (x + 3) (y + 3 * dy) = some p := by simpa using hd 3
  obtain ⟨c0, hx0, _, _, _⟩ := cellAtInt_some hs0
  obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some hs3
  have h0 := c0.isLt
  have h3 := c3.isLt
  have hx : x = 0 := by omega
  have hs : cellAtInt h b (d : Int) (y + (d : Int) * dy) = some p := by
    simpa only [hx, Int.zero_add, Int.mul_one] using hd d
  obtain ⟨c, hc, hy, _, ht⟩ := cellAtInt_some hs
  have he : c = d := Fin.ext (by omega)
  exact ⟨hy, by simpa only [he] using ht⟩

theorem black_pattern_safe (b : Board 4)
    (hp : Paint .black (fun d i => i % 2 = blackParity d) b) :
    ¬ HasFour b .white := by
  rintro ⟨h, hf⟩
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · have hs0 : cellAtInt h b x y = some .white := by simpa using hd 0
    have hs1 : cellAtInt h b x (y + 1) = some .white := by simpa using hd 1
    obtain ⟨c0, hx0, hy0, _, ht0⟩ := cellAtInt_some hs0
    obtain ⟨c1, hx1, hy1, _, ht1⟩ := cellAtInt_some hs1
    have he : c1 = c0 := Fin.ext (by omega)
    rw [he] at ht1
    have ha := hp c0 _ ht0
    have hb := hp c0 _ ht1
    have hi : (y + 1).toNat = y.toNat + 1 := by omega
    rw [hi] at hb
    omega
  · obtain ⟨_, ht0⟩ := line_cell hd 0
    obtain ⟨_, ht1⟩ := line_cell hd 1
    have ha := hp 0 _ ht0
    have hb := hp 1 _ ht1
    simp [blackParity] at ha hb
    omega
  · obtain ⟨hy1, ht1⟩ := line_cell hd 1
    obtain ⟨hy2, ht2⟩ := line_cell hd 2
    have ha := hp 1 _ ht1
    have hb := hp 2 _ ht2
    simp [blackParity] at ha hb
    norm_num at hy1 hy2
    omega
  · obtain ⟨hy1, ht1⟩ := line_cell hd 1
    obtain ⟨hy2, ht2⟩ := line_cell hd 2
    have ha := hp 1 _ ht1
    have hb := hp 2 _ ht2
    simp [blackParity] at ha hb
    norm_num at hy1 hy2
    omega

theorem empty_no_four (w : Nat) (p : Player) : ¬ HasFour (emptyBoard w) p := by
  rintro ⟨h, hf⟩
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ <;>
    obtain ⟨c, _, _, _, hs⟩ := cellAtInt_some (hd 0) <;>
    simp [emptyBoard, stone] at hs

theorem black_nonloss : CanAvoidLoss .black (emptyBoard 4) := by
  refine ⟨blackStrategy, ?_⟩
  intro k
  cases k with
  | zero => exact empty_no_four _ _
  | succ k =>
    refine ⟨empty_no_four _ _, Or.inr ?_⟩
    rw [if_pos (toMove_empty 4), toMove_empty]
    change SafeUsing .black blackStrategy k [0] (play (emptyBoard 4) 0 .black)
    apply (pairing .black blackStrategy (fun _ => True) (fun _ _ _ => rfl)
      (fun _ _ _ => True.intro) (fun d i => i % 2 = blackParity d) blackParity
      (fun _ _ h => h) black_pattern_safe k).1 _ _ True.intro
    · apply paint_defender
      intro d i hs
      simp [emptyBoard, stone] at hs
    · intro d
      by_cases hd : d = 0
      · subst d; simp [play, emptyBoard, blackParity]
      · simp [play, emptyBoard, blackParity, hd]
    · rw [toMove_play', toMove_empty]

/-! White's fixed first response and the subsequent pairing phase. -/
def whiteStrategy : Strategy 4
  | [] => 0
  | [c] => partner c
  | c :: _ :: _ => c

def whiteParity (q c : Fin 4) : Nat := if c = q ∨ c = partner q then 1 else 0

def whiteMask (q c : Fin 4) (i : Nat) : Prop :=
  i % 2 = whiteParity q c ∨ (c = q ∧ i = 0)

theorem white_pattern_safe (q : Fin 4) (b : Board 4) (hp : Paint .white (whiteMask q) b) :
    ¬ HasFour b .black := by
  rintro ⟨h, hf⟩
  apply noBlackFour_phase2 (q := q) (h := h) (b := b) _ _ _ hf
  · intro i hs
    rcases hp q i hs with he | ⟨_, he⟩
    · right; simpa [whiteParity, InP] using he
    · left; omega
  · intro i hs
    rcases hp (partner q) i hs with he | ⟨he, _⟩
    · simpa [whiteParity, InP] using he
    · exact False.elim (partner_ne q he)
  · intro d hd i hs
    change ¬ (d = q ∨ d = partner q) at hd
    rcases hp d i hs with he | ⟨he, _⟩
    · simpa [whiteParity, hd] using he
    · exact False.elim (hd (Or.inl he))

theorem white_nonloss : CanAvoidLoss .white (emptyBoard 4) := by
  refine ⟨whiteStrategy, ?_⟩
  intro k
  cases k with
  | zero => exact empty_no_four _ _
  | succ k =>
    refine ⟨empty_no_four _ _, Or.inr ?_⟩
    rw [if_neg (by rw [toMove_empty]; decide), toMove_empty]
    intro q
    have hnb : ¬ HasFour (play (emptyBoard 4) q .black) .black := by
      rintro ⟨h, hf⟩
      have := hasFour_minStones hf
      rw [totalStones_play', totalStones_empty] at this
      omega
    cases k with
    | zero => exact hnb
    | succ k =>
      have ht : toMove (play (emptyBoard 4) q .black) = .white := by
        rw [toMove_play', toMove_empty]; rfl
      refine ⟨hnb, Or.inr ?_⟩
      rw [if_pos ht, ht]
      change SafeUsing .white whiteStrategy k [partner q, q]
        (play (play (emptyBoard 4) q .black) (partner q) .white)
      apply (pairing .white whiteStrategy (fun hist => hist ≠ [])
        (by intro c hist hh; cases hist with
            | nil => exact False.elim (hh rfl)
            | cons a rest => rfl)
        (by intros; simp) (whiteMask q) (whiteParity q)
        (fun _ _ h => Or.inl h) (white_pattern_safe q) k).1 _ _ (by simp)
      · apply paint_defender
        intro d i hs
        by_cases hd : d = q
        · subst d
          rw [play_eq] at hs
          cases i with
          | zero => exact Or.inr ⟨rfl, rfl⟩
          | succ i => simp [emptyBoard, stone] at hs
        · rw [play_ne _ q d .black hd] at hs
          simp [emptyBoard, stone] at hs
      · intro d
        by_cases hdq : d = q
        · subst d
          rw [play_ne _ (partner q) q .white (Ne.symm (partner_ne q)), play_eq]
          simp [emptyBoard, whiteParity, InP]
        · by_cases hdp : d = partner q
          · subst d
            rw [play_eq, play_ne _ q (partner q) .black (partner_ne q)]
            simp [emptyBoard, whiteParity, InP]
          · rw [play_ne _ (partner q) d .white hdp, play_ne _ q d .black hdq]
            simp [emptyBoard, whiteParity, InP, hdq, hdp]
      · rw [toMove_play', toMove_play', toMove_empty]; rfl

/-- Both strategies are fixed functions, safe for every finite prefix of the
    genuinely unbounded game. Infinite play without a winner is a draw. -/
theorem four_columns_infinite_draw : IsDraw (emptyBoard 4) :=
  ⟨black_nonloss, white_nonloss⟩

/-! Widths 1–3: a single parity per column excludes vertical adjacency;
    every other direction would require at least four columns. -/
theorem narrow_pattern_safe {w : Nat} (hw : w ≤ 3) (p : Player)
    (r : Fin w → Nat) (b : Board w)
    (hp : Paint p (fun d i => i % 2 = r d) b) : ¬ HasFour b (opponent p) := by
  rintro ⟨h, hf⟩
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · have hs0 : cellAtInt h b x y = some (opponent p) := by simpa using hd 0
    have hs1 : cellAtInt h b x (y + 1) = some (opponent p) := by simpa using hd 1
    obtain ⟨c0, hx0, hy0, _, ht0⟩ := cellAtInt_some hs0
    obtain ⟨c1, hx1, _, _, ht1⟩ := cellAtInt_some hs1
    have he : c1 = c0 := Fin.ext (by omega)
    rw [he] at ht1
    have ha := hp c0 _ ht0
    have hb := hp c0 _ ht1
    have hi : (y + 1).toNat = y.toNat + 1 := by omega
    rw [hi] at hb
    omega
  all_goals
    obtain ⟨c0, hx0, _, _, _⟩ := cellAtInt_some (hd 0)
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some (hd 3)
    have h0 := c0.isLt
    have h3 := c3.isLt
    norm_num at hx0 hx3
    omega

def coverStrategy (first : Fin w) : Strategy w
  | [] => first
  | c :: _ => c

theorem narrow_white_nonloss {w : Nat} (first : Fin w) (hw : w ≤ 3) :
    CanAvoidLoss .white (emptyBoard w) := by
  refine ⟨coverStrategy first, fun k => ?_⟩
  apply (pairing .white (coverStrategy first) (fun _ => True) (fun _ _ _ => rfl)
    (fun _ _ _ => True.intro) (fun _ i => i % 2 = 0) (fun _ => 0)
    (fun _ _ h => h) (narrow_pattern_safe hw .white (fun _ => 0)) k).1 _ _ True.intro
  · intro d i hs; simp [emptyBoard, stone] at hs
  · intro d; rfl
  · rw [toMove_empty]; rfl

theorem narrow_black_nonloss {w : Nat} (first : Fin w) (hw : w ≤ 3) :
    CanAvoidLoss .black (emptyBoard w) := by
  let r : Fin w → Nat := fun d => if d = first then 1 else 0
  refine ⟨coverStrategy first, fun k => ?_⟩
  cases k with
  | zero => exact empty_no_four _ _
  | succ k =>
    refine ⟨empty_no_four _ _, Or.inr ?_⟩
    rw [if_pos (toMove_empty w), toMove_empty]
    change SafeUsing .black (coverStrategy first) k [first] (play (emptyBoard w) first .black)
    apply (pairing .black (coverStrategy first) (fun _ => True) (fun _ _ _ => rfl)
      (fun _ _ _ => True.intro) (fun d i => i % 2 = r d) r
      (fun _ _ h => h) (narrow_pattern_safe hw .black r) k).1 _ _ True.intro
    · apply paint_defender
      intro d i hs; simp [emptyBoard, stone] at hs
    · intro d
      by_cases hd : d = first
      · subst d; simp [play, emptyBoard, r]
      · simp [play, emptyBoard, r, hd]
    · rw [toMove_play', toMove_empty]

/-- Paper Theorem 1.1(3), with explicit uniform strategies on the infinite board. -/
theorem narrow_infinite_draw (w : Nat) (hw0 : 1 ≤ w) (hw4 : w ≤ 4) :
    IsDraw (emptyBoard w) := by
  by_cases hw3 : w ≤ 3
  · let first : Fin w := ⟨0, by omega⟩
    exact ⟨narrow_black_nonloss first hw3, narrow_white_nonloss first hw3⟩
  · have he : w = 4 := by omega
    subst w
    exact four_columns_infinite_draw

theorem previous_win_rejected {w : Nat} {b : Board w} {p : Player}
    (s : Strategy w) (hist : List (Fin w)) (k : Nat) (hw : HasFour b (opponent p)) :
    ¬ SafeUsing p s k hist b := by
  cases k with
  | zero => exact fun hs => hs hw
  | succ k => exact fun hs => hs.1 hw

#print axioms four_columns_infinite_draw
#print axioms narrow_infinite_draw
end Connect4.InfiniteNarrowBoards
