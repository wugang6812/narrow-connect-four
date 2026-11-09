import OddHeight.Core

namespace OddHeight
open Col

def totalHeight (b : Board) : Nat :=
  height b c1 + height b c2 + height b c3 + height b c4

def remaining (H : Nat) (b : Board) : Nat :=
  (H - height b c1) + (H - height b c2) + (H - height b c3) + (H - height b c4)

theorem totalHeight_drop (b : Board) (c : Col) (p : Player) :
    totalHeight (drop b c p) = totalHeight b + 1 := by
  cases c <;> simp [totalHeight, height, drop] <;> omega

theorem remaining_partition {H : Nat} {b : Board} (hb : Bounded H b) :
    remaining H b + totalHeight b = 4 * H := by
  have h1 := hb c1
  have h2 := hb c2
  have h3 := hb c3
  have h4 := hb c4
  unfold remaining totalHeight
  omega

theorem remaining_drop {H : Nat} {b : Board} {c : Col}
    (hb : Bounded H b) (hc : Legal H b c) (p : Player) :
    remaining H (drop b c p) + 1 = remaining H b := by
  have old := remaining_partition hb
  have next := remaining_partition (drop_bounded hb hc p)
  have step := totalHeight_drop b c p
  omega

theorem remaining_strictly_decreases {H : Nat} {b : Board} {c : Col}
    (hb : Bounded H b) (hc : Legal H b c) (p : Player) :
    remaining H (drop b c p) < remaining H b := by
  have h := remaining_drop hb hc p
  omega

theorem remaining_round {H : Nat} {b : Board} {q p : Col}
    (hb : Bounded H b) (hq : Legal H b q) (hp : Legal H (drop b q .Q) p) :
    remaining H (drop (drop b q .Q) p .P) + 2 = remaining H b := by
  have first := remaining_drop hb hq Player.Q
  have second := remaining_drop (drop_bounded hb hq Player.Q) hp Player.P
  omega

/-- Any legal move history, even before restricting alternation or stopping at wins. -/
inductive Moves (H : Nat) : Nat → Board → Board → Prop where
  | nil (b : Board) : Moves H 0 b b
  | cons {n : Nat} {b z : Board} (c : Col) (p : Player) :
      Legal H b c → Moves H n (drop b c p) z → Moves H (n + 1) b z

/-- A stronger capacity bound than needed for the strategy: every legal history is finite. -/
theorem moves_length_le {H n : Nat} {b z : Board} (hist : Moves H n b z) :
    Bounded H b → n ≤ remaining H b := by
  induction hist with
  | nil b => intro _; omega
  | @cons n b z c p hc tail ih =>
      intro hb
      have shorter := ih (drop_bounded hb hc p)
      have step := remaining_drop hb hc p
      omega

theorem no_arbitrarily_long_moves {H : Nat} {b : Board} (hb : Bounded H b) :
    ¬ (∀ n, ∃ z, Moves H n b z) := by
  intro infinite
  rcases infinite (remaining H b + 1) with ⟨z, hz⟩
  have bound := moves_length_le hz hb
  omega

#print axioms moves_length_le
#print axioms no_arbitrarily_long_moves
end OddHeight
