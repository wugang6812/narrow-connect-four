import experiments.FourColumnsOddFinal

namespace Connect4.FourColumns

private def topWinExample : Board 4 :=
  fourTuple [.black, .black, .black, .white, .black, .white, .black]
    [.black, .white, .black, .black, .white, .black, .white]
    [.white, .white, .white, .black, .black, .black, .white]
    [.white, .white, .white, .black]

-- A genuine high win must not be treated as a six-row control win.
example : HasFour 7 topWinExample .black := by decide +kernel
example : ¬ HasFour 6 topWinExample .black := by decide +kernel

-- Preserve the existing immediate-opponent-win guard at every horizon.
example (h k : Nat) (b : Board 4) (p : Player)
    (hf : HasFour h b (opponent p)) : ¬ SafeFor h p k b := by
  cases k with
  | zero => exact fun hs => hs hf
  | succ k => exact fun hs => hs.1 hf

-- Full without a win cannot be relabeled as a forced win.
example (h k : Nat) (b : Board 4) (p : Player)
    (hf : BoardFull h b) (hn : ¬ HasFour h b p) : ¬ WinFor h p k b :=
  full_without_win_not_win hf hn k

-- Exact universally quantified target type, with no capacity bound.
example : ∀ n : Nat, 1 ≤ n → IsDraw (2*n-1) (emptyBoard 4) :=
  four_columns_odd_draw

example : ∀ h : Nat, IsDraw h (emptyBoard 4) := four_columns_finite_draw

example : IsDraw 0 (emptyBoard 4) := four_columns_finite_draw 0
example : IsDraw 1 (emptyBoard 4) := four_columns_height_one_draw
example : IsDraw 3 (emptyBoard 4) := four_columns_height_three_draw
example : IsDraw 5 (emptyBoard 4) := four_columns_height_five_draw
example : IsDraw 7 (emptyBoard 4) := four_columns_finite_draw 7
example : IsDraw 9 (emptyBoard 4) := four_columns_finite_draw 9
example : IsDraw 1000001 (emptyBoard 4) := four_columns_finite_draw 1000001

-- A high unsupported opposing stone is excluded by the lifting invariant.
example {b : Board 4} {p : Player} (hs : HighSupported p b) (c : Fin 4)
    (he : stone (b c) 6 = some (opponent p)) :
    stone (b c) 5 = some p := hs c 6 (by decide) he

-- The control certificate checks both players only in the stated scoring region.
#check ControlTree
#check ControlTree.real_safe
#check odd_control_lift
#print axioms fastFour_iff
#print axioms high_supported_no_four
#print axioms tail_round
#print axioms pair_region_safe
#print axioms odd_control_lift
#print axioms ControlTree.real_safe
#print axioms ControlTree.mirror
#print axioms four_columns_odd_draw
#print axioms four_columns_finite_draw
#print axioms four_columns_odd_no_forced_win
#print axioms four_columns_finite_no_forced_win

end Connect4.FourColumns
