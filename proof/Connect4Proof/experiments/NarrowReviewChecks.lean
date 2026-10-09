import experiments.NarrowBoards
import experiments.FourColumnsFinal
import experiments.InfiniteNarrowBoards

/-! Public theorem audit and semantic regression checks. The unfinished draft
files are deliberately not imported into this certified dependency graph. -/

-- The mistaken permanent blocker from the old continuation notes is White.
example : Connect4.FourColumns.stone
    [Connect4.Player.white, .black, .white, .black, .white, .black] 4 = some .white := by
  decide

example : Connect4.FourColumns.stone
    [Connect4.Player.white, .black, .white, .black, .white, .black] 4 ≠ some .black := by
  decide

example {w h : Nat} {b : Connect4.FourColumns.Board w} {p : Connect4.Player}
    (hw : Connect4.FourColumns.HasFour h b (Connect4.opponent p)) (k : Nat) :
    ¬ Connect4.FourColumns.SafeFor h p k b := by
  cases k with
  | zero => exact fun hs => hs hw
  | succ k => exact fun hs => hs.1 hw

example {w h : Nat} {b : Connect4.FourColumns.Board w} {p : Connect4.Player}
    (hf : Connect4.FourColumns.BoardFull h b)
    (hn : ¬ Connect4.FourColumns.HasFour h b p) (k : Nat) :
    ¬ Connect4.FourColumns.WinFor h p k b :=
  Connect4.FourColumns.full_without_win_not_win hf hn k

-- Keep the strategy outside the horizon quantifier in the infinite theorem.
example : ∃ s : Connect4.InfiniteNarrowBoards.Strategy 4, ∀ k,
    Connect4.InfiniteNarrowBoards.SafeUsing .black s k []
      (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.InfiniteNarrowBoards.four_columns_infinite_draw.1

example : ∃ s : Connect4.InfiniteNarrowBoards.Strategy 4, ∀ k,
    Connect4.InfiniteNarrowBoards.SafeUsing .white s k []
      (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.InfiniteNarrowBoards.four_columns_infinite_draw.2

example : Connect4.FourColumns.IsDraw 2 (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.FourColumns.four_columns_even_draw 1 (by decide)

example : Connect4.FourColumns.IsDraw 4 (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.FourColumns.four_columns_even_draw 2 (by decide)

example : Connect4.FourColumns.IsDraw 6 (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.FourColumns.four_columns_even_draw 3 (by decide)

#check Connect4.NarrowBoards.narrow_empty_isDraw
#check Connect4.FourColumns.white_nonloss_four_columns
#check Connect4.FourColumns.opening0_small_safe
#check Connect4.InfiniteNarrowBoards.narrow_infinite_draw
#check Connect4.FourColumns.black_nonloss_four_columns
#check Connect4.FourColumns.four_columns_even_draw
#check Connect4.FourColumns.four_columns_even_no_forced_win
#print axioms Connect4.NarrowBoards.narrow_empty_isDraw
#print axioms Connect4.NarrowBoards.draw_excludes_forced_wins
#print axioms Connect4.FourColumns.white_nonloss_four_columns
#print axioms Connect4.FourColumns.pd_state_safe
#print axioms Connect4.FourColumns.pd1_state_safe
#print axioms Connect4.FourColumns.black_second_w1
#print axioms Connect4.FourColumns.black_second_w2
#print axioms Connect4.FourColumns.pd0b_safe
#print axioms Connect4.FourColumns.w0a_permanent
#print axioms Connect4.FourColumns.w0a_endgame_blocked
#print axioms Connect4.FourColumns.w0a_clear_exception
#print axioms Connect4.FourColumns.opening0_small_safe
#print axioms Connect4.FourColumns.draw_excludes_forced_wins
#print axioms Connect4.FourColumns.full_without_win_not_win
#print axioms Connect4.FourColumns.reserve_reply_exists
#print axioms Connect4.InfiniteNarrowBoards.black_nonloss
#print axioms Connect4.InfiniteNarrowBoards.white_nonloss
#print axioms Connect4.InfiniteNarrowBoards.four_columns_infinite_draw
#print axioms Connect4.InfiniteNarrowBoards.narrow_infinite_draw
#print axioms Connect4.InfiniteNarrowBoards.previous_win_rejected
#print axioms Connect4.FourColumns.opening0_safe
#print axioms Connect4.FourColumns.core13_white
#print axioms Connect4.FourColumns.permanent13_safe
#print axioms Connect4.FourColumns.reserve13_D
#print axioms Connect4.FourColumns.reserve13_U
#print axioms Connect4.FourColumns.reserve13_win
#print axioms Connect4.FourColumns.x_state_safe
#print axioms Connect4.FourColumns.y_state_safe
#print axioms Connect4.FourColumns.z_state_safe
#print axioms Connect4.FourColumns.vertical_threat_safe
#print axioms Connect4.FourColumns.full_right_empty_safe
#print axioms Connect4.FourColumns.opening1_safe
#print axioms Connect4.FourColumns.opening3_safe
#print axioms Connect4.FourColumns.black_nonloss_four_columns
#print axioms Connect4.FourColumns.four_columns_even_draw
#print axioms Connect4.FourColumns.four_columns_even_no_forced_win
