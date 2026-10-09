import experiments.NarrowReviewChecks
import experiments.FourColumnsOddReview

example (w h : Nat) (hw : w ≤ 3) :
    Connect4.NarrowBoards.IsDraw h (Connect4.NarrowBoards.emptyBoard w) :=
  Connect4.NarrowBoards.narrow_empty_isDraw w h hw

example (n : Nat) (hn : 1 ≤ n) :
    Connect4.FourColumns.IsDraw (2*n-1) (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.FourColumns.four_columns_odd_draw n hn

example (h : Nat) :
    Connect4.FourColumns.IsDraw h (Connect4.FourColumns.emptyBoard 4) :=
  Connect4.FourColumns.four_columns_finite_draw h

example (w : Nat) (hw0 : 1 ≤ w) (hw4 : w ≤ 4) :
    Connect4.InfiniteNarrowBoards.IsDraw (Connect4.FourColumns.emptyBoard w) :=
  Connect4.InfiniteNarrowBoards.narrow_infinite_draw w hw0 hw4

#print axioms Connect4.NarrowBoards.narrow_empty_isDraw
#print axioms Connect4.FourColumns.four_columns_odd_draw
#print axioms Connect4.FourColumns.four_columns_finite_draw
#print axioms Connect4.FourColumns.four_columns_odd_no_forced_win
#print axioms Connect4.InfiniteNarrowBoards.narrow_infinite_draw
