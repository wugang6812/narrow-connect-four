import experiments.FourColumnsOddRoots
import experiments.FourColumnsFinal

namespace Connect4.FourColumns

structure OddRootBundle : Prop where
  p0 : ControlTree 5 5 .black (fourTuple [.black] [] [] [])
  p1 : ControlTree 5 5 .white (fourTuple [.black, .white] [] [] [])
  p2 : ControlTree 5 5 .white (fourTuple [] [] [] [.black, .white])
  p3 : ControlTree 5 5 .white (fourTuple [.white] [.black] [] [])
  p4 : ControlTree 5 5 .white (fourTuple [] [] [.black] [.white])
  p5 : ControlTree 7 6 .black (fourTuple [.black] [] [] [])
  p6 : ControlTree 7 6 .white (fourTuple [.black, .white] [] [] [])
  p7 : ControlTree 7 6 .white (fourTuple [] [] [] [.black, .white])
  p8 : ControlTree 7 6 .white (fourTuple [.white] [.black] [] [])
  p9 : ControlTree 7 6 .white (fourTuple [] [] [.black] [.white])
  p10 : ControlTree 1 1 .black (fourTuple [.black] [] [] [])
  p11 : ControlTree 1 1 .white (fourTuple [] [] [] [])
  p12 : ControlTree 3 3 .black (fourTuple [.black] [] [] [])
  p13 : ControlTree 3 3 .white (fourTuple [] [] [] [])

namespace OddAssembly

private theorem tuple_empty_eq : fourTuple [] [] [] [] = emptyBoard 4 := by
  funext c
  fin_cases c <;> rfl

theorem four_columns_height_one_draw (roots : OddRootBundle) : IsDraw 1 (emptyBoard 4) := by
  constructor
  · exact black_empty_from_opening (by decide) roots.p10.real_safe
  · simpa only [tuple_empty_eq] using roots.p11.real_safe

theorem four_columns_height_three_draw (roots : OddRootBundle) : IsDraw 3 (emptyBoard 4) := by
  constructor
  · exact black_empty_from_opening (by decide) roots.p12.real_safe
  · simpa only [tuple_empty_eq] using roots.p13.real_safe

theorem four_columns_height_five_draw (roots : OddRootBundle) : IsDraw 5 (emptyBoard 4) := by
  constructor
  · exact black_empty_from_opening (by decide) roots.p0.real_safe
  · exact white_empty_from_openings (by decide)
      roots.p1.real_safe roots.p3.real_safe
      roots.p4.real_safe roots.p2.real_safe

theorem four_columns_large_odd_draw (roots : OddRootBundle) {h : Nat} (h7 : 7 ≤ h) (hh : h % 2 = 1) :
    IsDraw h (emptyBoard 4) := by
  constructor
  · apply black_empty_from_opening (by omega)
    apply small_control_safe h7 hh (htree := roots.p5) <;> decide
  · apply white_empty_from_openings (by omega)
    · apply small_control_safe h7 hh (htree := roots.p6) <;> decide
    · apply small_control_safe h7 hh (htree := roots.p8) <;> decide
    · apply small_control_safe h7 hh (htree := roots.p9) <;> decide
    · apply small_control_safe h7 hh (htree := roots.p7) <;> decide

theorem four_columns_odd_height_draw (roots : OddRootBundle) {h : Nat} (hh : h % 2 = 1) :
    IsDraw h (emptyBoard 4) := by
  by_cases h7 : 7 ≤ h
  · exact four_columns_large_odd_draw roots h7 hh
  · have hsmall : h = 1 ∨ h = 3 ∨ h = 5 := by omega
    rcases hsmall with rfl | rfl | rfl
    · exact four_columns_height_one_draw roots
    · exact four_columns_height_three_draw roots
    · exact four_columns_height_five_draw roots

/-- Assemble every positive odd height from the explicitly supplied finite roots. -/
theorem four_columns_odd_draw (roots : OddRootBundle) (n : Nat) (hn : 1 ≤ n) :
    IsDraw (2*n-1) (emptyBoard 4) :=
  four_columns_odd_height_draw roots (by omega)

/-- Combined with the previously verified even-height theorem, all finite heights. -/
theorem four_columns_finite_draw (roots : OddRootBundle) (h : Nat) : IsDraw h (emptyBoard 4) := by
  by_cases hz : h = 0
  · subst h
    constructor <;> intro k <;>
      exact safeFor_terminal' (empty_no_four' 0 _) (Or.inr (by decide)) k
  · by_cases he : h % 2 = 0
    · have hh : h = 2 * (h/2) := by omega
      have hn : 1 ≤ h/2 := by omega
      simpa only [← hh] using four_columns_even_draw (h/2) hn
    · exact four_columns_odd_height_draw roots (by omega)

theorem four_columns_odd_no_forced_win (roots : OddRootBundle) (n : Nat) (hn : 1 ≤ n) :
    (¬ ∃ k, WinFor (2*n-1) .black k (emptyBoard 4)) ∧
    (¬ ∃ k, WinFor (2*n-1) .white k (emptyBoard 4)) :=
  draw_excludes_forced_wins (four_columns_odd_draw roots n hn)

theorem four_columns_finite_no_forced_win (roots : OddRootBundle) (h : Nat) :
    (¬ ∃ k, WinFor h .black k (emptyBoard 4)) ∧
    (¬ ∃ k, WinFor h .white k (emptyBoard 4)) :=
  draw_excludes_forced_wins (four_columns_finite_draw roots h)


end OddAssembly

#print axioms OddAssembly.four_columns_finite_draw

end Connect4.FourColumns
