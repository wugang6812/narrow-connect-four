import experiments.FourColumnsOddAssembly
import experiments.OddCertificates.P0_0002
import experiments.OddCertificates.P1_0001
import experiments.OddCertificates.P2_0001
import experiments.OddCertificates.P3_0001
import experiments.OddCertificates.P4_0001
import experiments.OddCertificates.P5_0014
import experiments.OddCertificates.P6_0009
import experiments.OddCertificates.P7_0000
import experiments.OddCertificates.P8_0007
import experiments.OddCertificates.P9_0000
import experiments.OddCertificates.P10_0000
import experiments.OddCertificates.P11_0000
import experiments.OddCertificates.P12_0000
import experiments.OddCertificates.P13_0000

namespace Connect4.FourColumns

/-- Every certificate hypothesis is discharged by a kernel-checked proof DAG. -/
def odd_root_bundle : OddRootBundle where
  p0 := OddCertificate.P0.root
  p1 := OddCertificate.P1.root
  p2 := OddCertificate.P2.root
  p3 := OddCertificate.P3.root
  p4 := OddCertificate.P4.root
  p5 := OddCertificate.P5.root
  p6 := OddCertificate.P6.root
  p7 := OddCertificate.P7.root
  p8 := OddCertificate.P8.root
  p9 := OddCertificate.P9.root
  p10 := OddCertificate.P10.root
  p11 := OddCertificate.P11.root
  p12 := OddCertificate.P12.root
  p13 := OddCertificate.P13.root

theorem four_columns_height_one_draw : IsDraw 1 (emptyBoard 4) :=
  OddAssembly.four_columns_height_one_draw odd_root_bundle

theorem four_columns_height_three_draw : IsDraw 3 (emptyBoard 4) :=
  OddAssembly.four_columns_height_three_draw odd_root_bundle

theorem four_columns_height_five_draw : IsDraw 5 (emptyBoard 4) :=
  OddAssembly.four_columns_height_five_draw odd_root_bundle

theorem four_columns_large_odd_draw {h : Nat} (h7 : 7 ≤ h) (hh : h % 2 = 1) :
    IsDraw h (emptyBoard 4) :=
  OddAssembly.four_columns_large_odd_draw odd_root_bundle h7 hh

theorem four_columns_odd_height_draw {h : Nat} (hh : h % 2 = 1) :
    IsDraw h (emptyBoard 4) :=
  OddAssembly.four_columns_odd_height_draw odd_root_bundle hh

/-- Every positive odd height, without a search bound or unproved premise. -/
theorem four_columns_odd_draw (n : Nat) (hn : 1 ≤ n) :
    IsDraw (2*n-1) (emptyBoard 4) :=
  OddAssembly.four_columns_odd_draw odd_root_bundle n hn

/-- The odd and even results together cover every finite height, including zero. -/
theorem four_columns_finite_draw (h : Nat) : IsDraw h (emptyBoard 4) :=
  OddAssembly.four_columns_finite_draw odd_root_bundle h

theorem four_columns_odd_no_forced_win (n : Nat) (hn : 1 ≤ n) :
    (¬ ∃ k, WinFor (2*n-1) .black k (emptyBoard 4)) ∧
    (¬ ∃ k, WinFor (2*n-1) .white k (emptyBoard 4)) :=
  OddAssembly.four_columns_odd_no_forced_win odd_root_bundle n hn

theorem four_columns_finite_no_forced_win (h : Nat) :
    (¬ ∃ k, WinFor h .black k (emptyBoard 4)) ∧
    (¬ ∃ k, WinFor h .white k (emptyBoard 4)) :=
  OddAssembly.four_columns_finite_no_forced_win odd_root_bundle h

#print axioms four_columns_odd_draw
#print axioms four_columns_finite_draw
#print axioms four_columns_odd_no_forced_win
#print axioms four_columns_finite_no_forced_win

end Connect4.FourColumns
