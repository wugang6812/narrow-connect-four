import OddHeight.Core

namespace OddHeight

/-- H=1 is a separate branch: (3,2) does not exist there. -/
theorem odd_height_cases (H : Nat) (odd : H % 2 = 1) :
    H = 1 ∨ H = 3 ∨ 5 ≤ H := by omega

/-- First player's empty target column leaves 3H-1 outside cells. -/
theorem first_outside_even (H : Nat) (odd : H % 2 = 1) :
    (3 * H - 1) % 2 = 0 := by omega

/-- For a second-player Q-turn the total number of empty cells is even.
    A single target column of odd height then has even remaining capacity. -/
theorem single_target_outside_even (H q total out : Nat)
    (oddH : H % 2 = 1) (oddq : q % 2 = 1) (bound : q ≤ H)
    (totalEven : total % 2 = 0) (partition : total = out + (H - q)) :
    out % 2 = 0 := by omega

theorem two_empty_targets_outside_even (H total out : Nat)
    (totalEven : total % 2 = 0) (partition : total = out + 2 * H) :
    out % 2 = 0 := by omega

/-- I_a: an available Q move in column 1 can never fill odd H. -/
theorem i_wait_cover_legal (H a : Nat) (odd : H % 2 = 1)
    (legal : 1 + 2 * a < H) : 1 + 2 * a + 2 ≤ H := by omega

/-- E waiting has even heights. Covering is legal precisely when Q did not fill. -/
theorem e_wait_cover_legal (H a : Nat) (legal : 2 * a < H)
    (notFilled : 2 * a + 1 ≠ H) : 2 * a + 2 ≤ H := by omega

/-- A full outer column forces a>=2 at H>=5, blocking its bottom diagonal. -/
theorem filled_outer_has_two_pairs (H a : Nat) (h5 : 5 ≤ H)
    (filled : 2 * a + 1 = H) : 2 ≤ a := by omega

/-- A positive even gap leaves room for BOTH Q and P. -/
theorem positive_even_gap_room (H q g : Nat) (lt : q < g)
    (evenGap : (g - q) % 2 = 0) (roof : g ≤ H) : q + 2 ≤ g ∧ q + 2 ≤ H := by
  omega

theorem gap_after_cover (q g : Nat) (room : q + 2 < g)
    (evenGap : (g - q) % 2 = 0) : (g - (q + 2)) % 2 = 0 := by omega

/-- The capacity reason a full-column fallback can stay outside J. -/
theorem outside_reply_capacity (e : Nat) (evenE : e % 2 = 0) (qCanPlay : 0 < e) :
    0 < e - 1 := by omega

theorem outside_even_after_round (e : Nat) (evenE : e % 2 = 0) (room : 2 ≤ e) :
    (e - 2) % 2 = 0 := by omega

/-- Total outside capacity positive means at least one of four outside columns has room. -/
theorem positive_sum_four (a b c d : Nat) (h : 0 < a + b + c + d) :
    0 < a ∨ 0 < b ∨ 0 < c ∨ 0 < d := by omega

/-- Only d=0 and d=1 occur in the four middle-column delayed exits. -/
theorem delay_d_cases (d : Nat) (small : d ≤ 1) : d = 0 ∨ d = 1 := by omega

/-- Strict variant for the sole delaying move: c4 with d=0. -/
theorem delay_rank_decreases (d : Nat) (small : d ≤ 1) (stillOpen : d + 1 < 2) :
    2 - (d + 1) < 2 - d := by omega

theorem no_two_silent_delay_steps (d : Nat) (small : d ≤ 1) : ¬ (d + 2 < 2) := by
  omega

/-- I.2 explicit outside count; legality of column 1 is required for Nat subtraction. -/
theorem i2_outside_even (H a : Nat) (odd : H % 2 = 1)
    (bound : 1 + 2 * a ≤ H) (h3 : 3 ≤ H) :
    ((H - (1 + 2 * a)) + H + (H - 2)) % 2 = 0 := by omega

end OddHeight
