import OddHeight.Core

/-!
Resource arithmetic for U1. These are capacity/termination lemmas, not an
unconditional nonloss theorem: geometric protection and earliest-win safety
must still be supplied by each strategy using this interface.
-/
namespace U1Improvement
open OddHeight

theorem target_pair_room {H q g : Nat}
    (ahead : q < g) (inside : g ≤ H) (even : (g-q)%2 = 0) :
    q+1 < g ∧ q+2 ≤ g ∧ q+1 < H := by omega

theorem pending_target_after_cover {q g : Nat}
    (ahead : q+2 < g) (even : (g-q)%2 = 0) :
    0 < g-(q+2) ∧ (g-(q+2))%2 = 0 := by omega

theorem even_outside_has_reply {outside : Nat}
    (even : outside%2 = 0) (opponent_can_enter : 0 < outside) :
    0 < outside-1 ∧ (outside-2)%2 = 0 := by omega

/-- A completed ordinary target can be released exactly when its residual
column capacity is even. Terminal/winning targets do not need this release. -/
theorem release_even_iff {outside H g : Nat} (even : outside%2 = 0) :
    (outside+(H-g))%2 = 0 ↔ (H-g)%2 = 0 := by omega

theorem odd_release_flips {outside H g : Nat}
    (even : outside%2 = 0) (odd : (H-g)%2 = 1) :
    (outside+(H-g))%2 = 1 := by omega

theorem target_capacity_parity {H q g : Nat}
    (ordered : q ≤ g) (inside : g ≤ H) (even : (g-q)%2 = 0) :
    (H-q)%2 = (H-g)%2 := by omega

/-- Exactly the same capacity is counted before and after moving a completed
ordinary target column into the outside pool. The two real stones lower rank. -/
theorem release_preserves_round_rank {outside H q g : Nat}
    (target_reached : g = q+2) (inside : g ≤ H) :
    outside+(H-g)+2 = outside+(H-q) := by omega

def afterFullTransfer (remaining : Col → Nat) (filled other : Col) : Col → Nat :=
  fun c => if c = filled then 0 else if c = other then remaining c-1 else remaining c

/-- The full-column transfer of the two-odd-columns controller. This proves
legality and parity only; it intentionally does not assert first-win safety. -/
theorem two_odd_transfer {remaining : Col → Nat} {filled other : Col}
    (distinct : filled ≠ other)
    (filled_had_one : remaining filled = 1)
    (other_odd : remaining other % 2 = 1)
    (rest_even : ∀ c, c ≠ filled → c ≠ other → remaining c % 2 = 0) :
    0 < remaining other ∧
      ∀ c, afterFullTransfer remaining filled other c % 2 = 0 := by
  refine ⟨by omega, ?_⟩
  intro c
  by_cases first : c = filled
  · simp [afterFullTransfer, first]
  · by_cases second : c = other
    · subst c
      have even : (remaining other-1)%2 = 0 := by omega
      simpa [afterFullTransfer, first] using even
    · simpa [afterFullTransfer, first, second] using rest_even c first second

/-- The least integer of the requested parity at or above an interval's left
endpoint. This is the primitive needed by a three-pointer A2 interval scan. -/
def parityCeil (lo parity : Nat) : Nat :=
  if lo%2 = parity then lo else lo+1

theorem parityCeil_spec {lo parity : Nat} (bit : parity < 2) :
    lo ≤ parityCeil lo parity ∧ parityCeil lo parity % 2 = parity ∧
      ∀ n, lo ≤ n → n%2 = parity → parityCeil lo parity ≤ n := by
  by_cases equal : lo%2 = parity
  · simp only [parityCeil, if_pos equal]
    exact ⟨Nat.le_refl _, equal, fun n lower _ => lower⟩
  · simp only [parityCeil, if_neg equal]
    refine ⟨by omega, by omega, ?_⟩
    intro n lower color
    omega

theorem parity_interval_nonempty {lo hi parity : Nat} (bit : parity < 2) :
    (∃ n, lo ≤ n ∧ n ≤ hi ∧ n%2 = parity) ↔ parityCeil lo parity ≤ hi := by
  have spec := parityCeil_spec (lo := lo) bit
  constructor
  · rintro ⟨n, lower, upper, color⟩
    have least := spec.2.2 n lower color
    omega
  · intro upper
    exact ⟨parityCeil lo parity, spec.1, upper, spec.2.1⟩

#print axioms release_even_iff
#print axioms two_odd_transfer
#print axioms parity_interval_nonempty
end U1Improvement
