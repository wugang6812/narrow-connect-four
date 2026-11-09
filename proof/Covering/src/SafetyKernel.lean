import OddHeight.Core

namespace UniformFour
open OddHeight OddHeight.Player

/-- Input board is BEFORE Q's move. The returned column is AFTER that move.
    The driver checks terminality before asking for a response. -/
abbrev Controller (S : Type) := Board → Col → S → Option (Col × S)

/-- The implementation interface used by U2: actual post-Q board and last column.
    There is no phase, role flag, height-parity flag, or remembered certificate. -/
abbrev StatelessResponse := Board → Col → Option Col

def stateless (f : StatelessResponse) : Controller Unit :=
  fun b q _ => (f (drop b q Q) q).map (fun c => (c, ()))

/-- A missing/illegal response is a failure, never a vacuously safe dead end.
    Q's first win is excluded BEFORE looking for the P response. -/
def RoundSafe {S : Type} (H : Nat) (f : Controller S) : Nat → Board → S → Prop
  | 0, b, _ => ¬ Wins H b Q
  | k + 1, b, s =>
      ¬ Wins H b Q ∧
      (Wins H b P ∨ Full H b ∨
        ∀ q, Legal H b q →
          ¬ Wins H (drop b q Q) Q ∧
          (Full H (drop b q Q) ∨
            ∃ c next,
              f b q s = some (c, next) ∧
              Legal H (drop b q Q) c ∧
              RoundSafe H f k (drop (drop b q Q) c P) next))

def Safe {S : Type} (H : Nat) (f : Controller S) (b : Board) (s : S) : Prop :=
  ∀ k, RoundSafe H f k b s


end UniformFour
