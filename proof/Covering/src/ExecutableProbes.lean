import UniformFour.FiniteChecker

/-! Runtime comparison samples, NOT proof terms or a general equivalence theorem. -/
namespace U1ReviewProbes
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2
def samples : List (Nat × Board × Col × Col) := [
  (1, board [P] [Q] [] [], c2, c3),
  (1, board [Q] [] [] [], c1, c2),
  (1, board [Q] [P] [Q] [], c3, c4),
  (2, board [P,Q] [] [] [], c1, c2),
  (2, board [P,Q] [P,Q] [P] [Q], c4, c4),
  (2, board [Q] [] [] [], c1, c2),
  (2, board [Q,Q] [P] [] [], c1, c2),
  (2, board [Q,Q] [P,P] [Q] [], c3, c3),
  (2, board [Q] [P] [Q] [], c3, c3),
  (2, board [Q,Q] [P] [Q,P] [], c1, c2),
  (3, board [P,Q] [] [] [], c1, c1),
  (3, board [P,Q,P] [Q,P,Q] [] [], c2, c3),
  (3, board [Q] [] [] [], c1, c1),
  (3, board [Q,P,Q] [] [] [], c1, c2),
  (3, board [Q,P,Q] [P,Q] [] [], c2, c2),
  (3, board [Q,P,Q] [P,Q,P] [Q,P,Q] [], c3, c4),
  (3, board [Q,P] [Q] [] [], c2, c3),
  (3, board [Q,P] [] [] [Q], c4, c4),
  (3, board [] [Q] [] [], c2, c1),
  (3, board [P,Q] [Q] [] [], c1, c1),
  (3, board [P,Q,P] [Q,Q,P] [Q,P,Q] [P,Q], c4, c4),
  (4, board [P,Q] [] [] [], c1, c2),
  (4, board [P,Q,Q] [P] [] [], c1, c1),
  (4, board [P,Q,Q,P] [P,Q,P,Q] [] [], c2, c3),
  (4, board [P,Q,Q,P] [P,Q,P,Q] [P,Q] [], c3, c3),
  (4, board [P,Q,P,Q] [P,Q,P,Q] [Q,P,P,Q] [P,Q], c4, c4),
  (4, board [P] [] [Q] [], c3, c3),
  (4, board [Q] [] [] [], c1, c2),
  (4, board [Q,Q] [P] [] [], c1, c1),
  (4, board [Q,Q,P,Q] [P] [] [], c1, c2),
  (4, board [Q,Q,P,Q] [P,P,Q] [] [], c2, c2),
  (4, board [Q,Q,P,Q] [P,P,Q,P] [Q,P,Q] [], c3, c3),
  (4, board [Q,Q,P,Q] [P,Q,P] [Q,P] [], c1, c2),
  (4, board [Q,Q,P,Q] [P,Q,P] [Q,P,Q,P] [Q,P,Q,P], c1, c2),
  (5, board [P,Q] [] [] [], c1, c1),
  (5, board [P,Q,P,Q,P] [Q,P,Q,P,Q] [] [], c2, c4),
  (5, board [P,Q,P,Q,P] [Q,P,Q,P,Q] [Q] [P], c3, c3),
  (5, board [P,Q,P,Q,P] [Q,P,Q,P,Q] [Q,P,Q,P,Q] [P], c3, c4),
  (5, board [P,Q,P,Q,P] [Q,P,Q,P,Q] [Q,P] [], c2, c3),
  (5, board [P,Q,P,Q,P] [Q,P,Q,P,Q] [Q,P,P,Q] [], c3, c3),
  (5, board [Q] [] [] [], c1, c1),
  (5, board [Q,P,Q] [] [] [], c1, c1),
  (5, board [Q,P,Q,P,Q] [] [] [], c1, c3),
  (5, board [Q,P,Q,P,Q] [Q] [P] [], c2, c2),
  (5, board [Q,P,Q,P,Q] [Q,P,Q] [P] [], c2, c2),
  (5, board [Q,P,Q,P,Q] [Q,P,Q,P,Q] [P] [], c2, c4),
  (5, board [Q,P,Q,P] [Q] [] [], c2, c3),
  (5, board [Q,P,Q,P,Q] [Q] [P] [], c1, c4),
  (5, board [Q,P,Q] [Q] [P] [], c1, c1),
  (5, board [] [Q] [] [], c2, c1),
  (5, board [P,Q,P,Q,P] [Q,Q,P,Q,P] [Q,P,Q,P,Q] [P,Q], c4, c4),
  (6, board [P,Q] [] [] [], c1, c4),
  (6, board [P,Q,Q] [] [] [P], c1, c1),
  (6, board [P,Q,Q,P,Q,P] [Q,P,Q,P,Q] [] [P], c2, c2),
  (6, board [P,Q,Q,P,Q,P] [Q,P,Q,P,Q,P] [Q,P,Q,P,Q,P] [P,Q,P,Q], c4, c4),
  (6, board [P,Q,Q,P,Q,P] [Q,P,Q,P,Q,P] [Q,P,Q,P] [P,Q,P,Q,P,Q], c4, c3),
  (6, board [P,Q,Q,P,Q,P] [Q,P] [Q,P,Q,P,Q,P] [P,Q,P,Q,P,Q], c4, c2),
  (6, board [P,Q,Q,P,Q,P] [P,Q] [Q,P,Q,P,Q,P] [P,Q,P,Q,P,Q], c2, c2),
  (6, board [P,P,Q] [Q] [] [], c1, c1),
  (6, board [P,P,Q,P,Q] [Q] [] [], c1, c1),
  (6, board [P,P,Q,P,Q,P] [Q,Q,P,Q,P,Q] [] [], c2, c3),
  (6, board [P] [] [Q] [], c3, c3),
  (6, board [P,Q,P,Q,P,Q] [] [] [Q,P], c1, c2),
  (6, board [Q] [] [] [], c1, c2),
  (6, board [Q,Q] [P] [] [], c1, c1),
  (6, board [Q,Q,P,Q,P,Q] [P] [] [], c1, c2),
  (6, board [Q,Q,P,Q,P,Q] [P,P,Q,P,Q,P] [Q,P,Q] [], c3, c3),
  (6, board [Q,Q,P,Q,P,Q] [P,P,Q,P,Q,P] [Q,P,Q,P,Q] [], c3, c3),
  (6, board [Q,Q,P,Q,P,Q] [P,Q,P,Q,P] [Q,P] [], c1, c2),
  (6, board [Q,Q,P,Q,P,Q] [P,Q,P,Q,P] [Q,P,Q,P,Q,P] [Q,P,Q,P], c1, c2)
]

def verify : IO Unit := do
  for (H,b,q,expected) in samples do
    let actual := respond H b q
    if actual != some expected then
      throw (IO.userError s!"response mismatch at H={H}, q={repr q}, expected={repr expected}, actual={repr actual}")
  IO.println s!"All {samples.length} Lean/reference response probes passed."
#eval verify
end U1ReviewProbes
