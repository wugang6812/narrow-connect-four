import experiments.FourColumnsOddFinite
namespace Connect4.FourColumns
-- Intentionally false premise: compilation MUST fail.
example : Legal 1 (play (fourTuple [.black] [] [] []) 1 .white) 0 := by decide +kernel
end Connect4.FourColumns
