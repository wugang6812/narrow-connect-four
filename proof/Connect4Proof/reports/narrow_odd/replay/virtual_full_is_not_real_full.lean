import experiments.FourColumnsOddFinite
namespace Connect4.FourColumns
-- Intentionally false premise: compilation MUST fail.
example : BoardFull 9 (fourTuple (List.replicate 7 .black) (List.replicate 7 .black) (List.replicate 7 .black) (List.replicate 7 .black)) := by decide +kernel
end Connect4.FourColumns
