import experiments.FourColumnsOddFinite
namespace Connect4.FourColumns
-- Intentionally false premise: compilation MUST fail.
example : HasFour 6 (fourTuple [.black,.black,.black,.white,.black,.white,.black] [.black,.white,.black,.black,.white,.black,.white] [.white,.white,.white,.black,.black,.black,.white] [.white,.white,.white,.black]) .black := by decide +kernel
end Connect4.FourColumns
