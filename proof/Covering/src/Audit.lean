import HistoryRoots
import ReserveArithmetic
import SegmentBoundArithmetic
import U1LowerBounds
import ExecutableProbes

/-! Entry point for a trust-zero import replay of the full reviewed dependency
closure. Arithmetic-only U3 lemmas do not imply a verified compressed engine. -/
#print axioms UniformFour.U1.first_exact_controller_budget
#print axioms UniformFour.U1.second_exact_controller_budget
#print axioms UniformFour.U1.budgetSafe_iff_historyBudget
#print axioms UniformFour.U1.first_exact_history_budget
#print axioms UniformFour.U1.second_exact_history_budget
#print axioms UniformFour.U1.no_zero_first_history_policy
#print axioms UniformFour.U1.no_zero_second_history_policy
#print axioms UniformFour.U2.first_allSafe
#print axioms UniformFour.U2.second_allSafe
#print axioms UniformFour.U2.respond
#print axioms U1Improvement.release_even_iff
#print axioms U1Improvement.two_odd_transfer
#print axioms U1Improvement.parity_interval_nonempty
#print axioms U1Improvement.candidate_segment_bound
