import OddHeight.Core

/-! Arithmetic end of the improved U3 bound. The geometric/event-counting
premises are explicit. This file does NOT formalize the injection from adjacent
equal stones to switches or the maximal-alternating-segment representation.
See the accompanying mathematical proof for those remaining steps. -/
namespace U1Improvement

theorem candidate_segment_bound {width active passive sameP sameQ occupied
    current candidate allowance : Nat}
    (positive : 0 < width) (activeBound : active ≤ allowance)
    (passiveBound : passive < width)
    (pPairs : sameP ≤ active+passive) (qPairs : sameQ ≤ active)
    (columns : occupied ≤ width) (segments : current = occupied+sameP+sameQ)
    (oneStone : candidate ≤ current+1)
    (lastColumn : passive+1 = width → candidate ≤ current) :
    candidate ≤ 2*width-1+2*allowance := by
  by_cases last : passive+1 = width
  · have noNew := lastColumn last
    omega
  · omega

theorem four_column_candidate_nine {active passive sameP sameQ occupied
    current candidate : Nat}
    (activeBound : active ≤ 1) (passiveBound : passive < 4)
    (pPairs : sameP ≤ active+passive) (qPairs : sameQ ≤ active)
    (columns : occupied ≤ 4) (segments : current = occupied+sameP+sameQ)
    (oneStone : candidate ≤ current+1)
    (lastColumn : passive = 3 → candidate ≤ current) : candidate ≤ 9 := by
  apply candidate_segment_bound (width := 4) (allowance := 1)
    (by decide) activeBound passiveBound pPairs qPairs columns segments oneStone
  intro h
  exact lastColumn (by omega)

#print axioms candidate_segment_bound
end U1Improvement
