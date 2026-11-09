import OddHeight.Core

namespace OddHeight
def orient (flip : Bool) (c : Col) : Col := if flip then mirror c else c
def logicalBoard (flip : Bool) (b : Board) : Board := fun c => b (orient flip c)
end OddHeight

namespace Connect4.NarrowBoards.OddHeightDraft
open OddHeight.Col

@[simp] theorem logicalBoard_twice (b : OddHeight.Board) :
    OddHeight.logicalBoard true (OddHeight.logicalBoard true b) = b := by
  funext c
  simp [OddHeight.logicalBoard, OddHeight.orient]

@[simp] theorem logicalBoard_stone (b : OddHeight.Board) (c : OddHeight.Col) (r : Nat) :
    OddHeight.stoneAt (OddHeight.logicalBoard true b) ⟨c, r⟩ =
      OddHeight.stoneAt b ⟨OddHeight.mirror c, r⟩ := by
  simp [OddHeight.stoneAt, OddHeight.logicalBoard, OddHeight.orient]

/-- Geometric reflection reverses the four cells and swaps the diagonal slopes. -/
theorem wins_logicalBoard {H : Nat} {b : OddHeight.Board} {p : OddHeight.Player}
    (win : OddHeight.Wins H b p) : OddHeight.Wins H (OddHeight.logicalBoard true b) p := by
  rcases win with ⟨L, valid, stones⟩
  have good : ∀ z ∈ L.cells, OddHeight.InBoard H z ∧ OddHeight.stoneAt b z = some p :=
    fun z hz => ⟨valid z hz, stones z hz⟩
  have assemble : ∀ M : OddHeight.Line,
      (∀ z ∈ M.cells, OddHeight.InBoard H z ∧
        OddHeight.stoneAt (OddHeight.logicalBoard true b) z = some p) →
      OddHeight.Wins H (OddHeight.logicalBoard true b) p := by
    intro M h
    exact ⟨M, fun z hz => (h z hz).1, fun z hz => (h z hz).2⟩
  cases L with
  | horizontal r =>
      apply assemble (.horizontal r)
      intro z hz
      simp only [OddHeight.Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [OddHeight.mirror, OddHeight.InBoard] using good ⟨c4, r⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.mirror, OddHeight.InBoard] using good ⟨c3, r⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.mirror, OddHeight.InBoard] using good ⟨c2, r⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.mirror, OddHeight.InBoard] using good ⟨c1, r⟩ (by simp [OddHeight.Line.cells])
  | vertical c r =>
      apply assemble (.vertical (OddHeight.mirror c) r)
      intro z hz
      simp only [OddHeight.Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [OddHeight.InBoard] using good ⟨c, r⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.InBoard] using good ⟨c, r + 1⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.InBoard] using good ⟨c, r + 2⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.InBoard] using good ⟨c, r + 3⟩ (by simp [OddHeight.Line.cells])
  | rising r =>
      apply assemble (.falling (r + 3))
      intro z hz
      simp only [OddHeight.Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [OddHeight.mirror, OddHeight.InBoard] using
          good ⟨c4, r + 3⟩ (by simp [OddHeight.Line.cells])
      · have hr : r + 3 - 1 = r + 2 := by omega
        simpa [OddHeight.mirror, OddHeight.InBoard, hr] using
          good ⟨c3, r + 2⟩ (by simp [OddHeight.Line.cells])
      · have hr : r + 3 - 2 = r + 1 := by omega
        simpa [OddHeight.mirror, OddHeight.InBoard, hr] using
          good ⟨c2, r + 1⟩ (by simp [OddHeight.Line.cells])
      · simpa [OddHeight.mirror, OddHeight.InBoard] using
          good ⟨c1, r⟩ (by simp [OddHeight.Line.cells])
  | falling r =>
      have hr : 1 ≤ r - 3 := (valid ⟨c4, r - 3⟩ (by simp [OddHeight.Line.cells])).1
      apply assemble (.rising (r - 3))
      intro z hz
      simp only [OddHeight.Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [OddHeight.mirror, OddHeight.InBoard] using
          good ⟨c4, r - 3⟩ (by simp [OddHeight.Line.cells])
      · have he : r - 3 + 1 = r - 2 := by omega
        simpa [OddHeight.mirror, OddHeight.InBoard, he] using
          good ⟨c3, r - 2⟩ (by simp [OddHeight.Line.cells])
      · have he : r - 3 + 2 = r - 1 := by omega
        simpa [OddHeight.mirror, OddHeight.InBoard, he] using
          good ⟨c2, r - 1⟩ (by simp [OddHeight.Line.cells])
      · have he : r - 3 + 3 = r := by omega
        simpa [OddHeight.mirror, OddHeight.InBoard, he] using
          good ⟨c1, r⟩ (by simp [OddHeight.Line.cells])

theorem wins_logicalBoard_iff (H : Nat) (b : OddHeight.Board) (p : OddHeight.Player) :
    OddHeight.Wins H (OddHeight.logicalBoard true b) p ↔ OddHeight.Wins H b p := by
  constructor
  · intro h
    simpa using wins_logicalBoard h
  · exact wins_logicalBoard


end Connect4.NarrowBoards.OddHeightDraft
