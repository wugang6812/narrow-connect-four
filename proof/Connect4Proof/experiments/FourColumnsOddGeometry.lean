import experiments.FourColumnsOddCore

namespace Connect4.FourColumns

/-- Only genuine in-bounds winning lines, with natural-number coordinates. -/
def FastFour (h : Nat) (b : Board 4) (p : Player) : Prop :=
  (∃ c : Fin 4, ∃ r : Fin (h-3), ∀ i : Fin 4,
    stone (b c) (r.val + i.val) = some p) ∨
  (∃ r : Fin h, ∀ c : Fin 4, stone (b c) r.val = some p) ∨
  (∃ r : Fin (h-3), ∀ c : Fin 4, stone (b c) (r.val + c.val) = some p) ∨
  (∃ r : Fin (h-3), ∀ c : Fin 4, stone (b c) (r.val + 3 - c.val) = some p)

instance fastFour_decidable (h : Nat) (b : Board 4) (p : Player) :
    Decidable (FastFour h b p) := by unfold FastFour; infer_instance

theorem fastFour_of_four {h : Nat} {b : Board 4} {p : Player}
    (hf : HasFour h b p) : FastFour h b p := by
  rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · have h0 : cellAtInt h b x y = some p := by simpa using hd 0
    have h3 : cellAtInt h b x (y+3) = some p := by simpa using hd 3
    obtain ⟨c, hx, hy, _, _⟩ := cellAtInt_some h0
    obtain ⟨_, _, _, hy3, _⟩ := cellAtInt_some h3
    left
    refine ⟨c, ⟨y.toNat, by omega⟩, ?_⟩
    intro i
    obtain ⟨d, hdx, hdy, _, hs⟩ := cellAtInt_some (hd i)
    have he : d = c := Fin.ext (by simp only [Int.mul_zero, Int.add_zero] at hdx; omega)
    have hr : (y + (i : Int) * 1).toNat = y.toNat + i.val := by omega
    simpa only [he, hr] using hs
  · have h0 : cellAtInt h b x y = some p := by simpa using hd 0
    have h3 : cellAtInt h b (x+3) y = some p := by simpa using hd 3
    obtain ⟨c0, hx0, hy, hyh, _⟩ := cellAtInt_some h0
    obtain ⟨c3, hx3, _, _, _⟩ := cellAtInt_some h3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx : x = 0 := by omega
    right; left
    refine ⟨⟨y.toNat, by omega⟩, ?_⟩
    intro c
    obtain ⟨d, hdx, _, _, hs⟩ := cellAtInt_some (hd c)
    have he : d = c := Fin.ext (by simp only [hx, Int.zero_add, Int.mul_one] at hdx; omega)
    simpa only [he, Int.mul_zero, Int.add_zero] using hs
  · have h0 : cellAtInt h b x y = some p := by simpa using hd 0
    have h3 : cellAtInt h b (x+3) (y+3) = some p := by simpa using hd 3
    obtain ⟨c0, hx0, hy, _, _⟩ := cellAtInt_some h0
    obtain ⟨c3, hx3, _, hy3, _⟩ := cellAtInt_some h3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx : x = 0 := by omega
    right; right; left
    refine ⟨⟨y.toNat, by omega⟩, ?_⟩
    intro c
    obtain ⟨d, hdx, _, _, hs⟩ := cellAtInt_some (hd c)
    have he : d = c := Fin.ext (by simp only [hx, Int.zero_add, Int.mul_one] at hdx; omega)
    have hr : (y + (c : Int) * 1).toNat = y.toNat + c.val := by omega
    simpa only [he, hr] using hs
  · have h0 : cellAtInt h b x y = some p := by simpa using hd 0
    have h3 : cellAtInt h b (x+3) (y-3) = some p := by
      simpa [sub_eq_add_neg] using hd (3 : Fin 4)
    obtain ⟨c0, hx0, _, hyh, _⟩ := cellAtInt_some h0
    obtain ⟨c3, hx3, hy3, _, _⟩ := cellAtInt_some h3
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    have hx : x = 0 := by omega
    right; right; right
    refine ⟨⟨(y-3).toNat, by omega⟩, ?_⟩
    intro c
    obtain ⟨d, hdx, _, _, hs⟩ := cellAtInt_some (hd c)
    have he : d = c := Fin.ext (by simp only [hx, Int.zero_add, Int.mul_one] at hdx; omega)
    have hcv := c.isLt
    have hr : (y + (c : Int) * (-1)).toNat = (y-3).toNat + 3 - c.val := by omega
    simpa only [he, hr] using hs

theorem four_of_fastFour {h : Nat} {b : Board 4} {p : Player}
    (hf : FastFour h b p) : HasFour h b p := by
  rcases hf with ⟨c, r, hd⟩ | ⟨r, hd⟩ | ⟨r, hd⟩ | ⟨r, hd⟩
  · left
    refine ⟨c, r, ?_⟩
    intro i
    have hr := r.isLt
    have hi := i.isLt
    have he : ((r : Int) + (i : Int) * 1).toNat = r.val + i.val := by omega
    apply cellAtInt_of_stone' (c := c) (by simp) (by omega) (by omega)
    rw [he]
    exact hd i
  · right; left
    refine ⟨0, r, ?_⟩
    intro c
    have hr := r.isLt
    apply cellAtInt_of_stone' (c := c) (by simp) (by omega) (by omega)
    simpa using hd c
  · right; right; left
    refine ⟨0, r, ?_⟩
    intro c
    have hr := r.isLt
    have hc := c.isLt
    have he : ((r : Int) + (c : Int) * 1).toNat = r.val + c.val := by omega
    apply cellAtInt_of_stone' (c := c) (by simp) (by omega) (by omega)
    rw [he]
    exact hd c
  · right; right; right
    refine ⟨0, (r : Int)+3, ?_⟩
    intro c
    have hr := r.isLt
    have hc := c.isLt
    have he : ((r : Int)+3 + (c : Int) * (-1)).toNat = r.val+3-c.val := by omega
    apply cellAtInt_of_stone' (c := c) (by simp) (by omega) (by omega)
    rw [he]
    exact hd c

theorem fastFour_iff {h : Nat} {b : Board 4} {p : Player} :
    FastFour h b p ↔ HasFour h b p := ⟨four_of_fastFour, fastFour_of_four⟩

#print axioms fastFour_iff

end Connect4.FourColumns
