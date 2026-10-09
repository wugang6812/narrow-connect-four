import experiments.FourColumnsOddFinite

namespace Connect4.FourColumns

def flipFour (c : Fin 4) : Fin 4 := ⟨3 - c.val, by omega⟩
def mirrorFour (b : Board 4) : Board 4 := fun c => b (flipFour c)

@[simp] theorem flipFour_twice (c : Fin 4) : flipFour (flipFour c) = c := by
  apply Fin.ext
  have := c.isLt
  simp only [flipFour]
  omega

@[simp] theorem mirrorFour_twice (b : Board 4) : mirrorFour (mirrorFour b) = b := by
  funext c
  simp [mirrorFour]

theorem mirrorFour_play (b : Board 4) (c : Fin 4) (p : Player) :
    mirrorFour (play b c p) = play (mirrorFour b) (flipFour c) p := by
  funext d
  by_cases hd : d = flipFour c
  · subst d
    simp [mirrorFour, play_eq]
  · have hn : flipFour d ≠ c := by
      intro he
      have := congrArg flipFour he
      simp only [flipFour_twice] at this
      exact hd this
    simp only [mirrorFour, play_ne _ _ _ _ hd, play_ne _ _ _ _ hn]

theorem fastFour_mirror {h : Nat} {b : Board 4} {p : Player}
    (hf : FastFour h b p) : FastFour h (mirrorFour b) p := by
  rcases hf with ⟨c, r, ht⟩ | ⟨r, ht⟩ | ⟨r, ht⟩ | ⟨r, ht⟩
  · exact Or.inl ⟨flipFour c, r, by simpa [mirrorFour] using ht⟩
  · exact Or.inr (Or.inl ⟨r, fun c => ht (flipFour c)⟩)
  · right; right; right
    refine ⟨r, ?_⟩
    intro c
    have hc := c.isLt
    have he : r.val + 3 - c.val = r.val + (flipFour c).val := by
      simp only [flipFour]
      omega
    simpa only [mirrorFour, he] using ht (flipFour c)
  · right; right; left
    refine ⟨r, ?_⟩
    intro c
    have hc := c.isLt
    have he : r.val + 3 - (flipFour c).val = r.val + c.val := by
      simp only [flipFour]
      omega
    simpa only [mirrorFour, he] using ht (flipFour c)

@[simp] theorem hasFour_mirror_iff {h : Nat} {b : Board 4} {p : Player} :
    HasFour h (mirrorFour b) p ↔ HasFour h b p := by
  constructor
  · intro hf
    have := four_of_fastFour (fastFour_mirror (fastFour_of_four hf))
    simpa using this
  · exact fun hf => four_of_fastFour (fastFour_mirror (fastFour_of_four hf))

@[simp] theorem legal_mirror (h : Nat) (b : Board 4) (c : Fin 4) :
    Legal h (mirrorFour b) c ↔ Legal h b (flipFour c) := Iff.rfl

@[simp] theorem full_mirror (h : Nat) (b : Board 4) :
    BoardFull h (mirrorFour b) ↔ BoardFull h b := by
  constructor
  · intro hf c
    simpa [mirrorFour] using hf (flipFour c)
  · exact fun hf c => hf (flipFour c)

theorem valid_mirror {h : Nat} {b : Board 4} (hv : Valid h b) :
    Valid h (mirrorFour b) := fun c => hv (flipFour c)

@[simp] theorem totalStones_mirror (b : Board 4) :
    totalStones (mirrorFour b) = totalStones b := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  simp [totalStones, hu, mirrorFour, flipFour]
  omega

@[simp] theorem toMove_mirror (b : Board 4) : toMove (mirrorFour b) = toMove b := by
  simp [toMove]

@[simp] theorem play_mirror (b : Board 4) (c : Fin 4) (p : Player) :
    play (mirrorFour b) c p = mirrorFour (play b (flipFour c) p) := by
  rw [mirrorFour_play, flipFour_twice]

theorem ControlTree.mirror {cap score : Nat} {p : Player} {b : Board 4}
    (ht : ControlTree cap score p b) : ControlTree cap score p (mirrorFour b) := by
  induction ht with
  | won hn hw => exact .won (by simpa using hn) (by simpa using hw)
  | full hn hf => exact .full (by simpa using hn) (by simpa using hf)
  | @node b reply hv htm hn hchild hlegal hcap hnext ih =>
    let reply' : Fin 4 → Fin 4 := fun c => flipFour (reply (flipFour c))
    refine .node reply' (valid_mirror hv) (by simpa using htm) (by simpa using hn) ?_ ?_ ?_ ?_
    · intro c hc
      simpa using hchild (flipFour c) hc
    · intro c hc hf
      have hf' : ¬ BoardFull cap (play b (flipFour c) (opponent p)) := by
        simpa using hf
      simpa [reply'] using hlegal (flipFour c) hc hf'
    · intro c hc hf
      have hf' : ¬ BoardFull cap (play b (flipFour c) (opponent p)) := by
        simpa using hf
      rcases hcap (flipFour c) hc hf' with he | hs | hn
      · left
        simpa [reply'] using congrArg flipFour he
      · right; left
        simpa [mirrorFour] using hs
      · right; right
        simpa using hn
    · intro c hc hf
      have hf' : ¬ BoardFull cap (play b (flipFour c) (opponent p)) := by
        simpa using hf
      simpa [reply'] using ih (flipFour c) hc hf'

#print axioms ControlTree.mirror

end Connect4.FourColumns
