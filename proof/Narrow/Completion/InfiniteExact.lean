import Completion.InfiniteCost

namespace Connect4.InfiniteNarrowBoards.Cost

private theorem sparse_no_four {b : Board 4}
    (low : ∀ c, (b c).length ≤ 2) (last : b 3 = []) (p : Player) : ¬ HasFour b p := by
  rintro ⟨H, four⟩
  have across {x y dy : Int} (line : FourColumns.HasFourDir H b p x y 1 dy) : False := by
    have left : cellAtInt H b x y = some p := by simpa using line 0
    have right : cellAtInt H b (x+3) (y+3*dy) = some p := by simpa using line 3
    obtain ⟨a, ha, _, _, _⟩ := cellAtInt_some left
    obtain ⟨c, hc, _, _, stone⟩ := cellAtInt_some right
    have := a.isLt
    have := c.isLt
    have he : c = 3 := Fin.ext (by change c.val = 3; omega)
    have bound := FourColumns.stone_bound _ _ _ stone
    rw [he, last] at bound
    exact Nat.not_lt_zero _ bound
  rcases four with ⟨x,y,line⟩ | ⟨x,y,line⟩ | ⟨x,y,line⟩ | ⟨x,y,line⟩
  · have bottom : cellAtInt H b x y = some p := by simpa using line 0
    have top : cellAtInt H b x (y+3) = some p := by simpa using line 3
    obtain ⟨_, _, hy, _, _⟩ := cellAtInt_some bottom
    obtain ⟨c, _, _, _, stone⟩ := cellAtInt_some top
    have bound := FourColumns.stone_bound _ _ _ stone
    have := low c
    omega
  all_goals exact across line

private theorem attack {s : Strategy 4} (safe : SafePolicy .white s)
    {hist b n} (path : Run .white s hist b n) (own : ¬ HasFour b .white)
    (turn : toMove b = .black) (q : Fin 4) :
    Run .white s (q :: hist) (play b q .black) n := by
  have child := Run.step (c := q) path own (safe_on_run safe path 0)
    (fun bad => False.elim (by rw [turn] at bad; cases bad))
  simpa [turn] using child

private theorem forced_cover {s : Strategy 4} (ach : Achieves .white s 0)
    {hist b} {q : Fin 4} (path : Run .white s (q :: hist) b 0)
    (own : ¬ HasFour b .white) (turn : toMove b = .white) :
    Run .white s (q :: q :: hist) (play b q .white) 0 := by
  let p := s (q :: hist)
  have child := Run.step (c := p) path own (safe_on_run ach.1 path 0) (fun _ => rfl)
  have cost := ach.2 _ _ _ child
  have eq : p = q := by
    by_contra different
    simp [turn, switch, different] at cost
  simpa only [eq, turn, ite_true, switch, ite_self, Nat.add_zero, ↓reduceIte] using child

theorem white_zero_impossible (s : Strategy 4) : ¬ Achieves .white s 0 := by
  intro ach
  let b0 := emptyBoard 4
  have r0 : Run .white s [] b0 0 := Run.start
  let b1 := play b0 (0 : Fin 4) .black
  have no0 : ¬ HasFour b0 .white := sparse_no_four (by decide) (by decide) _
  have r1 := attack ach.1 r0 no0 (by decide) 0
  let b2 := play b1 (0 : Fin 4) .white
  have no1 : ¬ HasFour b1 .white := sparse_no_four (by decide) (by decide) _
  have r2 := forced_cover ach r1 no1 (by decide)
  let b3 := play b2 (1 : Fin 4) .black
  have no2 : ¬ HasFour b2 .white := sparse_no_four (by decide) (by decide) _
  have r3 := attack ach.1 r2 no2 (by decide) 1
  let b4 := play b3 (1 : Fin 4) .white
  have no3 : ¬ HasFour b3 .white := sparse_no_four (by decide) (by decide) _
  have r4 := forced_cover ach r3 no3 (by decide)
  let b5 := play b4 (2 : Fin 4) .black
  have no4 : ¬ HasFour b4 .white := sparse_no_four (by decide) (by decide) _
  have r5 := attack ach.1 r4 no4 (by decide) 2
  let b6 := play b5 (2 : Fin 4) .white
  have no5 : ¬ HasFour b5 .white := sparse_no_four (by decide) (by decide) _
  have r6 := forced_cover ach r5 no5 (by decide)
  let b7 := play b6 (3 : Fin 4) .black
  have no6 : ¬ HasFour b6 .white := sparse_no_four (by decide) (by decide) _
  have r7 := attack ach.1 r6 no6 (by decide) 3
  have won : HasFour b7 .black := by
    refine ⟨1, Or.inr (Or.inl ⟨0,0,?_⟩)⟩
    intro i
    fin_cases i <;> decide
  exact (safe_on_run ach.1 r7 0) won

theorem narrow_infinite_exact {w : Nat} (pos : 0 < w) (hw : w ≤ 3) (p : Player) :
    Exact w p 0 := by
  let first : Fin w := ⟨0,pos⟩
  refine ⟨⟨coverStrategy first, ?_, ?_⟩,fun _ _ _ => Nat.zero_le _⟩
  · cases p
    · exact narrow_black_nonloss_fixed first hw
    · exact narrow_white_nonloss_fixed first hw
  · intro hist b n path
    exact Nat.le_of_eq (cover_zero (fun _ _ => rfl) path)

theorem four_infinite_first_exact : Exact 4 .black 0 := by
  refine ⟨⟨blackStrategy, black_nonloss_fixed, ?_⟩, fun _ _ _ => Nat.zero_le _⟩
  intro hist b n path
  exact Nat.le_of_eq (cover_zero (fun _ _ => rfl) path)

theorem four_infinite_second_exact : Exact 4 .white 1 := by
  refine ⟨⟨whiteStrategy, white_nonloss_fixed, ?_⟩, ?_⟩
  · intro hist b n path
    have bound := white_cost path
    split at bound <;> omega
  · intro s n ach
    cases n with
    | zero => exact False.elim (white_zero_impossible s ach)
    | succ n => omega

#print axioms narrow_infinite_exact
#print axioms four_infinite_first_exact
#print axioms four_infinite_second_exact
end Connect4.InfiniteNarrowBoards.Cost
