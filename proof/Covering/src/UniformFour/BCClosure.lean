import UniformFour.RoundFacts

/-!
U2 B closure, including BOTH orders of the two odd columns.
These are actual current-board proofs, not assumed future closure fields.
Reviewed local copy; validation is recorded in audit.json and kernel_audit.json.
-/
namespace UniformFour.U2
open OddHeight OddHeight.Player OddHeight.Col

theorem protected_after_cover {H : Nat} {b : Board} {x : Cell}
    (h : Protected H b x) (q : Col) :
    Protected H (afterRound b q q) x := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with fixed | ⟨_, pos, even⟩
  · exact Or.inl (stoneAt_drop_preserves (stoneAt_drop_preserves fixed q Q) q P)
  · by_cases same : x.col = q
    · have ht : height (afterRound b q q) x.col = height b x.col + 2 := by
        rw [same]
        simp [afterRound, Nat.add_assoc]
      by_cases hit : x.row = height b x.col + 2
      · left
        have row : x.row = height (drop b q Q) q + 1 := by
          rw [height_drop_same, ← same]
          omega
        have eq : x = ⟨q, height (drop b q Q) q + 1⟩ := by
          cases x with
          | mk c r => exact (congrArg (fun k => Cell.mk k r) same).trans (congrArg (Cell.mk q) row)
        rw [eq]
        exact candidate_stoneAt_new_top (drop b q Q) q P
      · right
        have newpos : height (afterRound b q q) x.col < x.row := by omega
        exact ⟨cell_empty_above_height newpos, newpos, by omega⟩
    · have ht : height (afterRound b q q) x.col = height b x.col := by
        simp [height, drop, same]
      right
      exact ⟨cell_empty_above_height (by omega), by omega, by omega⟩

theorem remainder_cover_mod {H : Nat} {b : Board} {q : Col}
    (hp : Legal H (drop b q Q) q) (c : Col) :
    (H - height (afterRound b q q) c) % 2 = (H - height b c) % 2 := by
  by_cases same : c = q
  · subst c
    have room : height b q + 2 ≤ H := by
      unfold Legal at hp
      rw [height_drop_same] at hp
      omega
    simp only [height_drop_same]
    omega
  · simp [height, drop, same]

theorem odd_columns_cover {H : Nat} {b : Board} {q : Col}
    (hp : Legal H (drop b q Q) q) :
    oddColumns H (afterRound b q q) = oddColumns H b := by
  unfold oddColumns
  apply congrArg (fun f : Col → Bool => allCols.filter f)
  funext c
  rw [remainder_cover_mod hp c]

theorem odd_column_cover_iff {H : Nat} {b : Board} {q : Col}
    (hp : Legal H (drop b q Q) q) (c : Col) :
    OddColumn H (afterRound b q q) c ↔ OddColumn H b c := by
  unfold OddColumn
  rw [remainder_cover_mod hp c]

theorem b_cover_body {H : Nat} {b : Board} {q : Col}
    (h : B H b) (hq : Legal H b q) (hp : Legal H (drop b q Q) q) :
    B H (afterRound b q q) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [odd_columns_cover hp]
    exact h.zeroOrTwo
  · intro L hL
    rcases h.guards L (unresolved_after_cover_subset hq (Or.inl rfl) hL) with ⟨x, hx, hg⟩
    exact ⟨x, hx, protected_after_cover hg q⟩
  · intro f t ne hf ht L hL
    rcases h.bothOrderedExits f t ne ((odd_column_cover_iff hp f).mp hf)
      ((odd_column_cover_iff hp t).mp ht) L
      (unresolved_after_cover_subset hq (Or.inl rfl) hL) with ⟨x, hx, guard⟩
    refine ⟨x, hx, ?_⟩
    rcases guard with ⟨hg, out⟩ | roof
    · exact Or.inl ⟨protected_after_cover hg q, out⟩
    · exact Or.inr roof

theorem b_cover_good {H : Nat} {b : Board} {q : Col}
    (common : Common H b) (h : B H b) (hq : Legal H b q)
    (hp : Legal H (drop b q Q) q) : Good H (afterRound b q q) := by
  apply good_of_structural
    (structural_after_cover (common_structural common) hq hp
      (b_Q_move_safe common h hq) (Or.inl rfl))
  intro _ _
  exact Or.inr (Or.inl (b_cover_body h hq hp))

/-- The length condition is used, rather than silently assuming a second odd
column. The output also proves uniqueness, in all four column positions. -/
theorem b_other_odd {H : Nat} {b : Board} (h : B H b) {f : Col}
    (hf : OddColumn H b f) :
    ∃ t, f ≠ t ∧ ∀ c, OddColumn H b c ↔ c = f ∨ c = t := by
  have count := h.zeroOrTwo
  cases f <;>
    by_cases h1 : OddColumn H b c1 <;>
    by_cases h2 : OddColumn H b c2 <;>
    by_cases h3 : OddColumn H b c3 <;>
    by_cases h4 : OddColumn H b c4 <;>
    simp_all [OddColumn, oddColumns, allCols]
  all_goals solve
    | (refine ⟨c1, by decide, ?_⟩; intro c; cases c <;> simp_all [OddColumn])
    | (refine ⟨c2, by decide, ?_⟩; intro c; cases c <;> simp_all [OddColumn])
    | (refine ⟨c3, by decide, ?_⟩; intro c; cases c <;> simp_all [OddColumn])
    | (refine ⟨c4, by decide, ?_⟩; intro c; cases c <;> simp_all [OddColumn])

theorem full_move_was_odd {H : Nat} {b : Board} {f : Col}
    (hq : Legal H b f) (full : height (drop b f Q) f = H) :
    OddColumn H b f := by
  unfold OddColumn
  rw [height_drop_same] at full
  unfold Legal at hq
  omega

theorem odd_other_legal {H : Nat} {b : Board} {f t : Col}
    (ne : f ≠ t) (ht : OddColumn H b t) : Legal H (drop b f Q) t := by
  have lt := (odd_column_top_empty ht).1
  simpa [Legal, height, drop, Ne.symm ne] using lt

theorem protected_outside_full_transfer {H : Nat} {b : Board} {f t : Col}
    (full : height (drop b f Q) f = H) {x : Cell}
    (h : Protected H b x) (outside : x.col ≠ t) :
    Protected H (afterRound b f t) x := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with fixed | ⟨_, pos, even⟩
  · exact Or.inl (stoneAt_drop_preserves (stoneAt_drop_preserves fixed f Q) t P)
  · have not_f : x.col ≠ f := by
      intro same
      have bound := h.1.2
      rw [height_drop_same] at full
      rw [same] at pos even
      omega
    have ht : height (afterRound b f t) x.col = height b x.col := by
      simp [height, drop, outside, not_f]
    right
    exact ⟨cell_empty_above_height (by omega), by omega, by omega⟩

theorem roof_protected_after_transfer {H : Nat} {b : Board} {f t : Col}
    (ne : f ≠ t) (odd : OddColumn H b t) :
    Protected H (afterRound b f t) ⟨t, H⟩ := by
  have old := odd_column_top_empty odd
  have hodd := odd
  unfold OddColumn at hodd
  have ht : height (afterRound b f t) t = height b t + 1 := by
    simp [height, drop, Ne.symm ne]
  refine ⟨old.2.1, ?_⟩
  by_cases hit : H = height b t + 1
  · left
    have before : height (drop b f Q) t = height b t := by
      simp [height, drop, Ne.symm ne]
    have cell : (⟨t, H⟩ : Cell) = ⟨t, height (drop b f Q) t + 1⟩ := by
      rw [before, hit]
    rw [cell]
    exact candidate_stoneAt_new_top (drop b f Q) t P
  · right
    have pos : height (afterRound b f t) t < H := by
      have lt := old.1
      unfold Legal at lt
      omega
    exact ⟨cell_empty_above_height pos, pos, by (try dsimp only); omega⟩

theorem exit_protected_after_full {H : Nat} {b : Board} {f t : Col}
    (ne : f ≠ t) (full : height (drop b f Q) f = H)
    (odd : OddColumn H b t) {x : Cell} (h : ExitProtected H b t x) :
    Protected H (afterRound b f t) x := by
  rcases h with ⟨guard, outside⟩ | roof
  · exact protected_outside_full_transfer full guard outside
  · subst x
    exact roof_protected_after_transfer ne odd

theorem full_transfer_all_even {H : Nat} {b : Board} {f t : Col}
    (ne : f ≠ t) (full : height (drop b f Q) f = H)
    (pair : ∀ c, OddColumn H b c ↔ c = f ∨ c = t) :
    ∀ c, (H - height (afterRound b f t) c) % 2 = 0 := by
  intro c
  by_cases cf : c = f
  · subst c
    have final : height (afterRound b f t) f = H := by
      simpa [height, drop, ne] using full
    rw [final]
    simp
  by_cases ct : c = t
  · subst c
    have odd : (H - height b t) % 2 = 1 := (pair t).mpr (Or.inr rfl)
    have ht : height (afterRound b f t) t = height b t + 1 := by
      simp [height, drop, Ne.symm ne]
    rw [ht]
    omega
  · have old : ¬ OddColumn H b c := by
      intro odd
      rcases (pair c).mp odd with eq | eq
      · exact cf eq
      · exact ct eq
    have ht : height (afterRound b f t) c = height b c := by
      simp [height, drop, cf, ct]
    unfold OddColumn at old
    rw [ht]
    omega

theorem odd_columns_nil_of_even {H : Nat} {b : Board}
    (even : ∀ c, (H - height b c) % 2 = 0) : oddColumns H b = [] := by
  simp [oddColumns, allCols, even c1, even c2, even c3, even c4]

/-- f and t are ordered arguments. Reversing them invokes the OTHER exit field
of B; there is no fixed choice of which odd column fills first. -/
theorem b_full_body {H : Nat} {b : Board} {f t : Col}
    (h : B H b) (hq : Legal H b f) (ne : f ≠ t)
    (full : height (drop b f Q) f = H)
    (pair : ∀ c, OddColumn H b c ↔ c = f ∨ c = t) :
    B H (afterRound b f t) := by
  have hf : OddColumn H b f := (pair f).mpr (Or.inl rfl)
  have ht : OddColumn H b t := (pair t).mpr (Or.inr rfl)
  have even := full_transfer_all_even ne full pair
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · rw [odd_columns_nil_of_even even]
    rfl
  · intro L hL
    rcases h.bothOrderedExits f t ne hf ht L
      (unresolved_after_cover_subset hq (Or.inr full) hL) with ⟨x, hx, guard⟩
    exact ⟨x, hx, exit_protected_after_full ne full ht guard⟩
  · intro f' t' _ odd _
    have noodd := even f'
    unfold OddColumn at odd
    omega

theorem b_full_good {H : Nat} {b : Board} {f t : Col}
    (common : Common H b) (h : B H b) (hq : Legal H b f)
    (ne : f ≠ t) (full : height (drop b f Q) f = H)
    (pair : ∀ c, OddColumn H b c ↔ c = f ∨ c = t) :
    Legal H (drop b f Q) t ∧ Good H (afterRound b f t) := by
  have hp := odd_other_legal ne ((pair t).mpr (Or.inr rfl))
  refine ⟨hp, ?_⟩
  apply good_of_structural
    (structural_after_cover (common_structural common) hq hp
      (b_Q_move_safe common h hq) (Or.inr full))
  intro _ _
  exact Or.inr (Or.inl (b_full_body h hq ne full pair))

theorem b_full_reply_exists {H : Nat} {b : Board} {f : Col}
    (common : Common H b) (h : B H b) (hq : Legal H b f)
    (full : height (drop b f Q) f = H) :
    ∃ t, f ≠ t ∧ Legal H (drop b f Q) t ∧
      OddColumn H (drop b f Q) t ∧ Good H (afterRound b f t) ∧
      ∀ c, OddColumn H (drop b f Q) c ↔ c = t := by
  rcases b_other_odd h (full_move_was_odd hq full) with ⟨t, ne, pair⟩
  have ht : OddColumn H b t := (pair t).mpr (Or.inr rfl)
  have good := b_full_good common h hq ne full pair
  have unique : ∀ c, OddColumn H (drop b f Q) c ↔ c = t := by
    intro c
    by_cases cf : c = f
    · subst c
      simp only [OddColumn, full, Nat.sub_self, Nat.zero_mod]
      simp [ne]
    · have eq : height (drop b f Q) c = height b c := by simp [height, drop, cf]
      change (H - height (drop b f Q) c) % 2 = 1 ↔ c = t
      rw [eq]
      have pp := pair c
      simpa only [OddColumn, cf, false_or] using pp
  exact ⟨t, ne, good.1, (unique t).mpr rfl, good.2, unique⟩

/-- The complete B existence theorem: a cover if legal, otherwise the UNIQUE
remaining odd column. Immediate wins/full terminals are accepted by Good. -/
theorem b_reply_exists {H : Nat} {b : Board} {q : Col}
    (common : Common H b) (h : B H b) (hq : Legal H b q) :
    ∃ p, Legal H (drop b q Q) p ∧ Good H (afterRound b q p) := by
  by_cases hp : Legal H (drop b q Q) q
  · exact ⟨q, hp, b_cover_good common h hq hp⟩
  · have bound := drop_bounded common.1.1 hq Q q
    have full : height (drop b q Q) q = H := by unfold Legal at hp; omega
    rcases b_full_reply_exists common h hq full with ⟨t, _, legal, _, good, _⟩
    exact ⟨t, legal, good⟩

end UniformFour.U2
