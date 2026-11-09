import OddHeight.Support
import OddHeight.Strategy

/-! Executable permanent-controller obligations. Reviewed source.
Contains the local L4 closure argument, including the actual executable reply.
See audit.json and kernel_audit.json for the checked source hashes. -/
namespace OddHeight
open Player Col

/-- The actual permanent controller always finds a legal response on a nonfull board.
    It covers in the same column unless Q has filled that column. -/
theorem permanent_reply_exists {H : Nat} {b : Board} {q : Col}
    (hb : Bounded H b) (hq : Legal H b q)
    (hnot : ¬ Full H (drop b q Q)) :
    ∃ c, reply H b q .permanent = some (c, .permanent) ∧
      Legal H (drop b q Q) c ∧
      (c = q ∨ height (drop b q Q) q = H) := by
  have ha := drop_bounded hb hq Q
  by_cases hf : height (drop b q Q) q = H
  · rcases bounded_notFull_exists_legal ha hnot with ⟨c, hc⟩
    have hmem : c ∈ allCols := by cases c <;> simp [allCols]
    have hw : ∃ d ∈ allCols,
        height (drop b q Q) d < H ∧ inJ [] d = false :=
      ⟨c, hmem, hc, by simp [inJ]⟩
    rcases firstAvailable_complete hw with ⟨d, hd⟩
    have hs := firstAvailable_sound hd
    refine ⟨d, ?_, hs.1, Or.inr hf⟩
    simp [reply, rawReply, hf, hd, settle]
  · have hc : Legal H (drop b q Q) q := by
      have hbound := ha q
      unfold Legal
      omega
    refine ⟨q, ?_, hc, Or.inl rfl⟩
    have hf' : ¬ height b q + 1 = H := by simpa only [height_drop_same] using hf
    simp [reply, rawReply, hf', settle]

/-- Fixed P blockers persist through both moves of a round, with no parity assumption. -/
theorem permanent_blockers_preserved {H : Nat} {b : Board} {E : Cell → Prop}
    (blocked : ∀ L, ToCheck H E L → HasP b L) (q c : Col) :
    ∀ L, ToCheck H E L → HasP (drop (drop b q Q) c P) L := by
  intro L hL
  exact hasP_drop_preserves (hasP_drop_preserves (blocked L hL) q Q) c P

/-- P's response cannot create a Q win. This is separate from Q-move safety. -/
theorem P_response_preserves_noQ {H : Nat} {b : Board}
    (hn : ¬ Wins H b Q) (c : Col) : ¬ Wins H (drop b c P) Q := by
  intro hw
  exact hn (wins_drop_other_colour (by decide : Q ≠ P) c hw)

/-- Existing exceptions cannot be introduced by adding P. -/
theorem existing_exception_after_P {b : Board} {p : Col} {x : Cell}
    (hx : existingException (drop b p P) x) : existingException b x := by
  exact ⟨hx.1,
    stoneAt_drop_other_colour (by decide : Q ≠ P) p hx.2.1,
    stoneAt_drop_other_colour (by decide : Q ≠ P) p hx.2.2⟩

/-- A column to which P was just added cannot be Q-topped. -/
theorem no_Q_top_after_P (b : Board) (p : Col) :
    stoneAt (drop b p P) ⟨p, height (drop b p P) p⟩ ≠ some Q := by
  intro hq
  have ho := stoneAt_drop_other_colour (by decide : Q ≠ P) p hq
  have hb := (stoneAt_row_le ho).2
  change height (drop b p P) p ≤ height b p at hb
  rw [height_drop_same] at hb
  omega

/-- Under strict covering, every potential exception after the round was already
    potential before the round. Full Q columns create no potential exceptions. -/
theorem potential_exception_after_cover {H : Nat} {b : Board} {q p : Col}
    (cover : p = q ∨ height (drop b q Q) q = H) {x : Cell}
    (hx : potentialException H (drop (drop b q Q) p P) x) :
    potentialException H b x := by
  by_cases hxp : x.col = p
  · have ht := hx.2.2.2
    rw [hxp] at ht
    exact False.elim (no_Q_top_after_P (drop b q Q) p ht)
  by_cases hxq : x.col = q
  · rcases cover with he | he
    · exact False.elim (hxp (hxq.trans he.symm))
    · have heq : height (drop (drop b q Q) p P) x.col = H := by
        calc
          _ = height (drop b q Q) x.col := by simp [height, drop, hxp]
          _ = H := by simpa only [hxq] using he
      have hh := hx.2.1
      rw [heq] at hh
      omega
  · simpa [potentialException, stoneAt, height, drop, hxp, hxq] using hx

/-- The same complete E remains complete after a cover-or-full round. -/
theorem exceptionComplete_after_cover {H : Nat} {b : Board} {E : Cell → Prop}
    (complete : ExceptionComplete H b E) {q p : Col} (hq : Legal H b q)
    (cover : p = q ∨ height (drop b q Q) q = H) :
    ExceptionComplete H (drop (drop b q Q) p P) E := by
  intro x hx
  rcases hx with he | hp
  · exact complete x (existing_exception_after_Q hq (existing_exception_after_P he))
  · exact complete x (Or.inr (potential_exception_after_cover cover hp))

/-- Covering seals the newly extended Q run; a filled Q column cannot grow again. -/
theorem topRun_after_cover {H : Nat} {b : Board} {q p : Col}
    (htop : TopRunAtMostTwo H b)
    (cover : p = q ∨ height (drop b q Q) q = H) :
    TopRunAtMostTwo H (drop (drop b q Q) p P) := by
  intro c hc h3 hrun
  by_cases hcp : c = p
  · subst c
    exact no_Q_top_after_P (drop b q Q) p hrun.1
  by_cases hcq : c = q
  · rcases cover with he | he
    · exact hcp (hcq.trans he.symm)
    · have heq : height (drop (drop b q Q) p P) c = H := by
        calc
          _ = height (drop b q Q) c := by simp [height, drop, hcp]
          _ = H := by simpa only [hcq] using he
      omega
  · have hc' : height b c < H := by simpa [height, drop, hcp, hcq] using hc
    have h3' : 3 ≤ height b c := by simpa [height, drop, hcp, hcq] using h3
    apply htop c hc' h3'
    have hh : height (drop (drop b q Q) p P) c = height b c := by
      simp [height, drop, hcp, hcq]
    have hcell (r : Nat) : stoneAt (drop (drop b q Q) p P) ⟨c,r⟩ = stoneAt b ⟨c,r⟩ := by
      simp only [stoneAt, drop, if_neg hcp, if_neg hcq]
    simp only [hh, hcell] at hrun
    exact hrun

/-- L4's Q half-turn safety, using support descent and the vertical run bound. -/
theorem permanent_Q_move_safe {H : Nat} {b : Board} {E : Cell → Prop}
    (data : PermanentData H b E) (hnoP : ¬ Wins H b P)
    {q : Col} (hq : Legal H b q) : ¬ Wins H (drop b q Q) Q := by
  rintro ⟨L, hv, hall⟩
  cases L with
  | vertical c r =>
      exact vertical_Q_after_move_impossible hq data.structural.noQ
        data.structural.topRun c r hv hall
  | horizontal r =>
      exact blocked_exceptions_exclude_nonvertical_Q_after_move q hnoP
        (existing_exception_after_Q_in_E data.structural.complete hq)
        data.blocked hv trivial hall
  | rising r =>
      exact blocked_exceptions_exclude_nonvertical_Q_after_move q hnoP
        (existing_exception_after_Q_in_E data.structural.complete hq)
        data.blocked hv trivial hall
  | falling r =>
      exact blocked_exceptions_exclude_nonvertical_Q_after_move q hnoP
        (existing_exception_after_Q_in_E data.structural.complete hq)
        data.blocked hv trivial hall

/-- Full local structural closure for any legal cover-or-full response. -/
theorem structural_after_cover {H : Nat} {b : Board} {E : Cell → Prop}
    (hs : Structural H b E) {q p : Col} (hq : Legal H b q)
    (hp : Legal H (drop b q Q) p)
    (safeQ : ¬ Wins H (drop b q Q) Q)
    (cover : p = q ∨ height (drop b q Q) q = H) :
    Structural H (drop (drop b q Q) p P) E := by
  exact ⟨drop_bounded (drop_bounded hs.bounded hq Q) hp P,
    P_response_preserves_noQ safeQ p,
    topRun_after_cover hs.topRun cover,
    exceptionComplete_after_cover hs.complete hq cover⟩

/-- L4's invariant is preserved by the concrete permanent reply. -/
theorem permanent_local_step {H : Nat} {b : Board}
    (data : PermanentHyp H b) (hnoP : ¬ Wins H b P)
    {q : Col} (hq : Legal H b q) :
    ¬ Wins H (drop b q Q) Q ∧
    (Full H (drop b q Q) ∨ ∃ p,
      reply H b q .permanent = some (p, .permanent) ∧
      Legal H (drop b q Q) p ∧ PermanentHyp H (drop (drop b q Q) p P)) := by
  rcases data with ⟨E, data⟩
  have hs := permanent_Q_move_safe data hnoP hq
  refine ⟨hs, ?_⟩
  by_cases hf : Full H (drop b q Q)
  · exact Or.inl hf
  · right
    rcases permanent_reply_exists data.structural.bounded hq hf with ⟨p, hr, hp, hc⟩
    exact ⟨p, hr, hp, E,
      structural_after_cover data.structural hq hp hs hc,
      permanent_blockers_preserved data.blocked q p⟩

#print axioms permanent_reply_exists
#print axioms permanent_blockers_preserved
#print axioms permanent_local_step
end OddHeight
