import BudgetTools
import UniformFour.SecondRoot

/-! Reviewed candidate: the actual U2 selector, with its exact priority,
uses at most one active reply from the second-player root. No safety or
budget closure is assumed. Requires BudgetTools from u1_upper_work. -/
namespace UniformFour.U1
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U2

def ABCert (H : Nat) (b : Board) : Prop := Common H b ∧ (A H b ∨ B H b)

theorem ab_certificate {H : Nat} {b : Board} (h : ABCert H b) : Certificate H b := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with a | b
  · exact Or.inl a
  · exact Or.inr (Or.inl b)

/-- Strengthen the existing cover lemmas only in their geometric conclusion. -/
theorem ab_cover_body {H : Nat} {b : Board} {q : Col}
    (h : ABCert H b) (hq : Legal H b q) (hp : Legal H (drop b q Q) q)
    (noP : ¬ Wins H (afterRound b q q) P) (notFull : ¬ Full H (afterRound b q q)) :
    A H (afterRound b q q) ∨ B H (afterRound b q q) := by
  rcases h.2 with ha | hb
  · left
    rcases ha with h0 | ⟨t,h1⟩ | ⟨t,h2⟩
    · exact Or.inl (a0_cover_closed h.1 h0 hq hp (Or.inl rfl) noP notFull).2
    · have policy : TargetRound H b t q q := ⟨fun _ => rfl, fun ne => ne⟩
      rcases target_after_round h1.target hq hp policy with hit | keep
      · exact Or.inl (a1_capture_is_a0 h1 hq (Or.inl rfl) hit)
      · refine Or.inr (Or.inl ⟨t, keep, ?_⟩)
        intro L unresolved
        exact h1.commonTarget L (unresolved_after_cover_subset hq (Or.inl rfl) unresolved)
    · have policy : TargetRound H b t q q := ⟨fun _ => rfl, fun ne => ne⟩
      rcases target_after_round h2.target hq hp policy with hit | keep
      · exact False.elim (noP (a2_capture_wins q q h2 hit))
      · refine Or.inr (Or.inr ⟨t, keep, fixedWinningTarget_preserved h2.fixedWin q q, ?_⟩)
        intro L unresolved
        exact h2.commonUpperColumn L (unresolved_after_cover_subset hq (Or.inl rfl) unresolved)
  · exact Or.inr (b_cover_body hb hq hp)

/-- A full old column permanently rules out C after any legal response. -/
theorem full_reply_not_C {H : Nat} {b : Board} {q p : Col}
    (full : height (drop b q Q) q = H) (hp : Legal H (drop b q Q) p) :
    ¬ C H (afterRound b q p) := by
  have ne : q ≠ p := by
    intro eq
    subst p
    change height (drop b q Q) q < H at hp
    omega
  have heightQ : height (afterRound b q p) q = H := by
    simpa [afterRound, height, drop, ne] using full
  intro hc
  have odd := hc.fourOdd q
  simp [OddColumn, heightQ] at odd

/-- Actual selection is zero-cost on A/B and retains A/B unless terminal. -/
theorem ab_selected_step {H : Nat} {b : Board} {q p : Col}
    (h : ABCert H b) (hq : Legal H b q) (nf : ¬ Full H (drop b q Q))
    (chosen : select H (drop b q Q) q (referenceObservation H (drop b q Q)) = some p) :
    activeCost H (drop b q Q) q p = 0 ∧
      (SafeTerminal H (afterRound b q p) ∨ ABCert H (afterRound b q p)) := by
  have obs := referenceObserves H (drop b q Q)
  have good := certificate_selected_good (ab_certificate h) hq nf obs chosen
  by_cases available : Legal H (drop b q Q) q
  · have coverGood : Good H (afterRound b q q) := by
      rcases h.2 with ha | hb
      · exact a_cover_good h.1 ha hq available
      · exact b_cover_good h.1 hb hq available
    have same := select_cover_of_qualified obs ⟨available, coverGood⟩
    have eq : p = q := Option.some.inj (chosen.symm.trans same)
    subst p
    refine ⟨activeCost_self H _ q, ?_⟩
    rcases good.2 with terminal | cert
    · exact Or.inl terminal
    · exact Or.inr ⟨cert.1, ab_cover_body h hq available cert.1.1.2.1 cert.1.1.2.2.2⟩
  · refine ⟨activeCost_of_unavailable available, ?_⟩
    rcases good.2 with terminal | cert
    · exact Or.inl terminal
    · have bounded := drop_bounded h.1.1.1 hq Q q
      have full : height (drop b q Q) q = H := by
        change ¬ height (drop b q Q) q < H at available
        omega
      refine Or.inr ⟨cert.1, ?_⟩
      rcases cert.2 with ha | hb | hc
      · exact Or.inl ha
      · exact Or.inr hb
      · exact False.elim (full_reply_not_C full good.1 hc)

theorem ab_budget_zero {H : Nat} {b : Board} (h : ABCert H b) :
    BudgetSafe H (stateless (respond H)) 0 b () := by
  intro k
  induction k generalizing b with
  | zero => exact h.1.1.2.2.1
  | succ k ih =>
    refine ⟨h.1.1.2.2.1, Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨certificate_Q_move_safe (ab_certificate h) hq, ?_⟩
    by_cases full : Full H (drop b q Q)
    · exact Or.inl full
    · rcases select_total_legal (q := q) (o := referenceObservation H (drop b q Q))
        (drop_bounded h.1.1.1 hq Q) full with ⟨p, chosen, legal⟩
      have step := ab_selected_step h hq full chosen
      refine Or.inr ⟨p, (), ?_, legal, ?_, ?_⟩
      · simp only [stateless, respond, chosen, Option.map_some]
      · simp [step.1]
      · rw [step.1, Nat.sub_zero]
        rcases step.2 with terminal | child
        · exact budget_terminal terminal k 0 ()
        · exact ih child

/-- An active departure from C flips the old q parity, preventing any return
into C in that round. This applies to the actual selector, not a witness move. -/
theorem c_cross_not_C {H : Nat} {b : Board} {q p : Col}
    (h : C H b) (hq : Legal H b q) (ne : p ≠ q) :
    ¬ C H (afterRound b q p) := by
  intro child
  have old := h.fourOdd q
  have new := child.fourOdd q
  have heightQ : height (afterRound b q p) q = height b q + 1 := by
    simp [afterRound, height, drop, Ne.symm ne]
  change height b q < H at hq
  change (H - height b q) % 2 = 1 at old
  change (H - height (afterRound b q p) q) % 2 = 1 at new
  rw [heightQ] at new
  omega

/-- Every exact certificate has one unit of active budget. -/
theorem certificate_budget_one {H : Nat} {b : Board} (h : Certificate H b) :
    BudgetSafe H (stateless (respond H)) 1 b () := by
  intro k
  induction k generalizing b with
  | zero => exact h.1.1.2.2.1
  | succ k ih =>
    rcases h.2 with ha | hb | hc
    · exact budget_round_mono (k+1) (by omega) (ab_budget_zero ⟨h.1, Or.inl ha⟩ (k+1))
    · exact budget_round_mono (k+1) (by omega) (ab_budget_zero ⟨h.1, Or.inr hb⟩ (k+1))
    · have cert : Certificate H b := ⟨h.1, Or.inr (Or.inr hc)⟩
      refine ⟨h.1.1.2.2.1, Or.inr (Or.inr ?_)⟩
      intro q hq
      refine ⟨certificate_Q_move_safe cert hq, ?_⟩
      by_cases full : Full H (drop b q Q)
      · exact Or.inl full
      · rcases select_total_legal (q := q) (o := referenceObservation H (drop b q Q))
          (drop_bounded h.1.1.1 hq Q) full with ⟨p, chosen, legal⟩
        have good := certificate_selected_good cert hq full
          (referenceObserves H (drop b q Q)) chosen
        refine Or.inr ⟨p, (), ?_, legal, activeCost_le_one H _ q p, ?_⟩
        · simp only [stateless, respond, chosen, Option.map_some]
        · rcases good.2 with terminal | child
          · exact budget_terminal terminal k _ ()
          · by_cases same : p = q
            · subst p
              rw [activeCost_self, Nat.sub_zero]
              exact ih child
            · have ab : ABCert H (afterRound b q p) := by
                refine ⟨child.1, ?_⟩
                rcases child.2 with ha | hb | hc'
                · exact Or.inl ha
                · exact Or.inr hb
                · exact False.elim (c_cross_not_C hc hq same hc')
              exact budget_round_mono k (Nat.zero_le _) (ab_budget_zero ab k)

/-- A cross-column opening cannot be C: C has odd H, but q has height one. -/
theorem opening_cross_not_C {H : Nat} {q p : Col} (positive : 0 < H) (ne : p ≠ q) :
    ¬ C H (afterRound empty q p) := by
  intro hc
  have odd := c_height_odd hc
  have oq := hc.fourOdd q
  have hh : height (afterRound empty q p) q = 1 := by
    simp [afterRound, height, drop, Ne.symm ne]
  change (H - height (afterRound empty q p) q) % 2 = 1 at oq
  rw [hh] at oq
  omega

/-- The second player's first response is charged. If it is active, its
certificate is already A/B; if it covers, the full unit remains for C. -/
theorem second_budget_one (H : Nat) :
    BudgetSafe H (stateless (respond H)) 1 empty () := by
  by_cases zero : H = 0
  · subst H
    exact fun k => budget_terminal zero_empty_terminal k 1 ()
  have positive : 0 < H := by omega
  intro k
  cases k with
  | zero => exact empty_no_win H Q
  | succ k =>
    refine ⟨empty_no_win H Q, Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨oneStone_no_win H q Q, ?_⟩
    by_cases full : Full H (drop empty q Q)
    · exact Or.inl full
    · rcases select_total_legal (q := q) (o := referenceObservation H (drop empty q Q))
        (drop_bounded (empty_bounded H) hq Q) full with ⟨p, chosen, legal⟩
      have good := second_selected_opening_good positive
        (referenceObserves H (drop empty q Q)) chosen
      refine Or.inr ⟨p, (), ?_, legal, activeCost_le_one H _ q p, ?_⟩
      · simp only [stateless, respond, chosen, Option.map_some]
      · rcases good.2 with terminal | cert
        · exact budget_terminal terminal k _ ()
        · by_cases same : p = q
          · subst p
            rw [activeCost_self, Nat.sub_zero]
            exact certificate_budget_one cert k
          · have ab : ABCert H (afterRound empty q p) := by
              refine ⟨cert.1, ?_⟩
              rcases cert.2 with ha | hb | hc
              · exact Or.inl ha
              · exact Or.inr hb
              · exact False.elim (opening_cross_not_C positive same hc)
            exact budget_round_mono k (Nat.zero_le _) (ab_budget_zero ab k)

/-- Heights zero and one have no active second-player responses. -/
theorem second_budget_zero_of_le_one {H : Nat} (small : H ≤ 1) :
    BudgetSafe H (stateless (respond H)) 0 empty () := by
  by_cases zero : H = 0
  · subst H
    exact fun k => budget_terminal zero_empty_terminal k 0 ()
  have one : H = 1 := by omega
  subst H
  intro k
  cases k with
  | zero => exact empty_no_win 1 Q
  | succ k =>
    refine ⟨empty_no_win 1 Q, Or.inr (Or.inr ?_)⟩
    intro q hq
    refine ⟨oneStone_no_win 1 q Q, ?_⟩
    by_cases full : Full 1 (drop empty q Q)
    · exact Or.inl full
    · rcases select_total_legal (q := q) (o := referenceObservation 1 (drop empty q Q))
        (drop_bounded (empty_bounded 1) hq Q) full with ⟨p, chosen, legal⟩
      have good := second_selected_opening_good (by decide : 0 < 1)
        (referenceObserves 1 (drop empty q Q)) chosen
      have unavailable : ¬ Legal 1 (drop empty q Q) q := by
        simp [Legal, height, drop]
      have cost : activeCost 1 (drop empty q Q) q p = 0 :=
        activeCost_of_unavailable unavailable
      refine Or.inr ⟨p, (), ?_, legal, by simp [cost], ?_⟩
      · simp only [stateless, respond, chosen, Option.map_some]
      · rw [cost, Nat.sub_zero]
        rcases good.2 with terminal | cert
        · exact budget_terminal terminal k 0 ()
        · have ab : ABCert 1 (afterRound empty q p) := by
            refine ⟨cert.1, ?_⟩
            rcases cert.2 with ha | hb | hc
            · exact Or.inl ha
            · exact Or.inr hb
            · have impossible := c_height_at_least_three cert.1.1.1 hc
              omega
          exact ab_budget_zero ab k

#print axioms ab_budget_zero
#print axioms certificate_budget_one
#print axioms second_budget_zero_of_le_one
#print axioms second_budget_one
end UniformFour.U1
