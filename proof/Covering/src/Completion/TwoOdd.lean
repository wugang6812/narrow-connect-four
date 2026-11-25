import Completion.TotalSwitch

namespace UniformFour.PaperOne
open OddHeight OddHeight.Player OddHeight.Col UniformFour.U1 UniformFour.U2

def ZeroOrTwo (H : Nat) (b : Board) : Prop :=
  (oddColumns H b).length = 0 ∨ (oddColumns H b).length = 2

/-- The two-odd-column rule needs only the vacancies and a legal opponent
move. Safety against four-in-a-row is a separate geometric obligation. -/
def PairReply (H : Nat) (b : Board) (q p : Col) : Prop :=
  Legal H (drop b q Q) p ∧
    (if Legal H (drop b q Q) q then p = q else OddColumn H b p ∧ p ≠ q)

theorem pair_reply_exists {H b q} (bounded : Bounded H b) (count : ZeroOrTwo H b)
    (hq : Legal H b q) : ∃ p, PairReply H b q p := by
  by_cases room : Legal H (drop b q Q) q
  · exact ⟨q,room,by simp [room]⟩
  have atMost := drop_bounded bounded hq Q q
  have full : height (drop b q Q) q = H := by unfold Legal at room; omega
  obtain ⟨t,ne,pair⟩ := other_odd_of_count count (full_move_was_odd hq full)
  have odd := (pair t).2 (Or.inr rfl)
  exact ⟨t,odd_other_legal ne odd,by simp [room,odd,Ne.symm ne]⟩

private def credit (H : Nat) (b : Board) : Nat := if oddColumns H b = [] then 0 else 1

private theorem pair_round {H b q p} (bounded : Bounded H b) (count : ZeroOrTwo H b)
    (hq : Legal H b q) (r : PairReply H b q p) :
    ZeroOrTwo H (afterRound b q p) ∧ activeCost H (drop b q Q) q p = 0 ∧
      switch q p + credit H (afterRound b q p) = credit H b := by
  by_cases room : Legal H (drop b q Q) q
  · have eq : p = q := by simpa [room] using r.2
    subst p
    simpa [ZeroOrTwo, activeCost, switch, credit, odd_columns_cover room] using count
  have bound := drop_bounded bounded hq Q q
  have full : height (drop b q Q) q = H := by unfold Legal at room; omega
  obtain ⟨t,ne,pair⟩ := other_odd_of_count count (full_move_was_odd hq full)
  obtain ⟨odd,neq⟩ : OddColumn H b p ∧ p ≠ q := by simpa [room] using r.2
  obtain rfl : p = t := ((pair p).mp odd).resolve_left neq
  have old : oddColumns H b ≠ [] := by
    have size := odd_pair_length ne pair
    intro nil; simp [nil] at size
  have newCols := odd_columns_nil_of_even (full_transfer_all_even ne full pair)
  simp [ZeroOrTwo,credit,switch,neq,activeCost,room,old,newCols]

inductive PairRun (H : Nat) (root : Board) : Board → Nat → Nat → Prop
  | nil : PairRun H root root 0 0
  | step {b a t q p} : PairRun H root b a t → Legal H b q → PairReply H b q p →
      PairRun H root (afterRound b q p) (a + activeCost H (drop b q Q) q p) (t + switch q p)

theorem two_odd_controller {H root b a t} (bounded : Bounded H root) (count : ZeroOrTwo H root)
    (path : PairRun H root b a t) :
    a = 0 ∧ t ≤ 1 ∧ ∀ q, Legal H b q → ∃ p, PairReply H b q p := by
  have state : Bounded H b ∧ ZeroOrTwo H b ∧ a = 0 ∧ t + credit H b = credit H root := by
    induction path with
    | nil => exact ⟨bounded,count,rfl,by simp⟩
    | step _ hq r ih =>
      obtain ⟨valid,old,zero,spent⟩ := ih
      obtain ⟨newCount,free,transition⟩ := pair_round valid old hq r
      exact ⟨drop_bounded (drop_bounded valid hq Q) r.1 P,newCount,by omega,by omega⟩
  have cap : credit H root ≤ 1 := by unfold credit; split <;> decide
  exact ⟨state.2.2.1,by have := state.2.2.2; omega,fun _ hq => pair_reply_exists state.1 state.2.1 hq⟩

#print axioms two_odd_controller
end UniformFour.PaperOne
