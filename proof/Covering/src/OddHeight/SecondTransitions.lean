import OddHeight.Words
import OddHeight.StructuralProofs

/-!
The finite family calculations in Claude's odd-height second-player strategy.
All parameters below are arbitrary natural numbers; no bounded-height search is
used.  The tail theorems are deliberately kept out of these calculations.
-/
namespace OddHeight
open Player Col

@[simp] theorem read_QQP_Q (r : Nat) :
    readRow [Q,Q,P] r = some Q ↔ r = 1 ∨ r = 2 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r =>
              cases r with
              | zero => simp [readRow]
              | succ r => simp [readRow]

@[simp] theorem read_QQP_P (r : Nat) :
    readRow [Q,Q,P] r = some P ↔ r = 3 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r =>
              cases r with
              | zero => simp [readRow]
              | succ r => simp [readRow]

/-- One harmless common over-approximation for the registered exception sets. -/
def middleExceptions (x : Cell) : Prop :=
  (x.col = c2 ∨ x.col = c3) ∧ x.row = 2

theorem middle_check_lines {H : Nat} {L : Line}
    (h : ToCheck H middleExceptions L) :
    L = .horizontal 1 ∨ L = rise ∨ L = down ∨ L = rowTwo := by
  rcases h with ⟨hv, hn, x, hx, he⟩
  cases L with
  | vertical c r => exact False.elim hn
  | horizontal r =>
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        simp only [middleExceptions] at he
        have hr : r = 1 ∨ r = 2 := by
          rcases he with h | h
          · exact Or.inl h
          · exact Or.inr h.2
        rcases hr with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr rfl))
  | rising r =>
      have hr : 1 ≤ r := (hv ⟨c1,r⟩ (by simp [Line.cells])).1
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        have : r = 1 := by
          simp [middleExceptions] at he <;> ((try dsimp only at *); omega)
        subst r
        exact Or.inr (Or.inl rfl)
  | falling r =>
      have hr : 1 ≤ r - 3 := (hv ⟨c4,r-3⟩ (by simp [Line.cells])).1
      simp only [Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        have : r = 4 := by
          simp [middleExceptions] at he <;> ((try dsimp only at *); omega)
        subst r
        exact Or.inr (Or.inr (Or.inl rfl))

def NoThreeQ (b : Board) : Prop :=
  ∀ c r, ¬ (stoneAt b ⟨c,r⟩ = some Q ∧
    stoneAt b ⟨c,r+1⟩ = some Q ∧ stoneAt b ⟨c,r+2⟩ = some Q)

theorem noThree_topRun {H : Nat} {b : Board} (h : NoThreeQ b) :
    TopRunAtMostTwo H b := by
  intro c hlt h3 ht
  apply h c (height b c - 2)
  have e1 : height b c - 2 + 1 = height b c - 1 := by ((try dsimp only at *); omega)
  have e2 : height b c - 2 + 2 = height b c := by ((try dsimp only at *); omega)
  rw [e1, e2]
  exact ⟨ht.2.2, ht.2.1, ht.1⟩

theorem noQ_of_noThree_and_nonvertical {H : Nat} {b : Board}
    (hv : NoThreeQ b)
    (hn : ∀ L, L.Nonvertical → ValidLine H L →
      ¬ (∀ x ∈ L.cells, stoneAt b x = some Q)) : ¬ Wins H b Q := by
  rintro ⟨L, hvalid, hq⟩
  cases L with
  | horizontal r => exact hn (.horizontal r) trivial hvalid hq
  | rising r => exact hn (.rising r) trivial hvalid hq
  | falling r => exact hn (.falling r) trivial hvalid hq
  | vertical c r =>
      exact hv c r ⟨hq ⟨c,r⟩ (by simp [Line.cells]),
        hq ⟨c,r+1⟩ (by simp [Line.cells]),
        hq ⟨c,r+2⟩ (by simp [Line.cells])⟩

theorem permanent_of_four_blockers {H : Nat} {b : Board}
    (hs : Structural H b middleExceptions)
    (hb : HasP b (.horizontal 1)) (hr : HasP b rise)
    (hd : HasP b down) (h2 : HasP b rowTwo) : PermanentHyp H b := by
  refine ⟨middleExceptions, hs, ?_⟩
  intro L hL
  rcases middle_check_lines hL with rfl | rfl | rfl | rfl
  · exact hb
  · exact hr
  · exact hd
  · exact h2

theorem otherBlocked_of_four {H : Nat} {b : Board} {L : Line}
    (hb : L = .horizontal 1 ∨ HasP b (.horizontal 1))
    (hr : L = rise ∨ HasP b rise)
    (hd : L = down ∨ HasP b down)
    (h2 : L = rowTwo ∨ HasP b rowTwo) :
    ∀ M, ToCheck H middleExceptions M → M ≠ L → HasP b M := by
  intro M hM hne
  rcases middle_check_lines hM with rfl | rfl | rfl | rfl
  all_goals first
    | exact hb.resolve_left (fun h => hne h.symm)
    | exact hr.resolve_left (fun h => hne h.symm)
    | exact hd.resolve_left (fun h => hne h.symm)
    | exact h2.resolve_left (fun h => hne h.symm)

def innerExit1 (a : Nat) : Board := board ([P] ++ qp a) [Q,Q,P] [] []
def innerExit2 (a : Nat) : Board := board ([P] ++ qp a) [Q] [] [Q,P]
def innerExit3 (a : Nat) : Board := board ([P] ++ qp a) [Q] [Q,P] []

theorem inner_cover_shape (a : Nat) :
    drop (drop (innerBoard a) c1 Q) c1 P = innerBoard (a+1) := by
  funext c
  cases c <;> simp [drop, innerBoard, board, qp, List.append_assoc]

theorem inner_event2_shape (a : Nat) :
    drop (drop (innerBoard a) c2 Q) c2 P = innerExit1 a := by
  funext c
  cases c <;> rfl

theorem inner_event4_shape (a : Nat) :
    drop (drop (innerBoard a) c4 Q) c4 P = innerExit2 a := by
  funext c
  cases c <;> rfl

theorem inner_event3_shape (a : Nat) :
    drop (drop (innerBoard a) c3 Q) c3 P = innerExit3 a := by
  funext c
  cases c <;> rfl

theorem outer_cover1_shape (a d : Nat) :
    drop (drop (outerBoard a d) c1 Q) c1 P = outerBoard (a+1) d := by
  funext c
  cases c <;> simp [drop, outerBoard, board, qp, List.append_assoc]

theorem outer_cover4_shape (a d : Nat) :
    drop (drop (outerBoard a d) c4 Q) c4 P = outerBoard a (d+1) := by
  funext c
  cases c <;> simp [drop, outerBoard, board, qp, List.append_assoc]

theorem outer_event2_shape (a d : Nat) :
    drop (drop (outerBoard a d) c2 Q) c3 P = a1 a d := by
  funext c
  cases c <;> rfl

theorem outer_event3_shape (a d : Nat) :
    drop (drop (outerBoard a d) c3 Q) c2 P = a2 a d := by
  funext c
  cases c <;> rfl

theorem outer_event1_shape (a d : Nat) :
    drop (drop (outerBoard a d) c1 Q) c3 P = a3 a d := by
  funext c
  cases c <;> rfl

theorem outer_event4_shape (a d : Nat) :
    drop (drop (outerBoard a d) c4 Q) c2 P = a4 a d := by
  funext c
  cases c <;> rfl

@[simp] theorem read_QP_Q (r : Nat) : readRow [Q,P] r = some Q ↔ r = 1 := by
  have h := read_qp_Q 1 r
  change readRow [Q,P] r = some Q ↔ _ at h
  rw [h]
  ((try dsimp only at *); omega)

@[simp] theorem read_QP_P (r : Nat) : readRow [Q,P] r = some P ↔ r = 2 := by
  have h := read_qp_P 1 r
  change readRow [Q,P] r = some P ↔ _ at h
  rw [h]
  ((try dsimp only at *); omega)

@[simp] theorem read_PQP_Q (r : Nat) : readRow [P,Q,P] r = some Q ↔ r = 2 := by
  have h := read_pqp_Q 1 r
  change readRow [P,Q,P] r = some Q ↔ _ at h
  rw [h]
  ((try dsimp only at *); omega)

@[simp] theorem read_PQP_P (r : Nat) :
    readRow [P,Q,P] r = some P ↔ r = 1 ∨ r = 3 := by
  have h := read_pqp_P 1 r
  change readRow [P,Q,P] r = some P ↔ _ at h
  rw [h]
  ((try dsimp only at *); omega)

/-- A calculation certificate, not a strategic safety assumption.  It contains
only inequalities and facts about the current board's occupied cells. -/
structure ElementarySecond (H : Nat) (b : Board) : Prop where
  bounded : Bounded H b
  outerAdjacent : ∀ c, c = c1 ∨ c = c4 → ∀ r,
    ¬ (stoneAt b ⟨c,r⟩ = some Q ∧ stoneAt b ⟨c,r+1⟩ = some Q)
  middleLow : ∀ c, c = c2 ∨ c = c3 → ∀ r,
    stoneAt b ⟨c,r⟩ = some Q → r ≤ 2
  middleTop : ∀ c, c = c2 ∨ c = c3 →
    stoneAt b ⟨c,height b c⟩ = some Q → height b c = 1
  outerTop : ∀ c, c = c1 ∨ c = c4 → height b c < H →
    stoneAt b ⟨c,height b c⟩ ≠ some Q
  horizontal : ∀ r, ¬ (stoneAt b ⟨c1,r⟩ = some Q ∧
    stoneAt b ⟨c2,r⟩ = some Q ∧ stoneAt b ⟨c3,r⟩ = some Q ∧
    stoneAt b ⟨c4,r⟩ = some Q)

theorem ElementarySecond.noThree {H : Nat} {b : Board}
    (h : ElementarySecond H b) : NoThreeQ b := by
  intro c r hq
  cases c with
  | c1 => exact h.outerAdjacent c1 (Or.inl rfl) r ⟨hq.1,hq.2.1⟩
  | c4 => exact h.outerAdjacent c4 (Or.inr rfl) r ⟨hq.1,hq.2.1⟩
  | c2 =>
      have hr := h.middleLow c2 (Or.inl rfl) (r+2) hq.2.2
      have : r = 0 := by ((try dsimp only at *); omega)
      subst r
      simpa [stoneAt, readRow] using hq.1
  | c3 =>
      have hr := h.middleLow c3 (Or.inr rfl) (r+2) hq.2.2
      have : r = 0 := by ((try dsimp only at *); omega)
      subst r
      simpa [stoneAt, readRow] using hq.1

theorem noQ_of_low_middle {H : Nat} {b : Board}
    (hv : NoThreeQ b)
    (h2 : ∀ r, stoneAt b ⟨c2,r⟩ = some Q → r ≤ 2)
    (h3 : ∀ r, stoneAt b ⟨c3,r⟩ = some Q → r ≤ 2)
    (hh : ∀ r, ¬ (stoneAt b ⟨c1,r⟩ = some Q ∧
      stoneAt b ⟨c2,r⟩ = some Q ∧ stoneAt b ⟨c3,r⟩ = some Q ∧
      stoneAt b ⟨c4,r⟩ = some Q)) : ¬ Wins H b Q := by
  apply noQ_of_noThree_and_nonvertical hv
  intro L hn hvalid hall
  cases L with
  | vertical c r => exact False.elim hn
  | horizontal r =>
      exact hh r ⟨hall ⟨c1,r⟩ (by simp [Line.cells]),
        hall ⟨c2,r⟩ (by simp [Line.cells]),
        hall ⟨c3,r⟩ (by simp [Line.cells]),
        hall ⟨c4,r⟩ (by simp [Line.cells])⟩
  | rising r =>
      have hr := (hvalid ⟨c1,r⟩ (by simp [Line.cells])).1
      have hsmall := h3 (r+2) (hall ⟨c3,r+2⟩ (by simp [Line.cells]))
      ((try dsimp only at *); omega)
  | falling r =>
      have hr := (hvalid ⟨c4,r-3⟩ (by simp [Line.cells])).1
      have hsmall := h2 (r-1) (hall ⟨c2,r-1⟩ (by simp [Line.cells]))
      ((try dsimp only at *); omega)

theorem ElementarySecond.noQ {H : Nat} {b : Board}
    (h : ElementarySecond H b) : ¬ Wins H b Q :=
  noQ_of_low_middle h.noThree (h.middleLow c2 (Or.inl rfl))
    (h.middleLow c3 (Or.inr rfl)) h.horizontal

theorem ElementarySecond.complete {H : Nat} {b : Board}
    (h : ElementarySecond H b) : ExceptionComplete H b middleExceptions := by
  intro x hx
  rcases x with ⟨c,r⟩
  rcases hx with ⟨hr,hq,hprev⟩ | ⟨hp,hn,he,htop⟩
  · have he : r - 1 + 1 = r := by ((try dsimp only at *); omega)
    cases c with
    | c1 =>
        exact False.elim (h.outerAdjacent c1 (Or.inl rfl) (r-1)
          ⟨hprev, by simpa [he] using hq⟩)
    | c4 =>
        exact False.elim (h.outerAdjacent c4 (Or.inr rfl) (r-1)
          ⟨hprev, by simpa [he] using hq⟩)
    | c2 =>
        have hlo := h.middleLow c2 (Or.inl rfl) r hq
        exact ⟨Or.inl rfl, by ((try dsimp only at *); omega)⟩
    | c3 =>
        have hlo := h.middleLow c3 (Or.inr rfl) r hq
        exact ⟨Or.inr rfl, by ((try dsimp only at *); omega)⟩
  · cases c with
    | c1 => exact False.elim (h.outerTop c1 (Or.inl rfl) hn htop)
    | c4 => exact False.elim (h.outerTop c4 (Or.inr rfl) hn htop)
    | c2 =>
        have hheight := h.middleTop c2 (Or.inl rfl) htop
        exact ⟨Or.inl rfl, by ((try dsimp only at *); omega)⟩
    | c3 =>
        have hheight := h.middleTop c3 (Or.inr rfl) htop
        exact ⟨Or.inr rfl, by ((try dsimp only at *); omega)⟩

theorem ElementarySecond.structural {H : Nat} {b : Board}
    (h : ElementarySecond H b) : Structural H b middleExceptions :=
  ⟨h.bounded, h.noQ, noThree_topRun h.noThree, h.complete⟩

/-- The constructors contain only the explicit column strings and their bounds. -/
inductive SecondEndpoint (H : Nat) : Board → Prop where
  | inner (a : Nat) : 1 + 2*a ≤ H → SecondEndpoint H (innerBoard a)
  | inner1 (a : Nat) : 1 + 2*a ≤ H → 3 ≤ H → SecondEndpoint H (innerExit1 a)
  | inner2 (a : Nat) : 1 + 2*a ≤ H → 2 ≤ H → SecondEndpoint H (innerExit2 a)
  | inner3 (a : Nat) : 1 + 2*a ≤ H → 2 ≤ H → SecondEndpoint H (innerExit3 a)
  | outer (a d : Nat) : 2*a ≤ H → 2*d ≤ H → SecondEndpoint H (outerBoard a d)
  | event1 (a d : Nat) : 1 ≤ a → 2*a ≤ H → 2*d ≤ H → SecondEndpoint H (a1 a d)
  | event2 (a d : Nat) : 1 ≤ a → 2*a ≤ H → 2*d ≤ H → SecondEndpoint H (a2 a d)
  | event3 (a d : Nat) : 2*a+1 = H → 2*d ≤ H → 1 ≤ H → SecondEndpoint H (a3 a d)
  | event4 (a d : Nat) : 2*a ≤ H → 2*d+1 = H → 1 ≤ H → SecondEndpoint H (a4 a d)
  | middle1 (d : Nat) : 3 ≤ H → 2*d ≤ H → SecondEndpoint H (middleExit1 d)
  | middle2 (d : Nat) : 3 ≤ H → 2*d ≤ H → SecondEndpoint H (middleExit2 d)
  | middle3 (d : Nat) : 3 ≤ H → 2*d ≤ H → SecondEndpoint H (middleExit3 d)
  | middle4 (d : Nat) : 3 ≤ H → 2*d ≤ H → SecondEndpoint H (middleExit4 d)

/-- Uniform symbolic calculation.  `qp` is not unfolded: its lookup formula
handles arbitrarily large a and d. -/
macro "second_simp" : tactic => `(tactic|
  (simp_all [height, innerBoard, outerBoard, innerExit1, innerExit2,
    innerExit3, a1, a2, a3, a4, middleExit1, middleExit2,
    middleExit3, middleExit4, board] <;> ((try dsimp only at *); omega)))

theorem second_endpoint_elementary {H : Nat} {b : Board}
    (h : SecondEndpoint H b) : ElementarySecond H b := by
  cases h
  all_goals
    constructor
    · intro c; cases c <;> second_simp
    · intro c hc r hq
      rcases hc with rfl | rfl <;> second_simp
    · intro c hc r hq
      rcases hc with rfl | rfl <;> second_simp
    · intro c hc hq
      rcases hc with rfl | rfl <;> second_simp
    · intro c hc hn hq
      rcases hc with rfl | rfl <;> second_simp
    · intro r hq
      second_simp

theorem second_endpoint_structural {H : Nat} {b : Board}
    (h : SecondEndpoint H b) : Structural H b middleExceptions :=
  (second_endpoint_elementary h).structural

theorem inner_reply_legal {H a : Nat} (h5 : 5 ≤ H) (ho : H % 2 = 1)
    (hb : 1 + 2*a ≤ H) (q : Col) (hq : Legal H (innerBoard a) q) :
    Legal H (drop (innerBoard a) q Q) q := by
  cases q <;> simp_all [Legal, height, innerBoard, board, drop] <;> ((try dsimp only at *); omega)

theorem outer_nonfill_reply_legal {H a d : Nat} (q : Col)
    (hq : Legal H (outerBoard a d) q)
    (hn : height (drop (outerBoard a d) q Q) q ≠ H) :
    Legal H (drop (outerBoard a d) q Q) q := by
  simp only [Legal, height_drop_same] at *
  ((try dsimp only at *); omega)

theorem outer_cross_reply_legal {H a d : Nat} (h5 : 5 ≤ H) :
    Legal H (drop (outerBoard a d) c2 Q) c3 ∧
    Legal H (drop (outerBoard a d) c3 Q) c2 ∧
    Legal H (drop (outerBoard a d) c1 Q) c3 ∧
    Legal H (drop (outerBoard a d) c4 Q) c2 := by
  simp [Legal, height, drop, outerBoard, board]
  ((try dsimp only at *); omega)

@[simp] theorem read_QQ_Q (r : Nat) :
    readRow [Q,Q] r = some Q ↔ r = 1 ∨ r = 2 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r => simp [readRow]

@[simp] theorem read_PQ_Q (r : Nat) : readRow [P,Q] r = some Q ↔ r = 2 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          cases r with
          | zero => simp [readRow]
          | succ r => simp [readRow]

@[simp] theorem read_pqpq_Q (a r : Nat) :
    readRow (P :: (qp a ++ [Q])) r = some Q ↔
      0 < r ∧ r ≤ 2*a+2 ∧ r % 2 = 0 := by
  cases r with
  | zero => simp [readRow]
  | succ r =>
      cases r with
      | zero => simp [readRow]
      | succ r =>
          change (qp a ++ [Q])[r]? = some Q ↔ _
          rw [qpq_get_Q]
          ((try dsimp only at *); omega)

macro "second_drop_simp" : tactic => `(tactic|
  (simp_all [drop, innerBoard, outerBoard, a1, a2, board,
    List.append_assoc] <;> ((try dsimp only at *); omega)))

theorem inner_Q_noQ (H a : Nat) (q : Col) :
    ¬ Wins H (drop (innerBoard a) q Q) Q := by
  apply noQ_of_low_middle
  · intro c r h
    cases q <;> cases c <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp

theorem outer_Q_noQ (H a d : Nat) (q : Col) :
    ¬ Wins H (drop (outerBoard a d) q Q) Q := by
  apply noQ_of_low_middle
  · intro c r h
    cases q <;> cases c <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp

theorem a1_Q_noQ (H a d : Nat) (q : Col) :
    ¬ Wins H (drop (a1 a d) q Q) Q := by
  apply noQ_of_low_middle
  · intro c r h
    cases q <;> cases c <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp

theorem a2_Q_noQ (H a d : Nat) (q : Col) :
    ¬ Wins H (drop (a2 a d) q Q) Q := by
  apply noQ_of_low_middle
  · intro c r h
    cases q <;> cases c <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp
  · intro r h
    cases q <;> second_drop_simp

theorem candidate_rise_of_checks {H : Nat} {b : Board} (h5 : 5 ≤ H)
    (hs : Structural H b middleExceptions)
    (hb : HasP b (.horizontal 1)) (hd : HasP b down) (h2 : HasP b rowTwo)
    (height3 : height b c3 = 1)
    (even : outside H b [⟨c3,3⟩] % 2 = 0) :
    CandidateHyp H b rise [⟨c3,3⟩] := by
  refine ⟨middleExceptions, hs, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, even⟩
  · intro x hx
    simp only [rise, Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> unfold InBoard <;> simp <;> ((try dsimp only at *); omega)
  · exact otherBlocked_of_four (Or.inr hb) (Or.inl rfl) (Or.inr hd) (Or.inr h2)
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [targetCell, rise, down, Line.cells]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [height3]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [height3]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp
    ((try dsimp only at *); omega)

theorem candidate_down_of_checks {H : Nat} {b : Board} (h5 : 5 ≤ H)
    (hs : Structural H b middleExceptions)
    (hb : HasP b (.horizontal 1)) (hr : HasP b rise) (h2 : HasP b rowTwo)
    (height2 : height b c2 = 1)
    (even : outside H b [⟨c2,3⟩] % 2 = 0) :
    CandidateHyp H b down [⟨c2,3⟩] := by
  refine ⟨middleExceptions, hs, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, even⟩
  · intro x hx
    simp only [down, Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> unfold InBoard <;> simp <;> ((try dsimp only at *); omega)
  · exact otherBlocked_of_four (Or.inr hb) (Or.inr hr) (Or.inl rfl) (Or.inr h2)
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [targetCell, rise, down, Line.cells]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [height2]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [height2]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp
    ((try dsimp only at *); omega)

macro "second_blocker_simp" : tactic => `(tactic|
  (simp [HasP, rise, down, rowTwo, Line.cells,
    innerBoard, innerExit1, innerExit2, innerExit3,
    a1, a2, a3, a4, middleExit1, middleExit2, middleExit3,
    middleExit4, board] <;> ((try dsimp only at *); omega)))

macro "second_capacity_simp" : tactic => `(tactic|
  (simp [outside, allCols, inJ, height,
    innerBoard, innerExit1, innerExit2, innerExit3,
    a1, a2, a3, a4, middleExit1, middleExit2, middleExit3,
    middleExit4, board] <;> ((try dsimp only at *); omega)))

theorem inner1_candidate {H a : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (ha : 1 + 2*a ≤ H) : CandidateHyp H (innerExit1 a) rowTwo [⟨c3,2⟩,⟨c4,2⟩] := by
  have hs := second_endpoint_structural (SecondEndpoint.inner1 a ha (by ((try dsimp only at *); omega)))
  refine ⟨middleExceptions, hs, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [rowTwo, Line.cells, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> unfold InBoard <;> simp <;> ((try dsimp only at *); omega)
  · apply otherBlocked_of_four
    · exact Or.inr (by second_blocker_simp)
    · exact Or.inr (by second_blocker_simp)
    · exact Or.inr (by second_blocker_simp)
    · exact Or.inl rfl
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [targetCell, rowTwo, Line.cells]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [height,innerExit1,board]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [height,innerExit1,board]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp <;> ((try dsimp only at *); omega)
  · second_capacity_simp

theorem inner2_candidate {H a : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (ha : 1 + 2*a ≤ H) : CandidateHyp H (innerExit2 a) down [⟨c2,3⟩] := by
  apply candidate_down_of_checks h5
  · exact second_endpoint_structural (SecondEndpoint.inner2 a ha (by ((try dsimp only at *); omega)))
  · second_blocker_simp
  · second_blocker_simp
  · second_blocker_simp
  · rfl
  · second_capacity_simp

theorem inner3_permanent {H a : Nat} (h5 : 5 ≤ H)
    (ha : 1 + 2*a ≤ H) : PermanentHyp H (innerExit3 a) := by
  apply permanent_of_four_blockers
  · exact second_endpoint_structural (SecondEndpoint.inner3 a ha (by ((try dsimp only at *); omega)))
  all_goals second_blocker_simp

theorem a1_rise_iff (a d : Nat) : HasP (a1 a d) rise ↔ 2 ≤ d := by
  second_blocker_simp

theorem a1_down_iff (a d : Nat) : HasP (a1 a d) down ↔ 2 ≤ a := by
  second_blocker_simp

theorem a2_rise_iff (a d : Nat) : HasP (a2 a d) rise ↔ 2 ≤ d := by
  second_blocker_simp

theorem a2_down_iff (a d : Nat) : HasP (a2 a d) down ↔ 2 ≤ a := by
  second_blocker_simp

theorem a3_rise_iff (a d : Nat) : HasP (a3 a d) rise ↔ 2 ≤ d := by
  second_blocker_simp

theorem a3_down_iff (a d : Nat) : HasP (a3 a d) down ↔ 2 ≤ a := by
  second_blocker_simp

theorem a4_rise_iff (a d : Nat) : HasP (a4 a d) rise ↔ 2 ≤ d := by
  second_blocker_simp

theorem a4_down_iff (a d : Nat) : HasP (a4 a d) down ↔ 2 ≤ a := by
  second_blocker_simp

theorem hasPBool_true {b : Board} {L : Line} : hasPBool b L = true ↔ HasP b L := by
  simp [hasPBool, HasP]

theorem hasPBool_false {b : Board} {L : Line} (h : ¬ HasP b L) :
    hasPBool b L = false := by
  cases hb : hasPBool b L with
  | false => rfl
  | true => exact False.elim (h (hasPBool_true.mp hb))

theorem classify_both {b : Board} (hr : HasP b rise) (hd : HasP b down) :
    classify b = .permanent := by
  simp [classify, hasPBool_true.mpr hr, hasPBool_true.mpr hd]

theorem classify_only_down {b : Board} (hr : ¬ HasP b rise) (hd : HasP b down) :
    classify b = .candidate rise [⟨c3,3⟩] := by
  simp [classify, hasPBool_false hr, hasPBool_true.mpr hd]

theorem classify_only_rise {b : Board} (hr : HasP b rise) (hd : ¬ HasP b down) :
    classify b = .candidate down [⟨c2,3⟩] := by
  simp [classify, hasPBool_true.mpr hr, hasPBool_false hd]

theorem classify_neither {b : Board} (hr : ¬ HasP b rise) (hd : ¬ HasP b down) :
    classify b = .delay := by
  simp [classify, hasPBool_false hr, hasPBool_false hd]

theorem a12_classified {H a d : Nat} {b : Board}
    (h5 : 5 ≤ H) (odd : H % 2 = 1) (ha1 : 1 ≤ a)
    (ha : 2*a ≤ H) (hd : 2*d ≤ H) (he : b = a1 a d ∨ b = a2 a d) :
    PhaseInvariant H b (classify b) := by
  have hs : Structural H b middleExceptions := by
    rcases he with rfl | rfl
    · exact second_endpoint_structural (.event1 a d ha1 ha hd)
    · exact second_endpoint_structural (.event2 a d ha1 ha hd)
  have hbase : HasP b (.horizontal 1) := by
    rcases he with rfl | rfl <;> second_blocker_simp
  have hrow : HasP b rowTwo := by
    rcases he with rfl | rfl <;> second_blocker_simp
  have hrise : HasP b rise ↔ 2 ≤ d := by
    rcases he with rfl | rfl
    · exact a1_rise_iff a d
    · exact a2_rise_iff a d
  have hdown : HasP b down ↔ 2 ≤ a := by
    rcases he with rfl | rfl
    · exact a1_down_iff a d
    · exact a2_down_iff a d
  by_cases hr : 2 ≤ d
  · have hR := hrise.mpr hr
    by_cases hD : 2 ≤ a
    · rw [classify_both hR (hdown.mpr hD)]
      exact permanent_of_four_blockers hs hbase hR (hdown.mpr hD) hrow
    · have hnD : ¬ HasP b down := fun h => hD (hdown.mp h)
      rw [classify_only_rise hR hnD]
      apply candidate_down_of_checks h5 hs hbase hR hrow
      · rcases he with rfl | rfl <;> rfl
      · rcases he with rfl | rfl <;> second_capacity_simp
  · have hnR : ¬ HasP b rise := fun h => hr (hrise.mp h)
    by_cases hD : 2 ≤ a
    · rw [classify_only_down hnR (hdown.mpr hD)]
      apply candidate_rise_of_checks h5 hs hbase (hdown.mpr hD) hrow
      · rcases he with rfl | rfl <;> rfl
      · rcases he with rfl | rfl <;> second_capacity_simp
    · have hnD : ¬ HasP b down := fun h => hD (hdown.mp h)
      rw [classify_neither hnR hnD]
      have haeq : a = 1 := by ((try dsimp only at *); omega)
      subst a
      exact ⟨d, by ((try dsimp only at *); omega), he⟩

theorem a3_classified {H a d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (ha : 2*a+1 = H) (hd : 2*d ≤ H) :
    PhaseInvariant H (a3 a d) (classify (a3 a d)) := by
  have hs := second_endpoint_structural (SecondEndpoint.event3 a d ha hd (by ((try dsimp only at *); omega)))
  have hbase : HasP (a3 a d) (.horizontal 1) := by second_blocker_simp
  have hrow : HasP (a3 a d) rowTwo := by second_blocker_simp
  have hD : HasP (a3 a d) down := (a3_down_iff a d).mpr (by ((try dsimp only at *); omega))
  by_cases hd2 : 2 ≤ d
  · have hR := (a3_rise_iff a d).mpr hd2
    rw [classify_both hR hD]
    exact permanent_of_four_blockers hs hbase hR hD hrow
  · have hnR : ¬ HasP (a3 a d) rise := fun h => hd2 ((a3_rise_iff a d).mp h)
    rw [classify_only_down hnR hD]
    apply candidate_rise_of_checks h5 hs hbase hD hrow
    · rfl
    · second_capacity_simp

theorem a4_classified {H a d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (ha1 : 1 ≤ a) (ha : 2*a ≤ H) (hd : 2*d+1 = H) :
    PhaseInvariant H (a4 a d) (classify (a4 a d)) := by
  have hs := second_endpoint_structural (SecondEndpoint.event4 a d ha hd (by ((try dsimp only at *); omega)))
  have hbase : HasP (a4 a d) (.horizontal 1) := by second_blocker_simp
  have hrow : HasP (a4 a d) rowTwo := by second_blocker_simp
  have hR : HasP (a4 a d) rise := (a4_rise_iff a d).mpr (by ((try dsimp only at *); omega))
  by_cases ha2 : 2 ≤ a
  · have hD := (a4_down_iff a d).mpr ha2
    rw [classify_both hR hD]
    exact permanent_of_four_blockers hs hbase hR hD hrow
  · have hnD : ¬ HasP (a4 a d) down := fun h => ha2 ((a4_down_iff a d).mp h)
    rw [classify_only_rise hR hnD]
    apply candidate_down_of_checks h5 hs hbase hR hrow
    · rfl
    · second_capacity_simp

theorem middle1_classified {H d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (hd : d ≤ 1) : PhaseInvariant H (middleExit1 d) (classify (middleExit1 d)) := by
  have hnR : ¬ HasP (middleExit1 d) rise := by second_blocker_simp
  have hD : HasP (middleExit1 d) down := by second_blocker_simp
  rw [classify_only_down hnR hD]
  apply candidate_rise_of_checks h5
  · exact second_endpoint_structural (.middle1 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
  · second_blocker_simp
  · exact hD
  · second_blocker_simp
  · rfl
  · second_capacity_simp

theorem middle2_classified {H d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (hd : d ≤ 1) : PhaseInvariant H (middleExit2 d) (classify (middleExit2 d)) := by
  have hR : HasP (middleExit2 d) rise := by second_blocker_simp
  have hnD : ¬ HasP (middleExit2 d) down := by second_blocker_simp
  rw [classify_only_rise hR hnD]
  apply candidate_down_of_checks h5
  · exact second_endpoint_structural (.middle2 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
  · second_blocker_simp
  · exact hR
  · second_blocker_simp
  · rfl
  · second_capacity_simp

theorem middle3_classified {H d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (hd : d ≤ 1) : PhaseInvariant H (middleExit3 d) (classify (middleExit3 d)) := by
  have hR : HasP (middleExit3 d) rise := by second_blocker_simp
  have hnD : ¬ HasP (middleExit3 d) down := by second_blocker_simp
  rw [classify_only_rise hR hnD]
  apply candidate_down_of_checks h5
  · exact second_endpoint_structural (.middle3 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
  · second_blocker_simp
  · exact hR
  · second_blocker_simp
  · rfl
  · second_capacity_simp

theorem middle4_classified {H d : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    (hd : d ≤ 1) : PhaseInvariant H (middleExit4 d) (classify (middleExit4 d)) := by
  have hnR : ¬ HasP (middleExit4 d) rise := by second_blocker_simp
  have hD : HasP (middleExit4 d) down := by second_blocker_simp
  rw [classify_only_down hnR hD]
  apply candidate_rise_of_checks h5
  · exact second_endpoint_structural (.middle4 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
  · second_blocker_simp
  · exact hD
  · second_blocker_simp
  · rfl
  · second_capacity_simp

theorem second_endpoint_invariant {H : Nat} {b : Board} {ph : Phase}
    (hb : SecondEndpoint H b) (hp : PhaseInvariant H b ph) : ClaudeInvariant H b ph :=
  let hs := second_endpoint_structural hb
  ⟨hs.bounded, hs.noQ, hp⟩

theorem inner_reply1 (H a : Nat) :
    reply H (innerBoard a) c1 .innerWait = some (c1,.innerWait) := rfl

theorem inner_reply2 (H a : Nat) :
    reply H (innerBoard a) c2 .innerWait =
      some (c2,.candidate rowTwo [⟨c3,2⟩,⟨c4,2⟩]) := by
  simp [reply, rawReply, settle, inner_event2_shape,
    innerExit1, stoneAt, targetCell, board]

theorem inner_reply3 (H a : Nat) :
    reply H (innerBoard a) c3 .innerWait = some (c3,.permanent) := rfl

theorem inner_reply4 (H a : Nat) :
    reply H (innerBoard a) c4 .innerWait = some (c4,.candidate down [⟨c2,3⟩]) := by
  simp [reply, rawReply, settle, inner_event4_shape,
    innerExit2, stoneAt, targetCell, board]

theorem outer_reply1_filled {H a d : Nat}
    (hf : height (drop (outerBoard a d) c1 Q) c1 = H) :
    reply H (outerBoard a d) c1 .outerWait = some (c3,classify (a3 a d)) := by
  have he : 2*a+1 = H := by simpa using hf
  simp [reply, rawReply, he, settle, outer_event1_shape]

theorem outer_reply1_notfilled {H a d : Nat}
    (hf : height (drop (outerBoard a d) c1 Q) c1 ≠ H) :
    reply H (outerBoard a d) c1 .outerWait = some (c1,.outerWait) := by
  have he : 2*a+1 ≠ H := by simpa using hf
  simp [reply, rawReply, he, settle]

theorem outer_reply2 (H a d : Nat) :
    reply H (outerBoard a d) c2 .outerWait = some (c3,classify (a1 a d)) := by
  simp [reply, rawReply, settle, outer_event2_shape]

theorem outer_reply3 (H a d : Nat) :
    reply H (outerBoard a d) c3 .outerWait = some (c2,classify (a2 a d)) := by
  simp [reply, rawReply, settle, outer_event3_shape]

theorem outer_reply4_filled {H a d : Nat}
    (hf : height (drop (outerBoard a d) c4 Q) c4 = H) :
    reply H (outerBoard a d) c4 .outerWait = some (c2,classify (a4 a d)) := by
  have he : 2*d+1 = H := by simpa using hf
  simp [reply, rawReply, he, settle, outer_event4_shape]

theorem outer_reply4_notfilled {H a d : Nat}
    (hf : height (drop (outerBoard a d) c4 Q) c4 ≠ H) :
    reply H (outerBoard a d) c4 .outerWait = some (c4,.outerWait) := by
  have he : 2*d+1 ≠ H := by simpa using hf
  simp [reply, rawReply, he, settle]

theorem delay_reply (H : Nat) (b : Board) (q : Col) :
    reply H b q .delay = some (q,classify (drop (drop b q Q) q P)) := rfl

theorem a1_cover1_shape (a d : Nat) :
    drop (drop (a1 a d) c1 Q) c1 P = a1 (a+1) d := by
  funext c
  cases c <;> simp [a1, drop, board, qp, List.append_assoc]

theorem a2_cover1_shape (a d : Nat) :
    drop (drop (a2 a d) c1 Q) c1 P = a2 (a+1) d := by
  funext c
  cases c <;> simp [a2, drop, board, qp, List.append_assoc]

theorem a1_cover4_shape (a d : Nat) :
    drop (drop (a1 a d) c4 Q) c4 P = a1 a (d+1) := by
  funext c
  cases c <;> simp [a1, drop, board, qp, List.append_assoc]

theorem a2_cover4_shape (a d : Nat) :
    drop (drop (a2 a d) c4 Q) c4 P = a2 a (d+1) := by
  funext c
  cases c <;> simp [a2, drop, board, qp, List.append_assoc]

theorem a1_cover2_shape (d : Nat) :
    drop (drop (a1 1 d) c2 Q) c2 P = middleExit1 d := by
  funext c
  cases c <;> rfl

theorem a1_cover3_shape (d : Nat) :
    drop (drop (a1 1 d) c3 Q) c3 P = middleExit3 d := by
  funext c
  cases c <;> rfl

theorem a2_cover2_shape (d : Nat) :
    drop (drop (a2 1 d) c2 Q) c2 P = middleExit4 d := by
  funext c
  cases c <;> rfl

theorem a2_cover3_shape (d : Nat) :
    drop (drop (a2 1 d) c3 Q) c3 P = middleExit2 d := by
  funext c
  cases c <;> rfl

/-- Strong local conclusion for the three non-tail phases.  They always have
room for an actual legal response, even if Q's move would otherwise be terminal. -/
def SecondResponse (H : Nat) (b : Board) (q : Col) (ph : Phase) : Prop :=
  ¬ Wins H (drop b q Q) Q ∧
  ∃ c next, reply H b q ph = some (c,next) ∧ Legal H (drop b q Q) c ∧
    ClaudeInvariant H (drop (drop b q Q) c P) next

theorem inner_response {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    {b : Board} (hb : InnerFamily H b) (q : Col) (hq : Legal H b q) :
    SecondResponse H b q .innerWait := by
  rcases hb with ⟨a,rfl,ha⟩
  refine ⟨inner_Q_noQ H a q, ?_⟩
  have hl := inner_reply_legal h5 odd ha q hq
  cases q with
  | c1 =>
      refine ⟨c1,.innerWait,inner_reply1 H a,hl,?_⟩
      rw [inner_cover_shape]
      have hnew : 1+2*(a+1) ≤ H := by
        simp only [Legal, inner_height_one] at hq
        ((try dsimp only at *); omega)
      exact second_endpoint_invariant (.inner (a+1) hnew) ⟨a+1,rfl,hnew⟩
  | c2 =>
      refine ⟨c2,.candidate rowTwo [⟨c3,2⟩,⟨c4,2⟩],inner_reply2 H a,hl,?_⟩
      rw [inner_event2_shape]
      exact second_endpoint_invariant (.inner1 a ha (by ((try dsimp only at *); omega)))
        (inner1_candidate h5 odd ha)
  | c3 =>
      refine ⟨c3,.permanent,inner_reply3 H a,hl,?_⟩
      rw [inner_event3_shape]
      exact second_endpoint_invariant (.inner3 a ha (by ((try dsimp only at *); omega))) (inner3_permanent h5 ha)
  | c4 =>
      refine ⟨c4,.candidate down [⟨c2,3⟩],inner_reply4 H a,hl,?_⟩
      rw [inner_event4_shape]
      exact second_endpoint_invariant (.inner2 a ha (by ((try dsimp only at *); omega))) (inner2_candidate h5 odd ha)

theorem outer_response {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    {b : Board} (hb : OuterFamily H b) (q : Col) (hq : Legal H b q) :
    SecondResponse H b q .outerWait := by
  rcases hb with ⟨a,d,ha1,rfl,ha,hd⟩
  refine ⟨outer_Q_noQ H a d q,?_⟩
  have cross := outer_cross_reply_legal (a:=a) (d:=d) h5
  cases q with
  | c1 =>
      by_cases hf : height (drop (outerBoard a d) c1 Q) c1 = H
      · refine ⟨c3,classify (a3 a d),outer_reply1_filled hf,cross.2.2.1,?_⟩
        rw [outer_event1_shape]
        have he : 2*a+1 = H := by simpa using hf
        exact second_endpoint_invariant (.event3 a d he hd (by ((try dsimp only at *); omega)))
          (a3_classified h5 odd he hd)
      · have hl := outer_nonfill_reply_legal c1 hq hf
        refine ⟨c1,.outerWait,outer_reply1_notfilled hf,hl,?_⟩
        rw [outer_cover1_shape]
        have hnew : 2*(a+1) ≤ H := by
          simp only [Legal, height_drop_same, outer_height_one] at hl
          ((try dsimp only at *); omega)
        exact second_endpoint_invariant (.outer (a+1) d hnew hd)
          ⟨a+1,d,by ((try dsimp only at *); omega),rfl,hnew,hd⟩
  | c2 =>
      refine ⟨c3,classify (a1 a d),outer_reply2 H a d,cross.1,?_⟩
      rw [outer_event2_shape]
      exact second_endpoint_invariant (.event1 a d ha1 ha hd)
        (a12_classified h5 odd ha1 ha hd (Or.inl rfl))
  | c3 =>
      refine ⟨c2,classify (a2 a d),outer_reply3 H a d,cross.2.1,?_⟩
      rw [outer_event3_shape]
      exact second_endpoint_invariant (.event2 a d ha1 ha hd)
        (a12_classified h5 odd ha1 ha hd (Or.inr rfl))
  | c4 =>
      by_cases hf : height (drop (outerBoard a d) c4 Q) c4 = H
      · refine ⟨c2,classify (a4 a d),outer_reply4_filled hf,cross.2.2.2,?_⟩
        rw [outer_event4_shape]
        have he : 2*d+1 = H := by simpa using hf
        exact second_endpoint_invariant (.event4 a d ha he (by ((try dsimp only at *); omega)))
          (a4_classified h5 odd ha1 ha he)
      · have hl := outer_nonfill_reply_legal c4 hq hf
        refine ⟨c4,.outerWait,outer_reply4_notfilled hf,hl,?_⟩
        rw [outer_cover4_shape]
        have hnew : 2*(d+1) ≤ H := by
          simp only [Legal, height_drop_same, outer_height_four] at hl
          ((try dsimp only at *); omega)
        exact second_endpoint_invariant (.outer a (d+1) ha hnew)
          ⟨a,d+1,ha1,rfl,ha,hnew⟩

theorem delay_response {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    {b : Board} (hb : DelayFamily b) (q : Col) : SecondResponse H b q .delay := by
  rcases hb with ⟨d,hd,he⟩
  have hd1 : d ≤ 1 := by ((try dsimp only at *); omega)
  have hl : Legal H (drop b q Q) q := by
    rcases he with rfl | rfl <;> cases q <;>
      simp_all [Legal,height,a1,a2,board,drop] <;> ((try dsimp only at *); omega)
  have hn : ¬ Wins H (drop b q Q) Q := by
    rcases he with rfl | rfl
    · exact a1_Q_noQ H 1 d q
    · exact a2_Q_noQ H 1 d q
  refine ⟨hn,q,classify (drop (drop b q Q) q P),delay_reply H b q,hl,?_⟩
  rcases he with rfl | rfl
  · cases q with
    | c1 =>
        rw [a1_cover1_shape]
        apply second_endpoint_invariant (.event1 2 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
        exact a12_classified h5 odd (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (Or.inl rfl)
    | c2 =>
        rw [a1_cover2_shape]
        exact second_endpoint_invariant (.middle1 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
          (middle1_classified h5 odd hd1)
    | c3 =>
        rw [a1_cover3_shape]
        exact second_endpoint_invariant (.middle3 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
          (middle3_classified h5 odd hd1)
    | c4 =>
        rw [a1_cover4_shape]
        apply second_endpoint_invariant (.event1 1 (d+1) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
        exact a12_classified h5 odd (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (Or.inl rfl)
  · cases q with
    | c1 =>
        rw [a2_cover1_shape]
        apply second_endpoint_invariant (.event2 2 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
        exact a12_classified h5 odd (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (Or.inr rfl)
    | c2 =>
        rw [a2_cover2_shape]
        exact second_endpoint_invariant (.middle4 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
          (middle4_classified h5 odd hd1)
    | c3 =>
        rw [a2_cover3_shape]
        exact second_endpoint_invariant (.middle2 d (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
          (middle2_classified h5 odd hd1)
    | c4 =>
        rw [a2_cover4_shape]
        apply second_endpoint_invariant (.event2 1 (d+1) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)))
        exact a12_classified h5 odd (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (by ((try dsimp only at *); omega)) (Or.inr rfl)

theorem tail_to_claude {H : Nat} {b : Board} {ph : Phase}
    (h : TailInvariant H b ph) : ClaudeInvariant H b ph := by
  have hs := (tail_invariant_closed H).stateSafe b ph h
  refine ⟨hs.1,hs.2,?_⟩
  cases ph with
  | innerWait => exact False.elim h
  | outerWait => exact False.elim h
  | delay => exact False.elim h
  | candidate L ts => exact h
  | permanent => exact h

/-- The complete odd-height closure proof.  In particular there is no assumed
closure, nonloss theorem, C6 macro, or finite certificate among its arguments. -/
theorem claude_invariant_closed {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1) :
    ClosedInvariant H (ClaudeInvariant H) := by
  constructor
  · intro b ph h
    exact ⟨h.1,h.2.1⟩
  · intro b ph h live q legalQ
    cases ph with
    | innerWait =>
        rcases inner_response h5 odd h.2.2 q legalQ with ⟨hn,c,next,hr,hp,hi⟩
        exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inr hi⟩⟩
    | outerWait =>
        rcases outer_response h5 odd h.2.2 q legalQ with ⟨hn,c,next,hr,hp,hi⟩
        exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inr hi⟩⟩
    | delay =>
        rcases delay_response h5 odd h.2.2 q with ⟨hn,c,next,hr,hp,hi⟩
        exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inr hi⟩⟩
    | candidate L ts =>
        have ht : TailInvariant H b (.candidate L ts) := h.2.2
        rcases (tail_invariant_closed H).step b (.candidate L ts) ht live q legalQ with
          ⟨hn,hfull | response⟩
        · exact ⟨hn,Or.inl hfull⟩
        · rcases response with ⟨c,next,hr,hp,terminal | invariant⟩
          · exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inl terminal⟩⟩
          · exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inr (tail_to_claude invariant)⟩⟩
    | permanent =>
        have ht : TailInvariant H b .permanent := h.2.2
        rcases (tail_invariant_closed H).step b .permanent ht live q legalQ with
          ⟨hn,hfull | response⟩
        · exact ⟨hn,Or.inl hfull⟩
        · rcases response with ⟨c,next,hr,hp,terminal | invariant⟩
          · exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inl terminal⟩⟩
          · exact ⟨hn,Or.inr ⟨c,next,hr,hp,Or.inr (tail_to_claude invariant)⟩⟩

theorem claude_all_rounds_safe {H : Nat} (h5 : 5 ≤ H) (odd : H % 2 = 1)
    {b : Board} {ph : Phase} (h : ClaudeInvariant H b ph) : AllRoundsSafe H b ph :=
  invariant_all_rounds_safe (claude_invariant_closed h5 odd) h

#print axioms second_endpoint_structural
#print axioms inner_response
#print axioms outer_response
#print axioms delay_response
#print axioms claude_invariant_closed
#print axioms claude_all_rounds_safe
end OddHeight
