import experiments.FourColumnsOddGeometry

namespace Connect4.FourColumns

def fourTuple {α : Type} (a b c d : α) : Fin 4 → α :=
  fun i => match i.val with
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => d

def FiniteFour (h : Nat) (b : Board 4) (p : Player) : Prop :=
  ∃ x : Fin 4, ∃ y : Fin h,
    HasFourDir h b p (x : Int) (y : Int) 0 1 ∨
    HasFourDir h b p (x : Int) (y : Int) 1 0 ∨
    HasFourDir h b p (x : Int) (y : Int) 1 1 ∨
    HasFourDir h b p (x : Int) (y : Int) 1 (-1)

instance finiteFour_decidable (h : Nat) (b : Board 4) (p : Player) :
    Decidable (FiniteFour h b p) := by
  unfold FiniteFour HasFourDir
  infer_instance

theorem bounded_four_dir {h : Nat} {b : Board 4} {p : Player} {x y dx dy : Int}
    (hd : HasFourDir h b p x y dx dy) :
    ∃ c : Fin 4, ∃ r : Fin h, HasFourDir h b p (c : Int) (r : Int) dx dy := by
  have ht : cellAtInt h b x y = some p := by simpa using hd 0
  obtain ⟨c, hx, hy, hyh, _⟩ := cellAtInt_some ht
  refine ⟨c, ⟨y.toNat, by omega⟩, ?_⟩
  have hr : ((⟨y.toNat, by omega⟩ : Fin h) : Int) = y := by simp; omega
  simpa only [← hx, hr] using hd

theorem finiteFour_iff {h : Nat} {b : Board 4} {p : Player} :
    FiniteFour h b p ↔ HasFour h b p := by
  constructor
  · rintro ⟨x, y, hd | hd | hd | hd⟩
    · exact Or.inl ⟨x, y, hd⟩
    · exact Or.inr (Or.inl ⟨x, y, hd⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨x, y, hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x, y, hd⟩))
  · intro hf
    rcases hf with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
    · obtain ⟨c, r, h⟩ := bounded_four_dir hd
      exact ⟨c, r, Or.inl h⟩
    · obtain ⟨c, r, h⟩ := bounded_four_dir hd
      exact ⟨c, r, Or.inr (Or.inl h)⟩
    · obtain ⟨c, r, h⟩ := bounded_four_dir hd
      exact ⟨c, r, Or.inr (Or.inr (Or.inl h))⟩
    · obtain ⟨c, r, h⟩ := bounded_four_dir hd
      exact ⟨c, r, Or.inr (Or.inr (Or.inr h))⟩

instance four_decidable (h : Nat) (b : Board 4) (p : Player) :
    Decidable (HasFour h b p) :=
  decidable_of_iff (FastFour h b p) fastFour_iff

instance legal_decidable (h : Nat) (b : Board 4) (c : Fin 4) :
    Decidable (Legal h b c) := inferInstanceAs (Decidable ((b c).length < h))

instance valid_decidable (h : Nat) (b : Board 4) : Decidable (Valid h b) := by
  unfold Valid
  infer_instance

instance full_decidable (h : Nat) (b : Board 4) : Decidable (BoardFull h b) := by
  unfold BoardFull
  infer_instance

/-- Finite, fully kernel-checked strategy trees; sharing uses theorem references.
The scoring region may be shorter than the capacity. Both players use it. -/
inductive ControlTree (cap score : Nat) (p : Player) : Board 4 → Prop
  | won {b} : (¬ HasFour score b (opponent p)) → HasFour score b p →
      ControlTree cap score p b
  | full {b} : (¬ HasFour score b (opponent p)) → BoardFull cap b →
      ControlTree cap score p b
  | node {b} (reply : Fin 4 → Fin 4) :
      Valid cap b → toMove b = opponent p →
      (¬ HasFour score b (opponent p)) →
      (∀ c, Legal cap b c →
        ¬ HasFour score (play b c (opponent p)) (opponent p)) →
      (∀ c, Legal cap b c → ¬ BoardFull cap (play b c (opponent p)) →
        Legal cap (play b c (opponent p)) (reply c)) →
      (∀ c, Legal cap b c → ¬ BoardFull cap (play b c (opponent p)) →
        reply c = c ∨ (play b c (opponent p) c).length ≤ 2 ∨
          ¬ Legal cap (play b c (opponent p)) c) →
      (∀ c, Legal cap b c → ¬ BoardFull cap (play b c (opponent p)) →
        ControlTree cap score p (play (play b c (opponent p)) (reply c) p)) →
      ControlTree cap score p b

theorem ControlTree.no_enemy {cap score : Nat} {p : Player} {b : Board 4}
    (ht : ControlTree cap score p b) : ¬ HasFour score b (opponent p) := by
  cases ht <;> assumption

theorem safeFor_terminal' {h : Nat} {p : Player} {b : Board 4}
    (hn : ¬ HasFour h b (opponent p))
    (he : HasFour h b p ∨ BoardFull h b) (k : Nat) : SafeFor h p k b := by
  cases k with
  | zero => exact hn
  | succ k => exact ⟨hn, he.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

theorem ControlTree.real_safe {h : Nat} {p : Player} {b : Board 4}
    (ht : ControlTree h h p b) : CanAvoidLoss h p b := by
  intro k
  induction k using Nat.strong_induction_on generalizing b with
  | h k ih =>
    cases ht with
    | won hn hw => exact safeFor_terminal' hn (Or.inl hw) k
    | full hn hf => exact safeFor_terminal' hn (Or.inr hf) k
    | node reply hv htm hn hchild hlegal hcap hnext =>
      cases k with
      | zero => exact hn
      | succ k =>
        refine ⟨hn, Or.inr (Or.inr ?_)⟩
        rw [if_neg (by rw [htm]; exact Ne.symm (player_ne_opponent p)), htm]
        intro c hc
        have hn' := hchild c hc
        cases k with
        | zero => exact hn'
        | succ k =>
          by_cases hf : BoardFull h (play b c (opponent p))
          · exact safeFor_terminal' hn' (Or.inr hf) (k+1)
          · refine ⟨hn', Or.inr (Or.inr ?_)⟩
            have htm' : toMove (play b c (opponent p)) = p := by
              rw [toMove_play', htm, opponent_involutive]
            rw [if_pos htm', htm']
            exact ⟨reply c, hlegal c hc hf, ih k (by omega) (hnext c hc hf)⟩

#print axioms finiteFour_iff

end Connect4.FourColumns
