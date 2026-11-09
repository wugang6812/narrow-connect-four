import ReflectionKernel
import OddHeight.Arithmetic

namespace OddHeight
open Player Col

inductive Phase where
  | innerWait
  | outerWait
  | delay
  | candidate (line : Line) (targets : List Target)
  | permanent
  deriving DecidableEq, BEq, Repr

def hasPBool (b : Board) (L : Line) : Bool :=
  L.cells.any (fun x => stoneAt b x == some P)

def classify (b : Board) : Phase :=
  if hasPBool b rise then
    if hasPBool b down then .permanent else .candidate down [⟨c2,3⟩]
  else
    if hasPBool b down then .candidate rise [⟨c3,3⟩] else .delay

def settle (b : Board) : Phase → Phase
  | .delay => classify b
  | .candidate L ts =>
      if ts.any (fun t => stoneAt b (targetCell t) == some P) then .permanent
      else .candidate L ts
  | p => p

/-- The fallback search is restricted to the complement of J. -/
def firstAvailable (H : Nat) (b : Board) (ts : List Target) : List Col → Option Col
  | [] => none
  | c :: cs =>
      if height b c < H ∧ inJ ts c = false then some c else firstAvailable H b ts cs

theorem firstAvailable_sound {H : Nat} {b : Board} {ts : List Target}
    {cs : List Col} {c : Col} (found : firstAvailable H b ts cs = some c) :
    Legal H b c ∧ inJ ts c = false := by
  revert found
  induction cs with
  | nil => intro found; simp [firstAvailable] at found
  | cons d ds ih =>
      intro found
      by_cases hd : height b d < H ∧ inJ ts d = false
      · simp [firstAvailable, hd] at found
        cases found
        exact hd
      · simp [firstAvailable, hd] at found
        exact ih found

theorem firstAvailable_complete {H : Nat} {b : Board} {ts : List Target}
    {cs : List Col}
    (witness : ∃ c ∈ cs, height b c < H ∧ inJ ts c = false) :
    ∃ c, firstAvailable H b ts cs = some c := by
  revert witness
  induction cs with
  | nil =>
      intro witness
      rcases witness with ⟨c, hc, _⟩
      simp at hc
  | cons d ds ih =>
      intro witness
      by_cases hd : height b d < H ∧ inJ ts d = false
      · exact ⟨d, by simp [firstAvailable, hd]⟩
      · have rest : ∃ c ∈ ds, height b c < H ∧ inJ ts c = false := by
          rcases witness with ⟨c, hc, good⟩
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact False.elim (hd good)
          · exact ⟨c, hc, good⟩
        rcases ih rest with ⟨c, hc⟩
        exact ⟨c, by simpa [firstAvailable, hd] using hc⟩

/-- Given a legal Q move, choose a P move. Caller MUST test terminality before calling.
    Legality is an obligation, not silently repaired by a different move. -/
def rawReply (H : Nat) (b : Board) (q : Col) (ph : Phase) : Option (Col × Phase) :=
  let a := drop b q Q
  let filled := height a q == H
  match ph with
  | .innerWait =>
      match q with
      | c1 => some (q, .innerWait)
      | c2 => some (q, .candidate rowTwo [⟨c3,2⟩, ⟨c4,2⟩])
      | c3 => some (q, .permanent)
      | c4 => some (q, .candidate down [⟨c2,3⟩])
  | .outerWait =>
      match q with
      | c1 => if filled then some (c3, .delay) else some (c1, .outerWait)
      | c2 => some (c3, .delay)
      | c3 => some (c2, .delay)
      | c4 => if filled then some (c2, .delay) else some (c4, .outerWait)
  | .delay => some (q, .delay)
  | .candidate L ts =>
      if inJ ts q || !filled then some (q, .candidate L ts)
      else (firstAvailable H a ts allCols).map (fun c => (c, .candidate L ts))
  | .permanent =>
      if !filled then some (q, .permanent)
      else (firstAvailable H a [] allCols).map (fun c => (c, .permanent))

/-- Normalize the phase only AFTER P has played. -/
def reply (H : Nat) (b : Board) (q : Col) (ph : Phase) : Option (Col × Phase) :=
  (rawReply H b q ph).map fun (c, next) =>
    (c, settle (drop (drop b q Q) c P) next)

/-- Reflection is a coordinate map, not a claim that tie-breaking is unchanged. -/


@[simp] theorem orient_involutive (flipped : Bool) (c : Col) :
    orient flipped (orient flipped c) = c := by
  cases flipped <;> simp [orient]



def reflectedReply (H : Nat) (flipped : Bool) (b : Board) (q : Col) (ph : Phase) :=
  (reply H (logicalBoard flipped b) (orient flipped q) ph).map
    (fun (c, p) => (orient flipped c, p))

def secondOpening (q : Col) : Col × Phase × Bool :=
  match q with
  | c1 => (c1, .outerWait, false)
  | c2 => (c1, .innerWait, false)
  | c3 => (c4, .innerWait, true)
  | c4 => (c4, .outerWait, true)

def firstPhase (H : Nat) : Phase :=
  if H = 1 then .permanent
  else if H = 3 then .permanent
  else .candidate down [⟨c3,2⟩]

/-- Regression: when Q fills c4, fallback must skip the reserved c2 even though c2 is free. -/
example : rawReply 5
    (board [P,Q,P,Q,P] [Q] [P] [Q,P,Q,P]) c4
    (.candidate down [⟨c2,3⟩]) = some (c3, .candidate down [⟨c2,3⟩]) := by decide

example : firstPhase 1 = .permanent := by decide
example : firstPhase 3 = .permanent := by decide
example : firstPhase 5 = .candidate down [⟨c3,2⟩] := by decide

end OddHeight
