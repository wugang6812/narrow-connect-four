import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace Connect4

abbrev Width : Nat := 7
abbrev Height : Nat := 6
abbrev Column := Fin Width
abbrev Row := Fin Height

inductive Player : Type
  | black
  | white
  deriving DecidableEq, Repr

/-- 对手玩家：黑白互换。 -/
def opponent (p : Player) : Player :=
  match p with
  | .black => .white
  | .white => .black

/-- 换两次回到自己。`cases p <;> rfl` 的意思：
    对 `p` 做分类讨论（黑、白两种情况），每一种都用 `rfl`（定义相等）收尾。 -/
theorem opponent_involutive (p : Player) : opponent (opponent p) = p := by
  cases p <;> rfl

/-- A board maps each column to the list of stones already in that column,
    starting from the bottom. The list length is the current column height. -/
abbrev Board := Column → List Player

def emptyBoard : Board := fun _ => []

def height (b : Board) (c : Column) : Nat := (b c).length

def Legal (b : Board) (c : Column) : Prop := (b c).length < Height

def Full (b : Board) (c : Column) : Prop := (b c).length = Height

/-- Drop a stone into column `c`. It lands on top of the existing stones. -/
def play (b : Board) (c : Column) (p : Player) : Board :=
  Function.update b c ((b c) ++ [p])

/-- Access a cell by column/row. Returns `none` if the row is above the column height
    (i.e. empty) or if something is impossible. -/
def cellAt (b : Board) (c : Column) (r : Row) : Option Player :=
  if h : r.val < (b c).length then
    some ((b c).get ⟨r.val, h⟩)
  else
    none

/-- Access the cell at integer coordinates, returning `none` if out of bounds. -/
def cellAtInt (b : Board) (c r : Int) : Option Player :=
  if hc : 0 ≤ c ∧ c < (Width : Int) then
    if hr : 0 ≤ r ∧ r < (Height : Int) then
      let c' : Column := ⟨c.toNat, by omega⟩
      let r' : Row := ⟨r.toNat, by omega⟩
      cellAt b c' r'
    else
      none
  else
    none

/-- Four consecutive cells in a straight line (given a direction) all contain `p`. -/
def HasFourDir (b : Board) (p : Player) (c r dr dc : Int) : Prop :=
  ∀ i : Fin 4, cellAtInt b (c + (i : Int) * dr) (r + (i : Int) * dc) = some p

/-- The four directions that cover all possible four-in-a-row lines. -/
def HasFour (b : Board) (p : Player) : Prop :=
  (∃ c r : Int, HasFourDir b p c r 0 1) ∨
  (∃ c r : Int, HasFourDir b p c r 1 0) ∨
  (∃ c r : Int, HasFourDir b p c r 1 1) ∨
  (∃ c r : Int, HasFourDir b p c r 1 (-1))

/-- A drawn (full) board is one where every column has height 6. -/
def BoardFull (b : Board) : Prop := ∀ c : Column, (b c).length = Height

-- 一些最基础的可证明事实

theorem play_height (b : Board) (c : Column) (p : Player) :
    height (play b c p) c = (b c).length + 1 := by
  simp [height, play]

theorem play_other_column (b : Board) (c c' : Column) (p : Player) (h : c ≠ c') :
    (play b c p) c' = b c' := by
  by_cases hEq : c' = c
  · exact False.elim (h hEq.symm)
  · simp [play, Function.update, hEq]

theorem legal_iff_not_full (b : Board) (c : Column) (h6 : (b c).length ≤ 6) :
    Legal b c ↔ ¬ Full b c := by
  constructor
  · intro h
    intro hf
    have hlegal : (b c).length < 6 := by simpa [Legal] using h
    have hfull : (b c).length = 6 := by simpa [Full] using hf
    omega
  · intro h
    by_contra hnot
    have hnotlegal : ¬ (b c).length < 6 := by simpa [Legal] using hnot
    have hfull : (b c).length = 6 := by omega
    exact h (by simpa [Full] using hfull)

/-- A board is valid if no column exceeds the physical height. -/
def Valid (b : Board) : Prop := ∀ c : Column, (b c).length ≤ Height

/-- A move is a winning move if after dropping there, the player has four in a row. -/
def IsWinningMove (b : Board) (c : Column) (p : Player) : Prop :=
  HasFour (play b c p) p

theorem emptyBoard_valid : Valid emptyBoard := by
  intro c
  simp [Valid, emptyBoard]

theorem emptyBoard_not_has_four (p : Player) : ¬ HasFour emptyBoard p := by
  simp [HasFour, HasFourDir, cellAtInt, cellAt, emptyBoard]

theorem play_valid (b : Board) (c : Column) (p : Player)
    (hv : Valid b) (hlegal : (b c).length < Height) :
    Valid (play b c p) := by
  intro c'
  by_cases hEq : c' = c
  · subst c'
    have hlen : (b c).length < 6 := hlegal
    simp [play]
    omega
  · have hne : c ≠ c' := by
      intro hcontra
      exact hEq hcontra.symm
    have hsame := play_other_column b c c' p hne
    rw [hsame]
    exact hv c'



/-- Total number of stones on the board. -/
def totalStones (b : Board) : Nat :=
  ∑ c : Column, (b c).length

/-- The player to move: even number of stones means Black starts. -/
def toMove (b : Board) : Player :=
  if totalStones b % 2 = 0 then Player.black else Player.white

/-- Number of cells still remaining (used as a decreasing measure for recursion). -/
def remaining (b : Board) : Nat :=
  Width * Height - totalStones b





/-- `WinningWithin b n`：设行动方为 `toMove b`。行动方能在「我走一着 + 对方任意合法应着」
    重复 `n` 轮的框架内，**先于对方**连成四子。三个语义要点：
    1. 每层入口要求对方尚未连四 —— 四子棋是谁先连四谁赢、对局立即结束，
       对方已有四连则谈「强制获胜」没有意义；
    2. 对方应着后若连成四，会被递归调用下一层的入口守卫直接拒绝（我方已输掉竞速）；
    3. 我方落子后要求棋盘未满 —— 否则对方没有任何合法应着，
       `∀ d, Legal … d → …` 会「空真」（前提为假则蕴含式恒真），把和棋误判成胜。 -/
def WinningWithin : Board → Nat → Prop
  | b, 0 =>
      ¬ HasFour b (opponent (toMove b)) ∧
      ∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b)
  | b, n+1 =>
      ¬ HasFour b (opponent (toMove b)) ∧
      ((∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b)) ∨
       (∃ c : Column, Legal b c ∧
          ¬ BoardFull (play b c (toMove b)) ∧
          ∀ d : Column,
            Legal (play b c (toMove b)) d →
              WinningWithin
                (play (play b c (toMove b)) d (toMove (play b c (toMove b))))
                n))

/-- 局面 `b` 上行动方有强制胜利：存在某个深度上界 `n` 使 `WinningWithin b n` 成立。
    意义上默认 `b` 是「活」局面（双方都还没有四连）。 -/
def HasForcedWin (b : Board) : Prop :=
  ∃ n : Nat, WinningWithin b n

/-- 深度为 0 时，强制胜利就是「对方尚未连四，且我有一步制胜」。
    证明是 `rfl`：两边按定义展开后是同一个命题（定义相等）。 -/
theorem WinningWithin_zero (b : Board) :
    WinningWithin b 0 ↔
      (¬ HasFour b (opponent (toMove b)) ∧
       ∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b)) := by
  rfl

/-- 单调性：`n` 轮内能强制获胜，则 `n+1` 轮内也能。
    证明对 `n` 归纳，且必须让 `b` 一起泛化（`induction … generalizing …`），
    因为递归调用发生在**另一个局面**上——归纳假设要对所有局面可用才有用。 -/
theorem WinningWithin_mono (n : Nat) :
    ∀ b : Board, WinningWithin b n → WinningWithin b (n + 1) := by
  induction n with
  | zero =>
      intro b h
      exact ⟨h.1, Or.inl h.2⟩
  | succ n ih =>
      intro b h
      refine ⟨h.1, ?_⟩
      rcases h.2 with hw | ⟨c, hc, hnf, hall⟩
      · exact Or.inl hw
      · exact Or.inr ⟨c, hc, hnf, fun d hd => ih _ (hall d hd)⟩

/-- 活局面：双方都没有四连，对局尚未结束。
    「谁先连四谁赢」意味着四子棋的真实对局只会经过活局面。 -/
def Live (b : Board) : Prop :=
  ¬ HasFour b Player.black ∧ ¬ HasFour b Player.white

/-- `AvoidLossWithin b n`：行动方能在 n 轮框架内保证**不输**——
    要么自己先连成四，要么棋盘下满无人连四（和棋）。与 `WinningWithin` 对照：
    - 成功出口从 1 个变 3 个：一步制胜 / 棋盘已满（天然和棋）/
      我这手下完棋盘恰好下满（也是和棋）。注意「棋盘满」在这里是**终点线**，
      而在 `WinningWithin` 里「我下完后棋盘未满」是**刹车**——
      同一个事实在两个目标下意义相反；
    - 递归出口结构相同：对手任意应着后继续保证不输
      （对手若连成四，下一层的入口守卫会拒绝该线路）。 -/
def AvoidLossWithin : Board → Nat → Prop
  | b, 0 =>
      ¬ HasFour b (opponent (toMove b)) ∧
      ((∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b)) ∨ BoardFull b)
  | b, n+1 =>
      ¬ HasFour b (opponent (toMove b)) ∧
      ((∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b)) ∨ BoardFull b ∨
       (∃ c : Column, Legal b c ∧
          (BoardFull (play b c (toMove b)) ∨
           ∀ d : Column,
             Legal (play b c (toMove b)) d →
               AvoidLossWithin
                 (play (play b c (toMove b)) d (toMove (play b c (toMove b))))
                 n)))

/-- 行动方可以保平（不输）：存在深度上界 `n` 使 `AvoidLossWithin b n` 成立。
    注意「保平」包含「赢」——赢是不输的特例；真正的三分解要等确定性定理。 -/
def CanForceDraw (b : Board) : Prop :=
  ∃ n : Nat, AvoidLossWithin b n

/-- 主定理（今天）：能赢必然能不输。强制胜利蕴含强制保平。
    证明结构与 `WinningWithin_mono` 完全同构：对 `n` 归纳、局面泛化，
    递归分支里用归纳假设把「n 轮内胜」升级成「n 轮内不输」。 -/
theorem WinningWithin_imp (n : Nat) :
    ∀ b : Board, WinningWithin b n → AvoidLossWithin b n := by
  induction n with
  | zero =>
      intro b ⟨hg, hw⟩
      exact ⟨hg, Or.inl hw⟩
  | succ n ih =>
      intro b ⟨hg, h⟩
      refine ⟨hg, ?_⟩
      rcases h with hw | ⟨c, hc, hnf, hall⟩
      · exact Or.inl hw
      · exact Or.inr (Or.inr ⟨c, hc, Or.inr (fun d hd => ih _ (hall d hd))⟩)

-- ── 格子工具箱：落子如何改变四连（路线②地基） ────────────────────────

/-- 异列的格子不因落子改变。 -/
theorem cellAt_play_other (b : Board) (c c' : Column) (p : Player) (r : Row)
    (h : c' ≠ c) :
    cellAt (play b c p) c' r = cellAt b c' r := by
  simp only [cellAt]
  rw [play_other_column b c c' p (fun hh => h hh.symm)]

/-- 同列旧高度以下的格子不变（追加只动顶端）。 -/
theorem cellAt_play_below (b : Board) (c : Column) (p : Player) (r : Row)
    (hr : r.val < (b c).length) :
    cellAt (play b c p) c r = cellAt b c r := by
  have hlen : (b c ++ [p]).length = (b c).length + 1 := by simp
  have h1 : r.val < (b c ++ [p]).length := by omega
  have hu : play b c p c = b c ++ [p] := by simp [play, Function.update]
  unfold cellAt
  rw [hu, dif_pos h1, dif_pos hr]
  congr 1
  exact List.getElem_append_left hr

/-- 新顶端那格恰好是新落的子。 -/
theorem cellAt_play_top (b : Board) (c : Column) (p : Player)
    (h : (b c).length < Height) :
    cellAt (play b c p) c ⟨(b c).length, h⟩ = some p := by
  have hlen : (b c ++ [p]).length = (b c).length + 1 := by simp
  have h1 : (b c).length < (b c ++ [p]).length := by omega
  have hu : play b c p c = b c ++ [p] := by simp [play, Function.update]
  unfold cellAt
  rw [hu, dif_pos h1]
  congr 1
  simp

/-- 旧高度以上的格子（落子后）依然是空的。 -/
theorem cellAt_play_above (b : Board) (c : Column) (p : Player) (r : Row)
    (hr : (b c).length < r.val) :
    cellAt (play b c p) c r = none := by
  have hlen : (b c ++ [p]).length = (b c).length + 1 := by simp
  have hn : ¬ (r.val < (b c ++ [p]).length) := by omega
  have hu : play b c p c = b c ++ [p] := by simp [play, Function.update]
  unfold cellAt
  rw [hu, dif_neg hn]

/-- 界内坐标版的 `cellAtInt` 展开。 -/
theorem cellAtInt_eq (b : Board) (x y : Int)
    (hx : 0 ≤ x ∧ x < (Width : Int)) (hy : 0 ≤ y ∧ y < (Height : Int)) :
    cellAtInt b x y = cellAt b ⟨x.toNat, by omega⟩ ⟨y.toNat, by omega⟩ := by
  unfold cellAtInt
  rw [dif_pos hx, dif_pos hy]

/-- 落子后某格取值若非新子本身，则该格落子前后取值不变。 -/
theorem cellAtInt_play (b : Board) (c : Column) (p q : Player) (x y : Int)
    (h : cellAtInt (play b c p) x y = some q) (hq : q ≠ p) :
    cellAtInt b x y = some q := by
  by_cases hx : 0 ≤ x ∧ x < (Width : Int)
  · by_cases hy : 0 ≤ y ∧ y < (Height : Int)
    · rw [cellAtInt_eq _ x y hx hy] at h ⊢
      by_cases hxc : x.toNat = c.val
      · have hc' : (⟨x.toNat, by omega⟩ : Column) = c := Fin.ext hxc
        rw [hc'] at h ⊢
        by_cases hyt : y.toNat < (b c).length
        · rw [cellAt_play_below b c p ⟨y.toNat, by omega⟩ hyt] at h
          exact h
        · exfalso
          by_cases hye : y.toNat = (b c).length
          · have hrow : (⟨y.toNat, by omega⟩ : Row)
                = ⟨(b c).length, by omega⟩ := Fin.ext hye
            rw [hrow] at h
            rw [cellAt_play_top b c p (by omega)] at h
            exact hq (Option.some.inj h).symm
          · have hyg : (b c).length < y.toNat := by omega
            rw [cellAt_play_above b c p ⟨y.toNat, by omega⟩ hyg] at h
            simp at h
      · have hc' : (⟨x.toNat, by omega⟩ : Column) ≠ c :=
          fun hh => hxc (congrArg Fin.val hh)
        rw [cellAt_play_other b c ⟨x.toNat, by omega⟩ p ⟨y.toNat, by omega⟩
          (fun hh => hxc (congrArg Fin.val hh))] at h
        exact h
    · unfold cellAtInt at h
      rw [dif_pos hx, dif_neg hy] at h
      simp at h
  · unfold cellAtInt at h
    rw [dif_neg hx] at h
    simp at h

/-- 落子前已有子的格子，落子后取值不变（新顶端原来必然是空）。 -/
theorem cellAtInt_play_of (b : Board) (c : Column) (p' p : Player) (x y : Int)
    (h : cellAtInt b x y = some p) : cellAtInt (play b c p') x y = some p := by
  by_cases hx : 0 ≤ x ∧ x < (Width : Int)
  · by_cases hy : 0 ≤ y ∧ y < (Height : Int)
    · rw [cellAtInt_eq _ x y hx hy] at h ⊢
      by_cases hxc : x.toNat = c.val
      · have hc' : (⟨x.toNat, by omega⟩ : Column) = c := Fin.ext hxc
        rw [hc'] at h ⊢
        by_cases hyt : y.toNat < (b c).length
        · rw [cellAt_play_below b c p' ⟨y.toNat, by omega⟩ hyt]
          exact h
        · exfalso
          unfold cellAt at h
          rw [dif_neg (by omega)] at h
          simp at h
      · have hc' : (⟨x.toNat, by omega⟩ : Column) ≠ c :=
          fun hh => hxc (congrArg Fin.val hh)
        rw [cellAt_play_other b c ⟨x.toNat, by omega⟩ p' ⟨y.toNat, by omega⟩
          (fun hh => hxc (congrArg Fin.val hh))]
        exact h
    · unfold cellAtInt at h
      rw [dif_pos hx, dif_neg hy] at h
      simp at h
  · unfold cellAtInt at h
    rw [dif_neg hx] at h
    simp at h

theorem hasFourDir_play_of_ne (b : Board) (c : Column) (p q : Player) (hq : q ≠ p)
    (x y dx dy : Int) (h : HasFourDir (play b c p) q x y dx dy) :
    HasFourDir b q x y dx dy := by
  intro i
  exact cellAtInt_play b c p q _ _ (h i) hq

/-- 他人的四连不因我的落子而出现（落子后出现的他人四连，落子前就在）。 -/
theorem hasFour_play_of_ne (b : Board) (c : Column) (p q : Player) (hq : q ≠ p)
    (h : HasFour (play b c p) q) : HasFour b q := by
  rcases h with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · exact Or.inl ⟨x, y, hasFourDir_play_of_ne b c p q hq x y 0 1 hd⟩
  · exact Or.inr (Or.inl ⟨x, y, hasFourDir_play_of_ne b c p q hq x y 1 0 hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, hasFourDir_play_of_ne b c p q hq x y 1 1 hd⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y,
      hasFourDir_play_of_ne b c p q hq x y 1 (-1) hd⟩))

theorem hasFourDir_play_of (b : Board) (c : Column) (p' p : Player) (x y dx dy : Int)
    (h : HasFourDir b p x y dx dy) : HasFourDir (play b c p') p x y dx dy := by
  intro i
  exact cellAtInt_play_of b c p' p _ _ (h i)

/-- ★ 四连单调性：已有的四连不会被任何落子摧毁。路线②的第一块砖，
    也是"局面只会往有子的方向演化"这一直觉的严格化。 -/
theorem hasFour_play (b : Board) (c : Column) (p' p : Player) (h : HasFour b p) :
    HasFour (play b c p') p := by
  rcases h with ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩ | ⟨x, y, hd⟩
  · exact Or.inl ⟨x, y, hasFourDir_play_of b c p' p x y 0 1 hd⟩
  · exact Or.inr (Or.inl ⟨x, y, hasFourDir_play_of b c p' p x y 1 0 hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, hasFourDir_play_of b c p' p x y 1 1 hd⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y,
      hasFourDir_play_of b c p' p x y 1 (-1) hd⟩))

/-- 活局面在「落子未制胜」时保持活：对手的四连不会凭我的落子出现。 -/
theorem live_play (b : Board) (c : Column) (p : Player) (hl : Live b)
    (hnm : ¬ HasFour (play b c p) p) : Live (play b c p) := by
  obtain ⟨h1, h2⟩ := hl
  refine ⟨?_, ?_⟩
  · cases p with
    | black => exact hnm
    | white =>
        exact fun hf => h1 (hasFour_play_of_ne b c Player.white Player.black (by decide) hf)
  · cases p with
    | black =>
        exact fun hf => h2 (hasFour_play_of_ne b c Player.black Player.white (by decide) hf)
    | white => exact hnm

-- ── 基础引理：奇偶与轮换 ──────────────────────────────────────────────

/-- 落一子，棋子总数恰好加一。 -/
theorem totalStones_play (b : Board) (c : Column) (p : Player) :
    totalStones (play b c p) = totalStones b + 1 := by
  classical
  have key : ∀ c' : Column,
      ((Function.update b c ((b c) ++ [p])) c').length
        = (b c').length + (if c' = c then 1 else 0) := by
    intro c'
    by_cases h : c' = c
    · subst h
      simp [Function.update, List.length_append]
    · simp [Function.update, h]
  simp only [totalStones, play]
  rw [Finset.sum_congr rfl (fun c' _ => key c'), Finset.sum_add_distrib]
  simp

/-- 落一子后轮到对手：行动方由棋子总数的奇偶决定，总数 +1 恰好翻转黑白。 -/
theorem toMove_play (b : Board) (c : Column) (p : Player) :
    toMove (play b c p) = opponent (toMove b) := by
  unfold toMove
  rw [totalStones_play]
  by_cases h : totalStones b % 2 = 0
  · have h1 : (totalStones b + 1) % 2 = 1 := by omega
    simp [h, h1, opponent]
  · have h1 : (totalStones b + 1) % 2 = 0 := by omega
    simp [h, h1, opponent]

-- ── 棋盘有限性：游戏必然终止 ──────────────────────────────────────────

/-- 有效棋盘上棋子总数不超过 42（7 列 × 6 行）。 -/
theorem Valid_totalStones (b : Board) (hv : Valid b) : totalStones b ≤ 42 := by
  have h1 : ∑ c : Column, (b c).length ≤ ∑ _c : Column, (Height : Nat) :=
    Finset.sum_le_sum fun c _ => hv c
  have h2 : (∑ _c : Column, (Height : Nat)) = 42 := by decide
  have h3 : totalStones b = ∑ c : Column, (b c).length := rfl
  omega

/-- 还有子可下的有效棋盘，棋子总数至多 41（借助"落一子后仍有效"传递）。 -/
theorem Valid_legal_totalStones (b : Board) (c : Column) (hv : Valid b)
    (hl : Legal b c) : totalStones b ≤ 41 := by
  have h1 := Valid_totalStones (play b c (toMove b))
    (play_valid b c (toMove b) hv hl)
  rw [totalStones_play] at h1
  omega

/-- 没满的有效棋盘总有子可下——顺手拆掉一个潜在的空真来源。 -/
theorem not_full_exists_legal (b : Board) (hv : Valid b) (h : ¬ BoardFull b) :
    ∃ c : Column, Legal b c := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  intro c
  have hb : (b c).length ≤ Height := hv c
  have hn : ¬((b c).length < Height) := hcon c
  omega

/-- 「压缩」引理：深度 m+1 的强制胜利若声称需要超出棋盘容量的空间
    （棋数 + 2(m+1) ≥ 42），就能压成深度 m 的强制胜利。
    深处的着法没有格子可落，递归在满盘处自然截断。 -/
theorem win_compress (m : Nat) :
    ∀ b : Board, Valid b → WinningWithin b (m + 1) →
      totalStones b + 2 * (m + 1) ≥ 42 → WinningWithin b m := by
  induction m with
  | zero =>
      intro b hv hW hfull
      obtain ⟨hg, h⟩ := hW
      rcases h with ⟨c₀, hc₀, hwin⟩ | ⟨c₀, hc₀, hnf, hall⟩
      · exact ⟨hg, c₀, hc₀, hwin⟩
      · exfalso
        have hv1 : Valid (play b c₀ (toMove b)) :=
          play_valid b c₀ (toMove b) hv hc₀
        obtain ⟨d, hd⟩ := not_full_exists_legal _ hv1 hnf
        have hv2 : Valid (play (play b c₀ (toMove b)) d
            (toMove (play b c₀ (toMove b)))) :=
          play_valid _ d _ hv1 hd
        obtain ⟨_, c₁, hc₁, _⟩ := hall d hd
        have h41 := Valid_legal_totalStones _ c₁ hv2 hc₁
        rw [totalStones_play, totalStones_play] at h41
        omega
  | succ m ih =>
      intro b hv hW hfull
      obtain ⟨hg, h⟩ := hW
      rcases h with ⟨c₀, hc₀, hwin⟩ | ⟨c₀, hc₀, hnf, hall⟩
      · exact ⟨hg, Or.inl ⟨c₀, hc₀, hwin⟩⟩
      · refine ⟨hg, Or.inr ⟨c₀, hc₀, hnf, ?_⟩⟩
        intro d hd
        have hv1 : Valid (play b c₀ (toMove b)) :=
          play_valid b c₀ (toMove b) hv hc₀
        have hv2 : Valid (play (play b c₀ (toMove b)) d
            (toMove (play b c₀ (toMove b)))) :=
          play_valid _ d _ hv1 hd
        exact ih _ hv2 (hall d hd) (by rw [totalStones_play, totalStones_play]; omega)

/-- 超过 20 轮的深度都能压回 20 轮。 -/
theorem win_beyond20 (k : Nat) :
    ∀ b : Board, Valid b → WinningWithin b (20 + k) → WinningWithin b 20 := by
  induction k with
  | zero => intro _b _hv hW; exact hW
  | succ k ih =>
      intro b hv hW
      have hstep : WinningWithin b (20 + k) :=
        win_compress (20 + k) b hv hW (by omega)
      exact ih b hv hstep

/-- 单调性（范围版）：n ≤ m 时，n 轮能胜则 m 轮也能。 -/
theorem WinningWithin_mono_upto (n : Nat) :
    ∀ (m : Nat) (b : Board), n ≤ m → WinningWithin b n → WinningWithin b m := by
  intro m
  induction m with
  | zero =>
      intro b hn hW
      have h0 : n = 0 := by omega
      subst h0
      exact hW
  | succ m ih =>
      intro b hn hW
      by_cases h : n ≤ m
      · exact WinningWithin_mono m b (ih b h hW)
      · have heq : n = m + 1 := by omega
        subst heq
        exact hW

/-- 主坍缩定理：有效棋盘上，「存在强制胜利」⇔「20 轮内强制胜利」。
    那个折磨人的 `∃ n` 从此钉死在 20 上——覆盖性证明的量词障碍就此拆除。 -/
theorem HasForcedWin_iff_20 (b : Board) (hv : Valid b) :
    HasForcedWin b ↔ WinningWithin b 20 := by
  constructor
  · intro ⟨n, hn⟩
    by_cases hle : n ≤ 20
    · exact WinningWithin_mono_upto n 20 b hle hn
    · have hk : 20 + (n - 20) = n := by omega
      rw [← hk] at hn
      exact win_beyond20 (n - 20) b hv hn
  · intro h
    exact ⟨20, h⟩

-- ── 参考解答（原课后题）：不输的单调性 ────────────────────────────────
-- 骨架与 WinningWithin_mono 相同；新机关只有一处：setup 分支里的
-- 「盘满 ∨ 递归」要先拆一次再分头送进目标的左右口袋。
theorem AvoidLossWithin_mono (n : Nat) :
    ∀ b : Board, AvoidLossWithin b n → AvoidLossWithin b (n + 1) := by
  induction n with
  | zero =>
      intro b ⟨hg, h⟩
      rcases h with hw | hf
      · exact ⟨hg, Or.inl hw⟩
      · exact ⟨hg, Or.inr (Or.inl hf)⟩
  | succ n ih =>
      intro b ⟨hg, h⟩
      refine ⟨hg, ?_⟩
      rcases h with hw | hf | ⟨c, hc, hall⟩
      · exact Or.inl hw
      · exact Or.inr (Or.inl hf)
      · refine Or.inr (Or.inr ⟨c, hc, ?_⟩)
        rcases hall with hf | hall
        · exact Or.inl hf
        · exact Or.inr (fun d hd => ih _ (hall d hd))

-- ── 排他性：两个玩家不可能同时必胜 ────────────────────────────────────

/-- 我的一步制胜棋走完后，对手不可能再有强制胜利：
    我已经连成四，而 `WinningWithin` 的入口守卫恰恰要求"先手方的对手
    （也就是我）尚未连四"。 -/
theorem winning_move_blocks_opponent (b : Board) (c : Column)
    (hwin : IsWinningMove b c (toMove b)) :
    ¬ HasForcedWin (play b c (toMove b)) := by
  intro ⟨m, hm⟩
  cases m
  all_goals
    obtain ⟨hg, _⟩ := hm
    simp only [toMove_play] at hg
    rw [opponent_involutive] at hg
    exact hg hwin

/-- 两步版：当前行动方的制胜应手 `e` 走完后（对手先走一手的前提下），
    谁也无法在那个局面声称强制胜利。 -/
theorem two_move_win_blocks (b : Board) (c e : Column)
    (hwin : IsWinningMove (play b c (toMove b)) e (toMove (play b c (toMove b))))
    (m : Nat) :
    ¬ WinningWithin
        (play (play b c (toMove b)) e (toMove (play b c (toMove b)))) m := by
  intro hm
  cases m
  all_goals
    obtain ⟨hg, _⟩ := hm
    simp only [toMove_play] at hg hwin
    rw [opponent_involutive] at hg
    exact hg hwin

/-- 核心碰撞引理：若当前行动方的**每一手**都会让对手在 n 轮内强制获胜，
    那么当前行动方在此局面不可能有任何深度的强制胜利。
    对 n 归纳；imm 制胜情形由上面的守卫碰撞引理直接掐灭，
    setup 对 setup 情形则用归纳假设在（n-1, 任意深度）处收口。 -/
theorem all_moves_lose_not_win (n : Nat) :
    ∀ m : Nat, ∀ b : Board,
      (∀ d : Column, Legal b d → WinningWithin (play b d (toMove b)) n) →
      ¬ WinningWithin b m := by
  induction n with
  | zero =>
      intro m b hall hW
      cases m with
      | zero =>
          obtain ⟨_, d₀, hd₀, hwin⟩ := hW
          exact winning_move_blocks_opponent b d₀ hwin ⟨0, hall d₀ hd₀⟩
      | succ m =>
          obtain ⟨_, h⟩ := hW
          rcases h with ⟨d₀, hd₀, hwin⟩ | ⟨d₁, hd₁, _, hall'⟩
          · exact winning_move_blocks_opponent b d₀ hwin ⟨0, hall d₀ hd₀⟩
          · obtain ⟨_, e₀, he₀, hwin⟩ := hall d₁ hd₁
            exact two_move_win_blocks b d₁ e₀ hwin m (hall' e₀ he₀)
  | succ n ih =>
      intro m b hall hW
      cases m with
      | zero =>
          obtain ⟨_, d₀, hd₀, hwin⟩ := hW
          exact winning_move_blocks_opponent b d₀ hwin ⟨n + 1, hall d₀ hd₀⟩
      | succ m =>
          obtain ⟨_, h⟩ := hW
          rcases h with ⟨d₀, hd₀, hwin⟩ | ⟨d₁, hd₁, _, hall'⟩
          · exact winning_move_blocks_opponent b d₀ hwin ⟨n + 1, hall d₀ hd₀⟩
          · obtain ⟨_, h2⟩ := hall d₁ hd₁
            rcases h2 with ⟨e₀, he₀, hwin⟩ | ⟨e₁, he₁, _, hnew⟩
            · exact two_move_win_blocks b d₁ e₀ hwin m (hall' e₀ he₀)
            · exact ih m _ hnew (hall' e₁ he₁)

/-- 强制胜的策略里必藏一手"安全棋"：走它之后，对手不再有强制胜利。 -/
theorem winning_has_safe_move (n : Nat) :
    ∀ b : Board, WinningWithin b n →
      ∃ c : Column, Legal b c ∧ ¬ HasForcedWin (play b c (toMove b)) := by
  induction n with
  | zero =>
      intro b ⟨_, c₀, hc₀, hwin⟩
      exact ⟨c₀, hc₀, winning_move_blocks_opponent b c₀ hwin⟩
  | succ n _ih =>
      intro b ⟨_, h⟩
      rcases h with ⟨c₀, hc₀, hwin⟩ | ⟨c₀, hc₀, _, hall⟩
      · exact ⟨c₀, hc₀, winning_move_blocks_opponent b c₀ hwin⟩
      · refine ⟨c₀, hc₀, ?_⟩
        intro ⟨m, hm⟩
        exact all_moves_lose_not_win n m (play b c₀ (toMove b)) hall hm

/-- 对手强制胜（从行动方视角看是强制败）：还有子可下，但无论走哪一列，
    落子后的局面对手都有强制胜利。`∃ 合法着法` 是防空真的第三次出场：
    满盘活局没有合法着法，若去掉这半句，`∀` 会空真地把和棋判成必败。 -/
def ForcedLoss (b : Board) : Prop :=
  (∃ c : Column, Legal b c) ∧
  ∀ c : Column, Legal b c → HasForcedWin (play b c (toMove b))

/-- 排他性：我若 n 轮内能强制胜，则我不是强制败。 -/
theorem win_not_forcedLoss (n : Nat) (b : Board) (hW : WinningWithin b n) :
    ¬ ForcedLoss b := by
  intro ⟨_, hall⟩
  obtain ⟨c, hc, hsafe⟩ := winning_has_safe_move n b hW
  exact hsafe (hall c hc)

/-- 打包到 ∃ 层面：强制胜 ⇒ 强制保平；强制胜与强制败互斥。 -/
theorem HasForcedWin_imp (b : Board) (h : HasForcedWin b) : CanForceDraw b := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, WinningWithin_imp n b hn⟩

theorem HasForcedWin_not_forcedLoss (b : Board) (h : HasForcedWin b) :
    ¬ ForcedLoss b := by
  obtain ⟨n, hn⟩ := h
  exact win_not_forcedLoss n b hn

-- ── 覆盖性：Zermelo 收口 ──────────────────────────────────────────────

/-- 活局面没有任何人的四连。 -/
theorem live_no_four (b : Board) (hl : Live b) (p : Player) : ¬ HasFour b p := by
  cases p with
  | black => exact hl.1
  | white => exact hl.2

/-- 不输的单调性（范围版）。 -/
theorem AvoidLossWithin_mono_upto (n : Nat) :
    ∀ (m : Nat) (b : Board), n ≤ m → AvoidLossWithin b n → AvoidLossWithin b m := by
  intro m
  induction m with
  | zero =>
      intro b hn h
      have h0 : n = 0 := by omega
      subst h0
      exact h
  | succ m ih =>
      intro b hn h
      by_cases hle : n ≤ m
      · exact AvoidLossWithin_mono m b (ih b hle h)
      · have heq : n = m + 1 := by omega
        subst heq
        exact h

/-- 深度均匀化：Column 只有 7 列，「每个应手各自存在保平深度」可以汇成
    「一个公共深度」——取全体见证之和作上界，再用单调性抬齐。 -/
theorem exists_uniform_depth (b : Board) (c : Column)
    (hall : ∀ d : Column, Legal (play b c (toMove b)) d →
      ∃ m : Nat, AvoidLossWithin
        (play (play b c (toMove b)) d (toMove (play b c (toMove b)))) m) :
    ∃ K : Nat, ∀ d : Column, Legal (play b c (toMove b)) d →
      AvoidLossWithin
        (play (play b c (toMove b)) d (toMove (play b c (toMove b)))) K := by
  classical
  have hall' : ∀ d : Column, ∃ m : Nat, Legal (play b c (toMove b)) d →
      AvoidLossWithin
        (play (play b c (toMove b)) d (toMove (play b c (toMove b)))) m := by
    intro d
    by_cases hd : Legal (play b c (toMove b)) d
    · obtain ⟨m, hm⟩ := hall d hd
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun hcon => absurd hcon hd⟩
  choose f hf using hall'
  refine ⟨∑ d : Column, f d, fun d hd => ?_⟩
  have hle : f d ≤ ∑ d' : Column, f d' :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
  exact AvoidLossWithin_mono_upto (f d) _ _ hle (hf d hd)

/-- 覆盖性主证明：对燃料 M 强归纳（棋数 + M = 42）。
    非强制胜 ⇒ 强制败或可保平。 -/
theorem cover_step (M : Nat)
    (ih : ∀ K : Nat, K < M → ∀ b : Board, Valid b →
      ¬ HasFour b (opponent (toMove b)) → totalStones b + K = 42 →
      ¬ HasForcedWin b → ForcedLoss b ∨ CanForceDraw b) :
    ∀ b : Board, Valid b → ¬ HasFour b (opponent (toMove b)) →
      totalStones b + M = 42 → ¬ HasForcedWin b →
      ForcedLoss b ∨ CanForceDraw b := by
  intro b hv hguard hstones hnw
  by_cases hfull : BoardFull b
  · right
    exact ⟨0, hguard, Or.inr hfull⟩
  · obtain ⟨c₀, hc₀⟩ := not_full_exists_legal b hv hfull
    have hnimm : ¬ ∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b) := by
      intro hcon
      obtain ⟨c₁, hc₁, hwin⟩ := hcon
      exact hnw ⟨0, hguard, c₁, hc₁, hwin⟩
    by_cases hgood : ∃ c : Column, Legal b c ∧ ¬ HasForcedWin (play b c (toMove b))
    · obtain ⟨cg, hcg, hngw⟩ := hgood
      have hvchild : Valid (play b cg (toMove b)) := play_valid b cg (toMove b) hv hcg
      have hcg0 : ¬ HasFour (play b cg (toMove b))
          (opponent (toMove (play b cg (toMove b)))) := by
        rw [toMove_play, opponent_involutive]
        exact fun hf => hnimm ⟨cg, hcg, hf⟩
      have hnoImm : ∀ d : Column, Legal (play b cg (toMove b)) d →
          ¬ HasFour (play (play b cg (toMove b)) d (toMove (play b cg (toMove b))))
                    (toMove (play b cg (toMove b))) := by
        intro d hd hf
        exact hngw ⟨0, hcg0, d, hd, hf⟩
      have hgg : ∀ d : Column, Legal (play b cg (toMove b)) d →
          ¬ HasFour (play (play b cg (toMove b)) d (toMove (play b cg (toMove b))))
              (opponent (toMove (play (play b cg (toMove b)) d
                (toMove (play b cg (toMove b)))))) := by
        intro d hd
        have heq : opponent (toMove (play (play b cg (toMove b)) d
            (toMove (play b cg (toMove b)))))
            = toMove (play b cg (toMove b)) := by
          simp only [toMove_play, opponent_involutive]
        rw [heq]
        exact hnoImm d hd
      have hper : ∀ d : Column, Legal (play b cg (toMove b)) d →
          CanForceDraw (play (play b cg (toMove b)) d
            (toMove (play b cg (toMove b)))) := by
        intro d hd
        have hvg : Valid (play (play b cg (toMove b)) d
            (toMove (play b cg (toMove b)))) :=
          play_valid _ d _ hvchild hd
        by_cases hwg : HasForcedWin (play (play b cg (toMove b)) d
            (toMove (play b cg (toMove b))))
        · exact HasForcedWin_imp _ hwg
        · have ht2 := Valid_totalStones _ hvg
          rw [totalStones_play, totalStones_play] at ht2
          have hM2 : M ≥ 2 := by omega
          rcases ih (M - 2) (by omega) _ hvg (hgg d hd)
              (by rw [totalStones_play, totalStones_play]; omega) hwg with hfl | hcd
          · exfalso
            obtain ⟨hex, hall2⟩ := hfl
            obtain ⟨e₀, he₀⟩ := hex
            have hnf : ¬ BoardFull (play (play b cg (toMove b)) d
                (toMove (play b cg (toMove b)))) := by
              intro hfb
              have h1 := hfb e₀
              have h2 : ((play (play b cg (toMove b)) d
                (toMove (play b cg (toMove b)))) e₀).length < Height := he₀
              omega
            have h21 : WinningWithin (play b cg (toMove b)) 21 :=
              ⟨hcg0, Or.inr ⟨d, hd, hnf, fun e he =>
                (HasForcedWin_iff_20 _ (play_valid _ e _
                  (play_valid _ d _ hvchild hd) he)).mp (hall2 e he)⟩⟩
            exact hngw ⟨20, win_beyond20 1 _ hvchild h21⟩
          · exact hcd
      obtain ⟨K, hK⟩ := exists_uniform_depth b cg hper
      right
      refine ⟨K + 1, hguard, Or.inr (Or.inr ⟨cg, hcg, ?_⟩)⟩
      by_cases hfc : BoardFull (play b cg (toMove b))
      · exact Or.inl hfc
      · exact Or.inr hK
    · left
      refine ⟨⟨c₀, hc₀⟩, ?_⟩
      intro c hc
      by_contra hcon
      exact hgood ⟨c, hc, hcon⟩

theorem cover_fuel (N : Nat) :
    ∀ M : Nat, M ≤ N → ∀ b : Board, Valid b →
      ¬ HasFour b (opponent (toMove b)) → totalStones b + M = 42 →
      ¬ HasForcedWin b → ForcedLoss b ∨ CanForceDraw b := by
  induction N with
  | zero =>
      intro M hM
      have h0 : M = 0 := by omega
      subst h0
      exact cover_step 0 (by intro K hK; omega)
  | succ N ihQ =>
      intro M hM
      exact cover_step M (by intro K hK; exact ihQ K (by omega))

/-- 覆盖性定理：有效、守卫成立、非强制胜 ⇒ 强制败或可保平。 -/
theorem cover (b : Board) (hv : Valid b)
    (hguard : ¬ HasFour b (opponent (toMove b))) (hnw : ¬ HasForcedWin b) :
    ForcedLoss b ∨ CanForceDraw b := by
  have ht := Valid_totalStones b hv
  exact cover_fuel (42 - totalStones b) (42 - totalStones b) (Nat.le_refl _) b hv
    hguard (by omega) hnw

/-- ★ Zermelo 决定性（三分解）：有效且守卫成立的局面，三选一且覆盖——
    要么行动方强制胜，要么对手强制胜，要么行动方非胜且可保平。 -/
theorem determinacy (b : Board) (hv : Valid b)
    (hguard : ¬ HasFour b (opponent (toMove b))) :
    HasForcedWin b ∨ ForcedLoss b ∨ (CanForceDraw b ∧ ¬ HasForcedWin b) := by
  by_cases hw : HasForcedWin b
  · exact Or.inl hw
  · rcases cover b hv hguard hw with hfl | hcd
    · exact Or.inr (Or.inl hfl)
    · exact Or.inr (Or.inr ⟨hcd, hw⟩)

/-- 活局面版（Live ⇒ 守卫）。 -/
theorem determinacy_live (b : Board) (hv : Valid b) (hl : Live b) :
    HasForcedWin b ∨ ForcedLoss b ∨ (CanForceDraw b ∧ ¬ HasForcedWin b) :=
  determinacy b hv (live_no_four b hl (opponent (toMove b)))

-- ── E3：L/D 排他（对偶碰撞引理） ──────────────────────────────────────

/-- 满盘没有合法着法。 -/
theorem full_not_legal (b : Board) (c : Column) (h : BoardFull b) : ¬ Legal b c := by
  intro hl
  have h1 := h c
  have h2 : (b c).length < Height := hl
  omega

/-- 「不输」的入口守卫：任何深度下都要求对手尚未连四。 -/
theorem avoid_guard (b : Board) (k : Nat) (h : AvoidLossWithin b k) :
    ¬ HasFour b (opponent (toMove b)) := by
  cases k <;> exact h.1

/-- 「必胜」的入口守卫同理。 -/
theorem win_guard (b : Board) (k : Nat) (h : WinningWithin b k) :
    ¬ HasFour b (opponent (toMove b)) := by
  cases k <;> exact h.1

/-- 必胜方案至少需要一手合法着法，故满盘局面无人能必胜。 -/
theorem win_needs_legal (b : Board) (k : Nat) (h : WinningWithin b k) :
    ¬ BoardFull b := by
  intro hfull
  cases k with
  | zero =>
      obtain ⟨_, c₀, hc₀, _⟩ := h
      exact full_not_legal b c₀ hfull hc₀
  | succ k =>
      obtain ⟨_, h2⟩ := h
      rcases h2 with ⟨c₀, hc₀, _⟩ | ⟨c₀, hc₀, _, _⟩
      · exact full_not_legal b c₀ hfull hc₀
      · exact full_not_legal b c₀ hfull hc₀

/-- 对偶碰撞（配对引理）：若我的每个应手 d 之后都能 k 轮保平，
    则对手在此局面不可能有任何深度的必胜——追杀令撞上免死金牌。
    对 k 归纳：双方各摆长线时一轮剥掉两层，立即制胜全部撞守卫。 -/
theorem not_win_of_all_reply_draw (K : Nat) :
    ∀ (m : Nat) (y : Board),
      (∀ d : Column, Legal y d →
        AvoidLossWithin (play y d (toMove y)) K) →
      ¬ WinningWithin y m := by
  induction K with
  | zero =>
      intro m y hall hW
      cases m with
      | zero =>
          obtain ⟨_, d₀, hd₀, hwin⟩ := hW
          have hg := avoid_guard _ _ (hall d₀ hd₀)
          simp only [toMove_play, opponent_involutive] at hg
          exact hg hwin
      | succ m =>
          obtain ⟨_, h2⟩ := hW
          rcases h2 with ⟨d₀, hd₀, hwin⟩ | ⟨d₁, hd₁, hnf, hall2⟩
          · have hg := avoid_guard _ _ (hall d₀ hd₀)
            simp only [toMove_play, opponent_involutive] at hg
            exact hg hwin
          · obtain ⟨_, h3⟩ := hall d₁ hd₁
            rcases h3 with ⟨e₀, he₀, hwin⟩ | hfull
            · have hg := win_guard _ _ (hall2 e₀ he₀)
              simp only [toMove_play, opponent_involutive] at hg hwin
              exact hg hwin
            · exact hnf hfull
  | succ K ih =>
      intro m y hall hW
      cases m with
      | zero =>
          obtain ⟨_, d₀, hd₀, hwin⟩ := hW
          have hg := avoid_guard _ _ (hall d₀ hd₀)
          simp only [toMove_play, opponent_involutive] at hg
          exact hg hwin
      | succ m =>
          obtain ⟨_, h2⟩ := hW
          rcases h2 with ⟨d₀, hd₀, hwin⟩ | ⟨d₁, hd₁, hnf, hall2⟩
          · have hg := avoid_guard _ _ (hall d₀ hd₀)
            simp only [toMove_play, opponent_involutive] at hg
            exact hg hwin
          · obtain ⟨_, h3⟩ := hall d₁ hd₁
            rcases h3 with ⟨e₀, he₀, hwin⟩ | hfull | ⟨e₁, he₁, hall3⟩
            · have hg := win_guard _ _ (hall2 e₀ he₀)
              simp only [toMove_play, opponent_involutive] at hg hwin
              exact hg hwin
            · exact hnf hfull
            · rcases hall3 with hfe | hall4
              · exact win_needs_legal _ _ (hall2 e₁ he₁) hfe
              · exact ih m _ hall4 (hall2 e₁ he₁)

/-- ★ L/D 排他：强制败者无法保平。 -/
theorem ForcedLoss_not_forcedDraw (b : Board) (hfl : ForcedLoss b) :
    ¬ CanForceDraw b := by
  intro ⟨K, hK⟩
  induction K with
  | zero =>
      obtain ⟨_, h2⟩ := hK
      rcases h2 with ⟨c, hc, hwin⟩ | hfull
      · exact winning_move_blocks_opponent b c hwin (hfl.2 c hc)
      · obtain ⟨c₁, hc₁⟩ := hfl.1
        exact full_not_legal b c₁ hfull hc₁
  | succ K ih =>
      obtain ⟨_, h2⟩ := hK
      rcases h2 with ⟨c, hc, hwin⟩ | hfull | ⟨c, hc, hall3⟩
      · exact winning_move_blocks_opponent b c hwin (hfl.2 c hc)
      · obtain ⟨c₁, hc₁⟩ := hfl.1
        exact full_not_legal b c₁ hfull hc₁
      · obtain ⟨m, hm⟩ := hfl.2 c hc
        rcases hall3 with hfe | hall4
        · exact win_needs_legal _ _ hm hfe
        · exact not_win_of_all_reply_draw K m (play b c (toMove b)) hall4 hm

/-- ★ 强三分解：三种结局恰居其一（覆盖 + 两两排他全部到位）。 -/
theorem determinacy_strong (b : Board) (hv : Valid b)
    (hguard : ¬ HasFour b (opponent (toMove b))) :
    HasForcedWin b ∨ ForcedLoss b ∨
      (CanForceDraw b ∧ ¬ HasForcedWin b ∧ ¬ ForcedLoss b) := by
  rcases determinacy b hv hguard with h | h | ⟨hcd, hnw⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hcd, hnw,
      fun hfl => ForcedLoss_not_forcedDraw b hfl hcd⟩)

-- ── 战况：Zermelo 三分解 ★已完工（含强三分解） ───────────────────────
-- determinacy / determinacy_strong：有效守卫局面三选一、恰居其一。
-- 全部积木：胜⇒保平、胜败互斥、L/D 排他、深度坍缩（iff 20）、覆盖性（cover）。

/-- The central column, 0-based index 3 (1-based column 4). -/
def center : Column := ⟨3, by norm_num⟩

/-- The position after the first player drops a stone in the middle column. -/
def afterBlackCenter : Board := play emptyBoard center Player.black

theorem center_valid : Valid afterBlackCenter := by
  apply play_valid emptyBoard center Player.black emptyBoard_valid
  simp [center, emptyBoard]

theorem center_height : height afterBlackCenter center = 1 := by
  simp [afterBlackCenter, height, play, emptyBoard, center]

theorem center_toMove : toMove afterBlackCenter = Player.white := by
  decide



theorem emptyBoard_totalStones : totalStones emptyBoard = 0 := by
  decide

theorem emptyBoard_toMove : toMove emptyBoard = Player.black := by
  decide

theorem center_not_full : ¬ Full afterBlackCenter center := by
  simp [Full, afterBlackCenter, play, emptyBoard, center]

-- ── E1：条件偷策略（影子对局的条件化） ────────────────────────────────

/-- 垫步前提（S）：白方行动且必胜的局面，黑方任意垫一子后，
    新行动方（黑）仍然必胜——"额外一手棋不亏于无"的抢步压缩。
    `Connect4Proof.StrategyLimits` 中的 `not_stealDump` 已证明此全局前提不成立；
    保留用于记录条件论证。 -/
def StealDump : Prop :=
  ∀ (b : Board) (d : Column), Valid b → Legal b d → toMove b = Player.white →
    HasForcedWin b → HasForcedWin (play b d Player.black)

/-- 换色前提（C）：黑方在 d 落子后必胜 ⇒ 同格落白子后黑方仍必胜。
    这是重力下影子对局颜色错位的修补条款。
    `Connect4Proof.StrategyLimits` 中的 `not_stealSwap` 已证明此全局前提不成立。 -/
def StealSwap : Prop :=
  ∀ (x : Board) (d : Column), Valid x → Legal x d →
    HasForcedWin (play x d Player.black) → HasForcedWin (play x d Player.white)

/-- ★ 条件偷策略：S + C ⇒ 空盘不是先手的强制败。
    构造：黑走中列后，对白方每个应手 d，用 S（垫步吃一手）+ C（换色）把
    "白方必胜"换写成"黑方必胜"，拼出黑方 21 轮必胜，与强制败互斥。 -/
theorem stealing_conditional (hS : StealDump) (hC : StealSwap) :
    ¬ ForcedLoss emptyBoard := by
  intro hfl
  have hc : Legal emptyBoard center := by simp [Legal, center, emptyBoard]
  have hvA : Valid (play emptyBoard center Player.black) :=
    play_valid emptyBoard center Player.black emptyBoard_valid hc
  have hwhite : toMove (play emptyBoard center Player.black) = Player.white := by
    rw [toMove_play, emptyBoard_toMove]
    rfl
  have hWw := hfl.2 center hc
  refine HasForcedWin_not_forcedLoss emptyBoard
    ⟨21, ⟨emptyBoard_not_has_four _, Or.inr ⟨center, hc, ?_, ?_⟩⟩⟩ hfl
  · intro hf
    have h1 : ((play emptyBoard center Player.black) center).length = Height :=
      hf center
    have h2 : ((play emptyBoard center Player.black) center).length = 1 := by
      simp [play, Function.update, center, emptyBoard]
    have h3 : (Height : Nat) = 6 := rfl
    omega
  · intro d hd
    have h1 : HasForcedWin (play (play emptyBoard center Player.black) d
        Player.black) := hS _ d hvA hd hwhite hWw
    have h2 := hC _ d hvA hd h1
    exact (HasForcedWin_iff_20 _ (play_valid _ d _ hvA hd)).mp h2

/-- 推论（经典偷策略的结论形态）：S + C ⇒ 先手在空盘上胜或平。 -/
theorem first_player_not_lost (hS : StealDump) (hC : StealSwap) :
    HasForcedWin emptyBoard ∨ CanForceDraw emptyBoard := by
  rcases determinacy emptyBoard emptyBoard_valid
    (emptyBoard_not_has_four (opponent (toMove emptyBoard))) with h | h | ⟨hcd, _⟩
  · exact Or.inl h
  · exact absurd h (stealing_conditional hS hC)
  · exact Or.inr hcd

-- ── E2：反射桥——Bool 化的快速四连检查（③ 证书验证的缩微预演） ────────

/-- 单方向四连的 Bool 镜像。 -/
def hasFourDirBool (b : Board) (p : Player) (c r dr dc : Int) : Bool :=
  (List.range 4).all
    (fun i => cellAtInt b (c + (i : Int) * dr) (r + (i : Int) * dc) == some p)

/-- 全盘四连的 Bool 镜像：4 方向 × 7×6 起点，内核可直接求值。 -/
def hasFourBool (b : Board) (p : Player) : Bool :=
  (List.range 7).any (fun ci =>
    (List.range 6).any (fun ri =>
      hasFourDirBool b p ci ri 0 1 || hasFourDirBool b p ci ri 1 0 ||
      hasFourDirBool b p ci ri 1 1 || hasFourDirBool b p ci ri 1 (-1)))

theorem hasFourDirBool_iff (b : Board) (p : Player) (c r dr dc : Int) :
    hasFourDirBool b p c r dr dc = true ↔ HasFourDir b p c r dr dc := by
  constructor
  · intro h i
    have h1 := List.all_eq_true.mp h i (by simp [List.mem_range])
    simp at h1
    exact h1
  · intro h
    refine List.all_eq_true.mpr fun i hi => ?_
    simp
    exact h ⟨i, List.mem_range.mp hi⟩

/-- 取值非空的格子必然界内。 -/
theorem cellAtInt_some_inbounds (b : Board) (x y : Int) (p : Player)
    (h : cellAtInt b x y = some p) :
    (0 ≤ x ∧ x < (Width : Int)) ∧ (0 ≤ y ∧ y < (Height : Int)) := by
  unfold cellAtInt at h
  split at h
  · next hc =>
      split at h
      · next hr => exact ⟨hc, hr⟩
      · simp at h
  · simp at h

/-- 任何方向的四连见证都可搬到 Nat 坐标版本（第 0 格界内 ⇒ 见证起点界内）。 -/
theorem hasFourDir_toNat (b : Board) (p : Player) (c r dr dc : Int)
    (h : HasFourDir b p c r dr dc)
    (hcb : 0 ≤ c ∧ c < (Width : Int)) (hrb : 0 ≤ r ∧ r < (Height : Int)) :
    HasFourDir b p (c.toNat : Int) (r.toNat : Int) dr dc := by
  have hc' : (c.toNat : Int) = c := Int.toNat_of_nonneg hcb.1
  have hr' : (r.toNat : Int) = r := Int.toNat_of_nonneg hrb.1
  intro i
  rw [hc', hr']
  exact h i

theorem hasFourBool_iff (b : Board) (p : Player) :
    hasFourBool b p = true ↔ HasFour b p := by
  constructor
  · intro h
    simp only [hasFourBool, List.any_eq_true] at h
    obtain ⟨ci, -, ri, -, h3⟩ := h
    rcases Bool.or_eq_true_iff.mp h3 with h3 | h
    · rcases Bool.or_eq_true_iff.mp h3 with h3 | h
      · rcases Bool.or_eq_true_iff.mp h3 with h | h
        · exact Or.inl ⟨ci, ri, (hasFourDirBool_iff _ _ _ _ _ _).mp h⟩
        · exact Or.inr (Or.inl ⟨ci, ri, (hasFourDirBool_iff _ _ _ _ _ _).mp h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ci, ri, (hasFourDirBool_iff _ _ _ _ _ _).mp h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ci, ri, (hasFourDirBool_iff _ _ _ _ _ _).mp h⟩))
  · rintro (⟨c, r, hd⟩ | ⟨c, r, hd⟩ | ⟨c, r, hd⟩ | ⟨c, r, hd⟩)
    all_goals
      have h0 : cellAtInt b c r = some p := by
        have h1 := hd ⟨0, by omega⟩
        simpa using h1
      have hb := cellAtInt_some_inbounds b c r p h0
      have hW : (Width : Int) = 7 := rfl
      have hH : (Height : Int) = 6 := rfl
      have hc' : (c.toNat : Int) = c := Int.toNat_of_nonneg hb.1.1
      have hr' : (r.toNat : Int) = r := Int.toNat_of_nonneg hb.2.1
      have hd' := hasFourDir_toNat b p c r _ _ hd hb.1 hb.2
      refine List.any_eq_true.mpr ⟨c.toNat, List.mem_range.mpr (by omega), ?_⟩
      refine List.any_eq_true.mpr ⟨r.toNat, List.mem_range.mpr (by omega), ?_⟩
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl
        (Bool.or_eq_true_iff.mpr (Or.inl ((hasFourDirBool_iff _ _ _ _ _ _).mpr hd'))))))
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl
        (Bool.or_eq_true_iff.mpr (Or.inr ((hasFourDirBool_iff _ _ _ _ _ _).mpr hd'))))))
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr
        ((hasFourDirBool_iff _ _ _ _ _ _).mpr hd'))))
    · exact Bool.or_eq_true_iff.mpr (Or.inr ((hasFourDirBool_iff _ _ _ _ _ _).mpr hd'))

/-- 中列连下四手黑子。 -/
def centerFour : Board :=
  play (play (play (play emptyBoard center Player.black)
    center Player.black) center Player.black) center Player.black

/-- 反射演示：机器算 `decide`，桥定理把它升级为证明——③ 号里程碑
    （证书验证）的标准工作模式，在这里以最小形态跑通一遍。 -/
theorem centerFour_has_four : HasFour centerFour Player.black := by
  have h : hasFourBool centerFour Player.black = true := by decide
  exact (hasFourBool_iff centerFour Player.black).mp h

-- ── 攻城：把偷策略前提压缩为 Bool 方程 ───────────────────────────────

/-- 安全转换：自然数 → 列号（界外取模回卷，枚举时无害）。 -/
def colOf (i : Nat) : Column := ⟨i % 7, Nat.mod_lt i (by norm_num)⟩

theorem colOf_val (c : Column) : colOf c.val = c :=
  Fin.ext (Nat.mod_eq_of_lt c.2)

/-- 各部件的 Bool 镜像，与 Prop 版逐条对应，桥证明因此结构化。 -/
def guardB (b : Board) : Bool := !hasFourBool b (opponent (toMove b))

def legalB (b : Board) (c : Column) : Bool := decide ((b c).length < Height)

def immWinB (b : Board) : Bool :=
  (List.range 7).any (fun i =>
    legalB b (colOf i) && hasFourBool (play b (colOf i) (toMove b)) (toMove b))

def fullB (b : Board) : Bool :=
  (List.range 7).all (fun i => decide ((b (colOf i)).length = Height))

/-- `WinningWithin` 的 Bool 镜像（深度参数版）。 -/
def winB : Board → Nat → Bool
  | b, 0 => guardB b && immWinB b
  | b, k + 1 =>
      guardB b && (immWinB b ||
        (List.range 7).any (fun i =>
          legalB b (colOf i) && !fullB (play b (colOf i) (toMove b)) &&
            (List.range 7).all (fun j =>
              !legalB (play b (colOf i) (toMove b)) (colOf j) ||
                winB (play (play b (colOf i) (toMove b)) (colOf j)
                  (toMove (play b (colOf i) (toMove b)))) k)))

theorem legalB_iff (b : Board) (c : Column) : legalB b c = true ↔ Legal b c := by
  simp [legalB, Legal]

theorem guardB_iff (b : Board) :
    guardB b = true ↔ ¬ HasFour b (opponent (toMove b)) := by
  simp only [guardB, Bool.not_eq_true', Bool.eq_false_iff, ← hasFourBool_iff]

theorem fullB_iff (b : Board) : fullB b = true ↔ BoardFull b := by
  constructor
  · intro h c
    have hall := List.all_eq_true.mp h c.val (List.mem_range.mpr c.2)
    have h1 := of_decide_eq_true hall
    rwa [colOf_val] at h1
  · intro h
    refine List.all_eq_true.mpr fun i _ => decide_eq_true (h (colOf i))

theorem immWinB_iff (b : Board) :
    immWinB b = true ↔ ∃ c : Column, Legal b c ∧ IsWinningMove b c (toMove b) := by
  constructor
  · intro h
    obtain ⟨i, -, hc⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, legalB_iff, hasFourBool_iff] at hc
    exact ⟨colOf i, hc.1, hc.2⟩
  · intro h
    obtain ⟨c, hcl, hwin⟩ := h
    refine List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr c.2, ?_⟩
    rw [colOf_val]
    simp only [Bool.and_eq_true, legalB_iff, hasFourBool_iff]
    exact ⟨hcl, hwin⟩

theorem notFullB_eq (b : Board) (h : ¬ BoardFull b) : (!fullB b) = true := by
  cases hb : fullB b with
  | true => exact absurd (fullB_iff _ |>.mp hb) h
  | false => rfl

/-- ★ 深度镜像桥：`winB` 与 `WinningWithin` 在每个深度上等价。 -/
theorem winB_iff (b : Board) (k : Nat) : winB b k = true ↔ WinningWithin b k := by
  induction k generalizing b with
  | zero =>
      simp only [winB, WinningWithin, Bool.and_eq_true, guardB_iff, immWinB_iff]
  | succ k ih =>
      constructor
      · intro h
        simp only [winB, Bool.and_eq_true] at h
        obtain ⟨hg, h2⟩ := h
        refine ⟨guardB_iff _ |>.mp hg, ?_⟩
        rcases Bool.or_eq_true_iff.mp h2 with himm | hset
        · exact Or.inl (immWinB_iff _ |>.mp himm)
        · obtain ⟨i, -, hset⟩ := List.any_eq_true.mp hset
          simp only [Bool.and_eq_true, legalB_iff] at hset
          have hc : Legal b (colOf i) := hset.1.1
          have hnf : (!fullB (play b (colOf i) (toMove b))) = true := hset.1.2
          have hall := hset.2
          have hnf' : ¬ BoardFull (play b (colOf i) (toMove b)) := by
            rw [Bool.not_eq_true', Bool.eq_false_iff] at hnf
            exact fun hcon => hnf (fullB_iff _ |>.mpr hcon)
          refine Or.inr ⟨colOf i, hc, hnf', fun d hd => ?_⟩
          have hd2 := List.all_eq_true.mp hall d.val (List.mem_range.mpr d.2)
          rw [colOf_val] at hd2
          rcases Bool.or_eq_true_iff.mp hd2 with hneg | hw
          · exfalso
            rw [Bool.not_eq_true', Bool.eq_false_iff] at hneg
            exact hneg (legalB_iff _ _ |>.mpr hd)
          · exact (ih _) |>.mp hw
      · intro h
        obtain ⟨hg, h2⟩ := h
        rw [winB, Bool.and_eq_true, Bool.or_eq_true_iff]
        refine ⟨guardB_iff _ |>.mpr hg, ?_⟩
        rcases h2 with ⟨c, hc, hwin⟩ | ⟨c, hc, hnf, hall⟩
        · exact Or.inl (immWinB_iff _ |>.mpr ⟨c, hc, hwin⟩)
        · refine Or.inr (List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr c.2, ?_⟩)
          rw [colOf_val, Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨⟨legalB_iff _ _ |>.mpr hc, notFullB_eq _ hnf⟩, ?_⟩
          rw [List.all_eq_true]
          intro j _
          rw [Bool.or_eq_true_iff]
          by_cases hld : Legal (play b c (toMove b)) (colOf j)
          · exact Or.inr ((ih _) |>.mpr (hall (colOf j) hld))
          · exact Or.inl (by
              have hlb : legalB (play b c (toMove b)) (colOf j) = false :=
                Bool.eq_false_iff.mpr fun hcon => hld (legalB_iff _ _ |>.mp hcon)
              rw [hlb]; rfl)

/-- 总桥：有效棋盘上，「存在强制胜」⇔ 一个 Bool 方程。 -/
theorem HasForcedWin_iff_winB (b : Board) (hv : Valid b) :
    HasForcedWin b ↔ winB b 20 = true :=
  (HasForcedWin_iff_20 b hv).trans (winB_iff b 20).symm

/-- ★★ 前提收紧版偷策略：S 与 C 只需在「黑走中列后的位置」这一族上成立，
      且整体写成 Bool 方程。剩余债务 = 求解器算出这些 Bool 值：
      - S 的足迹：winB A₁ 20 = true ⇒ ∀d 合法，winB (A₁+黑@d) 20 = true；
      - C 的足迹：∀d 合法，winB (A₁+黑@d) = true ⇒ winB (A₁+白@d) = true。 -/
theorem stealing_at_center
    (hS : winB afterBlackCenter 20 = true →
      ∀ d : Column, Legal afterBlackCenter d →
        winB (play afterBlackCenter d Player.black) 20 = true)
    (hC : ∀ d : Column, Legal afterBlackCenter d →
      winB (play afterBlackCenter d Player.black) 20 = true →
        winB (play afterBlackCenter d Player.white) 20 = true) :
    ¬ ForcedLoss emptyBoard := by
  intro hfl
  have hc : Legal emptyBoard center := by simp [Legal, center, emptyBoard]
  have hvA : Valid (play emptyBoard center Player.black) :=
    play_valid emptyBoard center Player.black emptyBoard_valid hc
  have hWw : HasForcedWin afterBlackCenter := hfl.2 center hc
  have hw1 : winB afterBlackCenter 20 = true :=
    (HasForcedWin_iff_winB _ hvA).mp hWw
  refine HasForcedWin_not_forcedLoss emptyBoard
    ⟨21, ⟨emptyBoard_not_has_four _, Or.inr ⟨center, hc, ?_, ?_⟩⟩⟩ hfl
  · intro hf
    have h1 : ((play emptyBoard center Player.black) center).length = Height :=
      hf center
    have h2 : ((play emptyBoard center Player.black) center).length = 1 := by
      simp [play, Function.update, center, emptyBoard]
    have h3 : (Height : Nat) = 6 := rfl
    omega
  · intro d hd
    have h1 : winB (play afterBlackCenter d Player.black) 20 = true :=
      hS hw1 d hd
    have h2 : winB (play afterBlackCenter d Player.white) 20 = true :=
      hC d hd h1
    exact (HasForcedWin_iff_20 _
      (play_valid _ d _ hvA hd)).mp ((HasForcedWin_iff_winB _ (play_valid _ d _
        hvA hd)).mpr h2)


end Connect4
