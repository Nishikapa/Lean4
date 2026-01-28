--------------------------------------------------------------------------------
-- Basic_701.lean
-- 演習問題 701〜750（row/col-sum / transpose・scale・Hadamard の拡張代数 /
--                   WSpec の計算規則 / graph と keys の重みレベル）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 651〜700 は Basic_651 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_651

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（row/col-sum）
--------------------------------------------------------------------------------

-- 行方向の有限和：列候補 keys 上で R a b を足す
-- aで指定された行について、keys に含まれる列の成分を全部足す
def wRowSum (keys : List β) (R : WRel α β) (a : α) : Nat :=
  wsum keys (fun b => R a b)

-- 列方向の有限和：行候補 keys 上で R a b を足す
-- bで指定された列について、keys に含まれる行の成分を全部足す
def wColSum (keys : List α) (R : WRel α β) (b : β) : Nat :=
  wsum keys (fun a => R a b)

--------------------------------------------------------------------------------
-- 701〜710：wRowSum / wColSum の基本
--------------------------------------------------------------------------------

-- 701：空 keys の rowSum は 0
theorem ex701 (R : WRel α β) (a : α) :
    wRowSum ([] : List β) R a = 0 := by
  -- 列番号を一つも渡さなかったら、その合計は 0 である。
  dsimp [wRowSum, wsum]

-- 702：cons 展開（rowSum）
theorem ex702 (b : β) (keys : List β) (R : WRel α β) (a : α) :
    wRowSum (b :: keys) R a = R a b + wRowSum keys R a := by
  -- 列番号にbを追加したら、その合計には R a b が加わる。
  dsimp [wRowSum, wsum]

-- 703：rowSum の ext（keys 上で点ごと一致なら rowSum も一致）
theorem ex703 (keys : List β) (R S : WRel α β) (a : α) :
    (∀ b, b ∈ keys → R a b = S a b) →
      wRowSum keys R a = wRowSum keys S a := by
  -- 行列Rと行列Sのa行について、keysで指定された列の成分がすべて等しいなら、
  -- その合計は等しくなる。
  dsimp [wRowSum, wsum]
  intro hEq
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum]

    have h2 : (wsum bs fun b => R a b) = wsum bs fun b => S a b := by
      apply ih
      intro b1 hContins
      apply hEq
      apply List.mem_cons_of_mem
      exact hContins
    rw [h2]
    rw [Nat.add_right_cancel_iff]
    apply hEq
    apply List.mem_cons_self

-- 704：rowSum は wAdd に関して線形（点ごと）
theorem ex704 (keys : List β) (R S : WRel α β) (a : α) :
    wRowSum keys (wAdd R S) a = wRowSum keys R a + wRowSum keys S a := by
  -- 行列Rと行列Sの和の行列に対し、そのa行のkeysで指定された列の成分を足すことと、
  -- 各行列にて合計を取ったものの和は等しい。
  dsimp [wRowSum, wsum, wAdd]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wAdd]
    rw [ih]
    rw [←Nat.add_assoc]
    rw [Nat.add_assoc (R a b) (S a b) (wsum bs fun b => R a b)]
    rw [Nat.add_comm (S a b) (wsum bs fun b => R a b)]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc]

-- 705：rowSum とスカラー倍（wScale）
theorem ex705 (keys : List β) (t : Nat) (R : WRel α β) (a : α) :
    wRowSum keys (wScale t R) a = t * wRowSum keys R a := by
  -- 行列内のすべての要素をある値でスカラー倍したものでwRowSumしたものと
  -- 元の行列のwRowSumをスカラー倍したものは等しくなる。
  dsimp [wRowSum, wsum, wScale]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]

-- 706：空 keys の colSum は 0
theorem ex706 (R : WRel α β) (b : β) :
    wColSum ([] : List α) R b = 0 := by
  -- 行番号を一つも渡さなかったら、その合計は 0 である。
  dsimp [wColSum]
  dsimp [wsum]

-- 707：cons 展開（colSum）
theorem ex707 (a : α) (keys : List α) (R : WRel α β) (b : β) :
    wColSum (a :: keys) R b = R a b + wColSum keys R b := by
  -- 行番号にaを追加したら、その合計には R a b が加わる。
  dsimp [wColSum]
  dsimp [wsum]

-- 708：transpose は row/col を入れ替える（rowSum）
theorem ex708 (keys : List α) (R : WRel α β) (b : β) :
    wRowSum keys (wTrans R) b = wColSum keys R b := by
  -- wComSumの結果と、転地した行列のwRowSumの結果は等しい。
  dsimp [wRowSum]
  dsimp [wColSum]
  dsimp [wTrans]

-- 709：transpose は row/col を入れ替える（colSum）
theorem ex709 (keys : List β) (R : WRel α β) (a : α) :
    wColSum keys (wTrans R) a = wRowSum keys R a := by
  -- wRowSumの結果と、転地した行列のwColSumの結果は等しい。
  dsimp [wColSum]
  dsimp [wRowSum]
  dsimp [wTrans]

-- 710：rowSum > 0 ↔ ∃ b∈keys, R a b > 0
theorem ex710 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a > 0 ↔ ∃ b, b ∈ keys ∧ R a b > 0 := by
  -- wRowSumの結果が０より大きいのと
  -- keysで指定された列の中に０より大きい成分が存在するのは同値である。
  dsimp [wRowSum]
  obtain hEx606 :=
    ex606 keys (fun b => R a b)
  rw [hEx606]

--------------------------------------------------------------------------------
-- 711〜720：row/col の “0⇔全0” と maskW
--------------------------------------------------------------------------------

-- 711：rowSum = 0 ↔ ∀ b∈keys, R a b = 0
theorem ex711 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a = 0 ↔ (∀ b, b ∈ keys → R a b = 0) := by
  -- wRowSumの結果が0であるのと
  -- keysで指定された列の成分がすべて0であるのは同値である。
  dsimp [wRowSum]
  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0)
  obtain hEx607 :=
    ex607 keys (R a)
  rw [hEx607]

-- 712：colSum > 0 ↔ ∃ a∈keys, R a b > 0
theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0 := by
  -- wColSumの結果が０より大きいのと
  -- keysで指定された行の中に０より大きい成分が存在するのは同値である。
  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --   (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  dsimp [wColSum]
  obtain hEx606 :=
    ex606 keys (fun a => R a b)
  rw [hEx606]

-- 713：colSum = 0 ↔ ∀ a∈keys, R a b = 0
theorem ex713 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys R b = 0 ↔ (∀ a, a ∈ keys → R a b = 0) := by
  -- wColSumの結果が0であるのと
  -- keysで指定された行の成分がすべて0であるのは同値である。
  dsimp [wColSum]
  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
  obtain hEx607 :=
    ex607 keys (fun a => R a b)
  rw [hEx607]

-- 714：singleton rowSum（正）↔ 成分（正）
theorem ex714_pre (a : α) (b : β) (R : WRel α β) :
    wRowSum [b] R a =  R a b := by
  -- keysに一つだけ列番号を与えたときのwRowSumの値は
  -- その成分自体に等しい。
  dsimp [wRowSum]
  dsimp [wsum]

theorem ex714 (a : α) (b : β) (R : WRel α β) :
    wRowSum [b] R a > 0 ↔ R a b > 0 := by
  -- keysに一つだけ列番号を与えたときのwRowSumが０より大きいのと
  -- その成分自体が０より大きいのは同値である。
  rw [ex714_pre]

-- 715：b∈keys かつ R a b>0 なら rowSum>0
theorem ex715 (keys : List β) (R : WRel α β) (a : α) (b : β) :
    b ∈ keys → R a b > 0 → wRowSum keys R a > 0 := by
  dsimp [wRowSum]
  intro hIn hRab
  obtain hEx606 :=
    ex606 keys (fun b => R a b)
  rw [hEx606]
  exists b

-- 716：append 分解（rowSum）
theorem ex716 (keys more : List β) (R : WRel α β) (a : α) :
    wRowSum (keys ++ more) R a = wRowSum keys R a + wRowSum more R a := by
  -- 列番号のリストが二つあった場合、
  -- その二つのリストを結合したリストでのwRowSumの値と
  -- それぞれのリストでのwRowSumの和は等しい。
  dsimp [wRowSum]
  -- theorem ex536 {X : Type} (xs ys : List X) (f : X → Nat) :
  --     wsum (xs ++ ys) f = wsum xs f + wsum ys f := by
  obtain hEx536 :=
    ex536 keys more (R a)
  rw [hEx536]

-- 717：append 分解（colSum）
theorem ex717 (keys more : List α) (R : WRel α β) (b : β) :
    wColSum (keys ++ more) R b = wColSum keys R b + wColSum more R b := by
  -- 行番号のリストが二つあった場合、
  -- その二つのリストを結合したリストでのwColSumの値と
  -- それぞれのリストでのwColSumの和は等しい。
  dsimp [wColSum]
  obtain hEx536 :=
    ex536 keys more (fun a => R a b)
  rw [hEx536]

-- 718：rowSum>0 は append で保たれる
theorem ex718 (keys more : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a > 0 → wRowSum (keys ++ more) R a > 0 := by
  -- ある列番号リストでwRowSumが０より大きいなら、
  -- そのリストに別の列番号リストを追加してもwRowSumは０より大きい。

  -- TODO（ヒント：ex716 と Nat.add_pos_left / Nat.add_pos_right）

  -- theorem ex716 (keys more : List β) (R : WRel α β) (a : α) :
  --     wRowSum (keys ++ more) R a = wRowSum keys R a + wRowSum more R a
  rw [ex716 keys more R a]
  dsimp [wRowSum]
  intro h1
  apply Nat.add_pos_left
  exact h1

-- 719：wZero の rowSum は常に 0
theorem ex719 (keys : List β) (a : α) :
    wRowSum keys (wZero α β) a = 0 := by
  -- ０行列に対しては、どんな行について、どんな列番号リストでwRowSumを取っても
  -- その結果は０になる。

  dsimp [wRowSum]
  dsimp [wZero]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

-- 720：maskW の rowSum>0 ↔ ∃ b∈keys, M a b
theorem ex720 (keys : List β) (M : Rel α β) (a : α) :
    wRowSum keys (maskW M) a > 0 ↔ ∃ b, b ∈ keys ∧ M a b := by
  -- 命題の配列を1と0の値へ変換した行列のwRowSumが０より大きいのと
  -- その元の命題の行列について、真となる成分が存在するのは同値である。

  dsimp [wRowSum, maskW]
  constructor
  intro hwRowSum1
  induction keys with
  | nil =>
    dsimp [wsum] at hwRowSum1
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum] at hwRowSum1
    --obtain hwRowSum2 : 0 < ((if M a b1 then 1 else 0) + wsum bs fun b => if M a b then 1 else 0) := hwRowSum1

    rw [gt_iff_lt] at hwRowSum1
    rw [Nat.add_pos_iff_pos_or_pos] at hwRowSum1
    cases hwRowSum1 with
    | inl hMab1 =>
      by_cases hM : M a b1
      rw [if_pos hM] at hMab1
      exists b1
      constructor
      apply List.mem_cons_self
      exact hM
      rw [if_neg hM] at hMab1
      contradiction
    | inr hWsumBs =>
      obtain h2 := ih hWsumBs
      obtain ⟨b2, hContains, hMab2⟩ := h2
      exists b2
      constructor
      apply List.mem_cons_of_mem
      exact hContains
      exact hMab2

  intro hExists
  obtain ⟨b, hIn, hMab⟩ := hExists
  induction keys with
  | nil =>
    dsimp [wsum]
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum]
    rw [gt_iff_lt]
    rw [Nat.add_pos_iff_pos_or_pos]
    by_cases hEq : b = b1
    rw [←hEq]
    left
    rw [if_pos hMab]
    exact Nat.zero_lt_one
    right
    obtain hInc := List.mem_of_ne_of_mem hEq hIn
    obtain hWsumBs := ih hInc
    exact hWsumBs

--------------------------------------------------------------------------------
-- 721〜730：wCompList / wMask / wGraph（重みレベル）
--------------------------------------------------------------------------------

-- 721：空 keys の wCompList は wZero
theorem ex721 (R : WRel α β) (S : WRel β γ) :
    wCompList ([] : List β) R S = wZero α γ := by
  -- n行m列の行列Rと m行p列の行列Sの縮約を
  -- 列番号リストが空の場合に計算すると、n行p列の０行列になる。

  funext a c
  dsimp [wCompList, wZero, wsum]

-- 722：singleton keys の wCompList（1 項だけ）
theorem ex722 (b : β) (R : WRel α β) (S : WRel β γ) :
    wCompList [b] R S = (fun a c => R a b * S b c) := by
  -- n行m列の行列Rと m行p列の行列Sの縮約を
  -- 列番号リストが一つだけ b の場合に計算すると、
  -- 各成分(a, c)は R a b と S b c の積になる。
  funext a c
  dsimp [wCompList, wsum]

-- 723：右をスカラー倍すると結果もスカラー倍（右線形性）
theorem ex723 (keys : List β) (t : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys R (wScale t S) = wScale t (wCompList keys R S) := by
  -- n行m列の行列Rと m行p列の行列Sのt倍の行列の縮約は、
  -- t倍前の縮約をt倍したものに等しい。

  funext a c
  dsimp [wCompList, wScale, wsum]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]
    rw [←Nat.mul_assoc (R a b) t (S b c)]
    rw [←Nat.mul_comm t (R a b)]
    rw [←Nat.mul_assoc t (R a b) (S b c)]

-- 724：両側をスカラー倍すると係数は積になる
theorem ex724 (keys : List β) (t u : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wScale t R) (wScale u S) = wScale (t * u) (wCompList keys R S) := by
  -- n行m列の行列Rのt倍と m行p列の行列Sのu倍の縮約は、
  -- 縮約をt*u倍したものに等しい。
  funext a c
  dsimp [wCompList, wScale, wsum]
  induction keys with
  | nil =>
    rfl
  | cons b1 bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]
    rw [←Nat.mul_assoc (t * R a b1) u (S b1 c)]
    rw [Nat.mul_assoc t (R a b1) u]
    rw [Nat.mul_comm (R a b1) u]
    rw [←Nat.mul_assoc t u (R a b1)]
    rw [←Nat.mul_assoc (t * u) (R a b1) (S b1 c)]

-- 725：wMask は Hadamard（wMul）で “maskW を掛ける” のと同じ
theorem ex725 (R : WRel α β) (M : Rel α β) :
    wMask R M = wMul R (maskW M) := by
  funext a b
  dsimp [wMask, wMul, maskW]

-- 726：Hadamard と mask の交換（mask を外へ寄せる）
theorem ex726 (R S : WRel α β) (M : Rel α β) :
    wMul (wMask R M) S = wMask (wMul R S) M := by
  -- 右側の行列でマスクするのと左側の行列でマスクするのは結果は同じ
  funext a b
  dsimp [wMask, wMul, maskW]
  by_cases hMab : M a b
  rw [if_pos hMab]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  rw [if_neg hMab]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [Nat.zero_mul]

-- 727：keys.Nodup のとき、graph を左に置いた縮約は “行選択＋mask” になる（重み）
theorem ex727 (keys : List β) (f : α → β) (S : WRel β γ) :
    keys.Nodup →
      wCompList keys (wGraph f) S
        =
      wMask (fun a c => S (f a) c) (fun a _ => f a ∈ keys) := by

  intro hNodup
  funext a c
  dsimp [wCompList, wGraph, wMask, maskW, wsum, relGraph]
  induction keys with
  | nil =>
    dsimp [wsum]
    obtain h1 :=
      if_neg List.not_mem_nil
    rw [h1]
    rw [Nat.mul_zero]
  | cons b1 bs ih =>
    dsimp [wsum]
    obtain hNodup2 := hNodup.of_cons
    obtain hNodup3 := (List.nodup_cons.mp hNodup).1
    obtain ih2 := ih hNodup2
    by_cases hEq : f a = b1

    -- pos
    rw [if_pos hEq]
    rw [Nat.one_mul]
    rw [hEq]
    rw [if_pos List.mem_cons_self]
    rw [Nat.mul_one]
    rw [hEq] at ih2
    rw [ih2]
    obtain hNodup4 := if_neg hNodup3
    rw [hNodup4]
    rw [Nat.mul_zero]
    rw [Nat.add_zero]

    -- neg
    rw [if_neg hEq]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    rw [ih2]
    obtain hhh_iff : f a ∈ b1 :: bs ↔ f a ∈ bs :=
      ⟨fun h =>
        match List.mem_cons.mp h with
        | .inl eq => (hEq eq).elim  -- 「f a = b1」だったら矛盾なので消去
        | .inr mem => mem,          -- 「f a ∈ bs」だったらそのまま返す
      fun h => List.mem_cons.mpr (.inr h)⟩
    rw [hhh_iff]

-- 728：ex727 の “>0” 版（重みが正になる条件）
theorem ex728 (keys : List β) (f : α → β) (S : WRel β γ) :
    keys.Nodup →
    ∀ a c,
      wCompList keys (wGraph f) S a c > 0
        ↔ (f a ∈ keys ∧ S (f a) c > 0) := by
  intro hNodup a c
  rw [ex727 keys f S hNodup]
  dsimp [wMask, maskW]
  constructor

  -- → 方向
  intro hWCompPos
  rw [gt_iff_lt] at hWCompPos
  rw [gt_iff_lt]
  obtain hWCompPos1 := Nat.pos_of_mul_pos_left hWCompPos
  obtain hWCompPos2 := Nat.pos_of_mul_pos_right hWCompPos
  have hWCompPos3 : f a ∈ keys := by
    by_cases hWCompPos3_1 : f a ∈ keys
    exact hWCompPos3_1
    rw [if_neg hWCompPos3_1] at hWCompPos1
    contradiction
  constructor
  exact hWCompPos3
  exact hWCompPos2

  -- ← 方向
  intro hExists
  obtain ⟨hIn, hSPos⟩ := hExists
  rw [gt_iff_lt]
  rw [gt_iff_lt] at hSPos
  rw [if_pos hIn]
  rw [Nat.mul_one]
  exact hSPos

-- 729：graph-graph の縮約（keys.Nodup のときの “関数合成＋mask”）（重み）
theorem ex729 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
      wCompList keys (wGraph f) (wGraph g)
        =
      wMask (wGraph (fun a => g (f a))) (fun a _ => f a ∈ keys) := by
  intro hNodup
  funext a c
  dsimp [wCompList, wGraph, wMask, maskW, wsum, relGraph]
  induction keys with
  | nil =>
    dsimp [wsum]
    --obtain h1 := if_neg List.mem_nil_iff
    rw [if_neg List.not_mem_nil]
    rw [Nat.mul_zero]
  | cons b1 bs ih =>
    dsimp [wsum]
    obtain hNodup2 := hNodup.of_cons
    obtain ih2 := ih hNodup2
    rw [ih2]
    by_cases hEq : f a = b1
    rw [if_pos hEq]
    rw [Nat.one_mul]
    rw [hEq]
    rw [if_pos List.mem_cons_self]
    rw [Nat.mul_one]
    by_cases hEq2 : g b1 = c
    rw [if_pos hEq2]
    rw [Nat.one_mul]
    obtain hNodup3 := (List.nodup_cons.mp hNodup).1
    rw [if_neg hNodup3]

    -- neg
    rw [if_neg hEq2]
    rw [Nat.zero_mul]

    rw [if_neg hEq]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]

    by_cases hEq3 : g (f a) = c
    rw [if_pos hEq3]
    rw [Nat.one_mul]
    rw [Nat.one_mul]
    by_cases hIn : f a ∈ bs
    rw [if_pos hIn]
    have h2 : (f a ∈ b1 :: bs) := by
      apply List.mem_cons.mpr
      right
      exact hIn
    rw [if_pos h2]
    have h3 : ¬ (f a ∈ b1 :: bs) := by
      intro h3_1
      rw [List.mem_cons] at h3_1
      obtain h3_2 | h3_3 := h3_1
      contradiction
      contradiction
    rw [if_neg h3]
    rw [if_neg hIn]
    rw [if_neg hEq3]
    rw [Nat.zero_mul]
    rw [Nat.zero_mul]

-- 730：keys が “十分大きい（全包含）” なら mask が消えて graph 合成そのもの（重み）
theorem ex730 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
    (∀ b, b ∈ keys) →
      wCompList keys (wGraph f) (wGraph g) = wGraph (fun a => g (f a)) := by
  -- TODO（ヒント：ex729 の RHS で mask 条件が常に True になる）

  intro hNodup hAll

  -- theorem ex729 (keys : List β) (f : α → β) (g : β → γ) :
  --     keys.Nodup →
  --       wCompList keys (wGraph f) (wGraph g)
  --         =
  --       wMask (wGraph (fun a => g (f a))) (fun a _ => f a ∈ keys) := by
  obtain hEx729 :=
    ex729 keys f g hNodup

  rw [hEx729]

  funext a c
  dsimp [wMask, maskW, wGraph, relGraph]

  by_cases hEq : g (f a) = c
  rw [if_pos hEq]
  rw [Nat.one_mul]
  obtain hIn := hAll (f a)
  rw [if_pos hIn]

  rw [if_neg hEq]
  rw [Nat.zero_mul]

--------------------------------------------------------------------------------
-- 731〜740：transpose / scale / Hadamard の拡張代数（未出の相性）
--------------------------------------------------------------------------------

-- 731：wTrans は wScale と可換
theorem ex731 (t : Nat) (R : WRel α β) :
    wTrans (wScale t R) = wScale t (wTrans R) := by
  -- 転置する前にスカラー倍するのと
  -- 転置した後にスカラー倍するのは同じ結果になる。
  funext b a
  dsimp [wTrans, wScale]

-- 732：wTrans は wMul と可換（点ごと）
theorem ex732 (R S : WRel α β) :
    wTrans (wMul R S) = wMul (wTrans R) (wTrans S) := by
  -- 各要素を掛け合わせてから転置するのと
  -- それぞれを転置してから掛け合わせるのは同じ結果になる。
  funext b a
  dsimp [wTrans, wMul]

-- 733：wScale は wAdd に分配
theorem ex733 (t : Nat) (R S : WRel α β) :
    wScale t (wAdd R S) = wAdd (wScale t R) (wScale t S) := by
  -- 行列の各要素を足し合わせてからスカラー倍するのと
  -- それぞれをスカラー倍してから各要素を足し合わせるのは同じ結果になる。
  funext b a
  dsimp [wScale, wAdd]
  rw [Nat.mul_add]

-- 734：wScale の合成（係数が積になる）
theorem ex734 (t u : Nat) (R : WRel α β) :
    wScale t (wScale u R) = wScale (t * u) R := by
  -- ある行列をu倍してからt倍するのと
  -- その行列をt*u倍するのは同じ結果になる。
  funext b a
  dsimp [wScale]
  rw [Nat.mul_assoc]

-- 735：wScale 1 は恒等
theorem ex735 (R : WRel α β) :
    wScale 1 R = R := by
  -- ある行列を1倍するのは、その行列自身に等しい。
  funext b a
  dsimp [wScale]
  rw [Nat.one_mul]

-- 736：wMul は右の wAdd に分配（点ごと）
theorem ex736 (R S T : WRel α β) :
    wMul R (wAdd S T) = wAdd (wMul R S) (wMul R T) := by
  -- 同じ列数・行数の3つの行列があったとき、
  -- 右側の行列で各要素を足し合わせてから左側の行列と掛け合わせるのと
  -- それぞれを左側の行列と掛け合わせてから各要素を足し合わせるのは同じ結果になる。
  -- TODO（ヒント：Nat.mul_add）
  funext a b
  dsimp [wMul, wAdd]
  rw [Nat.mul_add]

-- 737：wScale は wMul から外に出せる（左側係数）
theorem ex737 (t : Nat) (R S : WRel α β) :
    wMul (wScale t R) S = wScale t (wMul R S) := by
  -- 同じ列数・行数の２つの行列があったとき、
  -- 左側の行列をt倍してから右側の行列と掛け合わせるのと
  -- 行列を掛け合わせてからt倍するのは同じ結果になる。
  funext a b
  dsimp [wMul, wScale]
  rw [Nat.mul_assoc]

-- 738：WLe は wScale で保たれる（単調性）
theorem ex738 (t : Nat) (R S : WRel α β) :
    WLe R S → WLe (wScale t R) (wScale t S) := by
  -- 同じ列数・行数の２つの行列(R, S)があったとき、
  -- Rのすべての要素が対応するSの要素以下であったとき、
  -- R及びSをt倍した行列についても同じ関係が成り立つ。
  intro hWLe
  intro a1 b1
  dsimp [wScale]
  dsimp [WLe] at hWLe
  obtain hRS := hWLe a1 b1
  obtain hMul := Nat.mul_le_mul_left t hRS
  exact hMul

-- 739：WLe は wMul（右固定）で保たれる
theorem ex739 (R S T : WRel α β) :
    WLe R S → WLe (wMul R T) (wMul S T) := by
  -- 同じ列数・行数の三つの行列(R, S, T)があり、
  -- Rのすべての要素が対応するSの要素以下であったとする。
  -- この時、行列RとTを掛け合わせた行列と
  -- 行列SとTを掛け合わせた行列についても同じ関係が成り立つ。
  intro hWLe
  intro a1 b1
  dsimp [wMul]
  dsimp [WLe] at hWLe
  obtain hRS := hWLe a1 b1
  obtain hMul := Nat.mul_le_mul_right (T a1 b1) hRS
  exact hMul

-- 740：WLe は wTrans で保たれる
theorem ex740 (R S : WRel α β) :
    WLe R S → WLe (wTrans R) (wTrans S) := by
  -- 同じ列数・行数の二つの行列(R, S)があったとき、
  -- Rのすべての要素が対応するSの要素以下でとする。
  -- この時、R及びSを転置しても同じ関係が成り立つ。
  intro hWLe
  intro b1 a1
  dsimp [wTrans]
  obtain hRS := hWLe a1 b1
  exact hRS

--------------------------------------------------------------------------------
-- 741〜750：WSpec（「仕様の外は 0」）の計算規則・応用
--------------------------------------------------------------------------------

-- 741：transpose すると spec も transpose する
theorem ex741 (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wTrans R) (relTrans T) := by
  intro hWSpec
  dsimp [WSpec] at hWSpec
  intro b a
  dsimp [wTrans, relTrans]
  obtain hSpec := hWSpec a b
  exact hSpec

-- 742：スカラー倍しても spec は保たれる
theorem ex742 (t : Nat) (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wScale t R) T := by
  intro hWSpec a1 b1 hNotT
  dsimp [WSpec] at hWSpec
  obtain hSpec := hWSpec a1 b1 hNotT
  dsimp [wScale]
  rw [hSpec]
  rw [Nat.mul_zero]

-- 743：別々の spec を持つ 2 つを足すと、spec は OR（合併）になる
theorem ex743 (R S : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec S U → WSpec (wAdd R S) (relAdd T U) := by
  intro hWSpecR hWSpecS a1 b1 hNotTU
  dsimp [WSpec] at hWSpecR hWSpecS
  dsimp [relAdd] at hNotTU
  dsimp [wAdd]
  obtain hSpecR := hWSpecR a1 b1
  obtain hSpecS := hWSpecS a1 b1
  have hNotTU2 : ¬ T a1 b1 ∧ ¬ U a1 b1 := by
    constructor
    intro h1
    apply hNotTU
    left
    exact h1
    intro h2
    apply hNotTU
    right
    exact h2
  obtain ⟨hNotTU3, hNotTU4⟩ := hNotTU2
  obtain hSupcR2 := hSpecR hNotTU3
  obtain hSupcS2 := hSpecS hNotTU4
  rw [hSupcR2]
  rw [hSupcS2]

-- 744：mask すると spec は ∧（交差）へ強化できる
theorem ex744 (R : WRel α β) (T : Rel α β) (M : Rel α β) :
    WSpec R T → WSpec (wMask R M) (relMul T M) := by
  intro hWSpec a1 b1 hNotTM
  dsimp [WSpec] at hWSpec
  dsimp [relMul] at hNotTM
  dsimp [wMask, wMul, maskW]
  obtain hSpec := hWSpec a1 b1
  have hNotTM2 : ¬ T a1 b1 ∨ ¬ M a1 b1 := by
    by_cases hNotTM2_1 : T a1 b1
    right
    intro hNotTM2_2
    apply hNotTM
    constructor
    exact hNotTM2_1
    exact hNotTM2_2
    left
    exact hNotTM2_1
  obtain hNotT | hNotM := hNotTM2
  obtain hRab := hSpec hNotT
  rw [hRab]
  rw [Nat.zero_mul]
  rw [if_neg hNotM]
  rw [Nat.mul_zero]

-- 745：WSpec は “下に閉じる”（R ≤ S かつ S が spec なら R も spec）
theorem ex745 (R S : WRel α β) (T : Rel α β) :
    WLe R S → WSpec S T → WSpec R T := by
  intro hWLe hWSpec a1 b1 hNotT
  dsimp [WLe] at hWLe
  obtain hLe := hWLe a1 b1
  dsimp [WSpec] at hWSpec
  obtain hSpecS := hWSpec a1 b1
  obtain hSupcS2 := hSpecS hNotT
  rw [hSupcS2] at hLe
  rw [Nat.le_zero] at hLe
  exact hLe

-- 746：縮約（keys つき）での spec：relCompList keys で表せる（ex700 の強化）
theorem ex746 (keys : List β) (R : WRel α β) (S : WRel β γ)
    (T : Rel α β) (U : Rel β γ) :
    WSpec R T → WSpec S U → WSpec (wCompList keys R S) (relCompList keys T U) := by
  intro hWSpecR hWSpecS a1 c1 hNotTU
  dsimp [WSpec] at *
  dsimp [wCompList] at *
  dsimp [relCompList] at *
  obtain hNotTU2 : ∀ b, b ∈ keys → (R a1 b = 0) ∨ (S b c1 = 0) := by
    intro b hIn
    by_cases hNotTU2_1 : T a1 b
    right
    apply hWSpecS
    intro hNotTU2_2
    apply hNotTU
    exists b
    left
    apply hWSpecR
    exact hNotTU2_1
  clear hNotTU
  clear hWSpecR
  clear hWSpecS
  induction keys with
  | nil =>
    dsimp [wsum] at *
  | cons b1 bs ih =>
    dsimp [wsum] at *
    obtain hIn := List.mem_cons_self (a := b1)
    obtain hRab | hSbc := hNotTU2 b1 hIn
    rw [hRab]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    apply ih
    intro b2 hIn2
    obtain hIn3 := List.mem_cons_of_mem b1 hIn2
    obtain hNotTU3 := hNotTU2 b2 hIn3
    exact hNotTU3

    rw [hSbc]
    rw [Nat.mul_zero]
    rw [Nat.zero_add]
    apply ih
    intro b2 hIn2
    obtain hIn3 := List.mem_cons_of_mem b1 hIn2
    obtain hNotTU3 := hNotTU2 b2 hIn3
    exact hNotTU3

-- 747：spec の外しか見ない keys なら rowSum は 0
theorem ex747 (keys : List β) (R : WRel α β) (T : Rel α β) (a : α) :
    WSpec R T →
    (∀ b, b ∈ keys → ¬ T a b) →
      wRowSum keys R a = 0 := by

  intro hWSpec h2
  dsimp [WSpec] at hWSpec
  have h3 b hb := hWSpec a b (h2 b hb)
  dsimp [wRowSum]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b1 bs ih =>
    dsimp [wsum]
    obtain hIn := List.mem_cons_self (a := b1)
    obtain hRab := h3 b1 hIn
    rw [hRab]
    rw [Nat.zero_add]
    apply ih
    intro b2 hIn2
    obtain hIn3 := List.mem_cons_of_mem b1 hIn2
    obtain hNotT := h2 b2 hIn3
    exact hNotT
    intro b2
    intro hIn3
    obtain hIn4 := List.mem_cons_of_mem b1 hIn3
    obtain hRab := h3 b2 hIn4
    exact hRab

-- 748：spec の外しか見ない keys なら colSum は 0
theorem ex748 (keys : List α) (R : WRel α β) (T : Rel α β) (b : β) :
    WSpec R T →
    (∀ a, a ∈ keys → ¬ T a b) →
      wColSum keys R b = 0 := by

  intro hWSpec h2
  dsimp [WSpec] at hWSpec
  dsimp [wColSum]
  --have h3 b hb := hWSpec a b (h2 b hb)
  have h3 a hIn := hWSpec a b (h2 a hIn)
  clear hWSpec h2
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons a1 as ih =>
    dsimp [wsum]
    obtain h4 := h3 List.mem_cons_self (a := a1)
    rw [h4]
    rw [Nat.zero_add]
    apply ih
    intro a2 hIn2
    apply h3
    apply List.mem_cons_of_mem
    exact hIn2

-- 749：graph は自分の graph-spec を満たす
theorem ex749 (f : α → β) :
    WSpec (wGraph f) (relGraph f) := by
  intro a1 b1 hNotGraph
  dsimp [relGraph] at hNotGraph
  dsimp [wGraph, maskW, relGraph]
  rw [if_neg hNotGraph]

-- 750：multi-head（QK を足す）で spec が head ごとに違うなら、合併 spec になる（重みレベル）
theorem ex750 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ)
    (T1 T2 : Rel α γ) :
    WSpec (attnWRel keys QK1 KV) T1 →
    WSpec (attnWRel keys QK2 KV) T2 →
    WSpec (attnWRel keys (wAdd QK1 QK2) KV) (relAdd T1 T2) := by

  -- def WSpec {α β : Type} (R : WRel α β) (T : Rel α β) : Prop :=
  --   ∀ a b, (¬ T a b) → R a b = 0

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- def wAdd {α β : Type} (R S : WRel α β) : WRel α β :=
  --   fun a b => R a b + S a b

  -- def relAdd (R S : Rel α β) : Rel α β :=
  --   fun a b => R a b ∨ S a b

  -- T1かT2のどちらかに属していれば、
  -- attnWRel keys (wAdd QK1 QK2) KVは0よりも大きくなる可能性がある。

  -- TODO（ヒント：attnWRel は wCompList の別名。
  --   まず “線形性” で attn(wAdd QK1 QK2) を wAdd(attn QK1)(attn QK2) にしてから ex743 を使う）
  --dsimp [WSpec, attnWRel, wCompList, relAdd, wAdd]
  intro hWSpec1 hWSpec2 a1 c1 hNotT
  --dsimp [attnWRel, wCompList, wAdd]
  --dsimp [WSpec] at hWSpec1 hWSpec2
  obtain hEx743 := ex743 (wCompList keys QK1 KV) (wCompList keys QK2 KV) T1 T2 hWSpec1 hWSpec2 a1 c1 hNotT
  rw [wAdd] at hEx743
  rw [attnWRel]

  -- theorem ex511 (keys : List β) (R S : WRel α β) (T : WRel β γ) :
  --     wCompList keys (wAdd R S) T
  --       = wAdd (wCompList keys R T) (wCompList keys S T) := by
  obtain hEx511 :=
    ex511 keys QK1 QK2 KV
  rw [hEx511]
  exact hEx743

end TL
