--------------------------------------------------------------------------------
-- Basic_811.lean
-- 演習問題 811〜825（fast-track 5：wBool の代数 / 到達テンソル（0/1）/ ブリッジ補題）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 796〜810 は Basic_796 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_796

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wReachComp：wCompList の “到達だけ” 版）
--------------------------------------------------------------------------------

-- wCompList の「到達（>0）だけ」を 0/1 にしたもの
--   wReachComp keys R S a c = 1  ⇔  ∃ b∈keys, R a b >0 ∧ S b c >0
noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  maskW (relCompList keys (wSupp R) (wSupp S))

--------------------------------------------------------------------------------
-- 811〜815：wBool の基本代数（idempotent / transpose / Hadamard / scale）
--------------------------------------------------------------------------------

-- 811：wBool は 2 回かけても同じ（idempotent）
theorem ex811 (R : WRel α β) :
    wBool (wBool R) = wBool R := by
  -- ヒント：
  --   funext a b; dsimp [wBool]
  --   ex796（wSupp (wBool R) = wSupp R）
  funext a1 b1
  dsimp [wBool, maskW, wSupp]
  by_cases hRa1b1 : R a1 b1 > 0
  rw [if_pos hRa1b1]
  rw [if_pos Nat.zero_lt_one]
  rw [if_neg hRa1b1]
  rw [gt_iff_lt]
  rw [Nat.pos_iff_ne_zero]
  rw [if_neg]
  intro h
  apply h
  rfl

-- 812：0/1 行列は wBool で変わらない（maskW は固定点）
theorem ex812 (M : Rel α β) :
    wBool (maskW M) = maskW M := by
  -- ヒント：
  --   wBool の定義：maskW (wSupp _)
  --   ex613：wSupp (maskW M) = M
  funext a1 b1
  dsimp [wBool, maskW, wSupp]
  by_cases hMa1b1 : M a1 b1
  rw [if_pos hMa1b1]
  rw [if_pos Nat.zero_lt_one]
  rw [if_neg hMa1b1]
  rw [gt_iff_lt]
  rw [if_neg]
  intro h
  contradiction

-- 813：wBool は transpose と可換
theorem ex813 (R : WRel α β) :
    wBool (wTrans R) = wTrans (wBool R) := by
  -- ヒント：
  --   * wBool = maskW ∘ wSupp
  --   * ex666：wSupp (wTrans R) = relTrans (wSupp R)
  --   * ex785：wTrans (maskW M) = maskW (relTrans M)
  funext b1 a1
  dsimp [wBool, wTrans, maskW, wSupp]

-- 814：wBool は Hadamard 積（wMul）と相性がよい（∧ に対応）
theorem ex814 (R S : WRel α β) :
    wBool (wMul R S) = wMul (wBool R) (wBool S) := by
  -- ヒント：
  --   * ex667：wSupp (wMul R S) = relMul (wSupp R) (wSupp S)
  --   * ex783：wMul (maskW A) (maskW B) = maskW (relMul A B)
  --   * wBool の定義
  funext a1 b1
  dsimp [wBool, wMul, maskW, wSupp]
  by_cases hRa1b1 : R a1 b1 > 0
  rw [if_pos hRa1b1]
  rw [Nat.one_mul]
  by_cases hSa1b1 : S a1 b1 > 0
  rw [if_pos hSa1b1]
  rw [if_pos]
  apply Nat.mul_pos
  rw [←gt_iff_lt]
  exact hRa1b1
  rw [←gt_iff_lt]
  exact hSa1b1
  rw [if_neg hSa1b1]
  rw [if_neg]
  intro h
  apply hSa1b1
  obtain h2 := Nat.pos_of_mul_pos_left h
  contradiction
  rw [if_neg hRa1b1]
  rw [if_neg]
  rw [Nat.zero_mul]
  intro h3
  apply hRa1b1
  obtain h4 := Nat.pos_of_mul_pos_right h3
  contradiction

-- 815：t>0 のとき、wBool はスカラー倍で変わらない
theorem ex815 (t : Nat) (R : WRel α β) :
    t > 0 → wBool (wScale t R) = wBool R := by
  -- ヒント：
  --   * ex689：t>0 → wSupp (wScale t R) = wSupp R
  --   * wBool の定義
  intro ht
  funext a1 b1
  dsimp [wBool, wScale, maskW, wSupp]
  by_cases hRa1b1 : R a1 b1 > 0
  rw [if_pos hRa1b1]
  rw [if_pos]
  apply Nat.mul_pos
  exact ht
  exact hRa1b1
  rw [if_neg hRa1b1]
  obtain hRa1b1_2 :=
    Nat.eq_zero_of_not_pos hRa1b1
  rw [hRa1b1_2]
  rw [Nat.mul_zero]
  rw [if_neg]
  intro h
  contradiction

--------------------------------------------------------------------------------
-- 816〜820：wBool / wReachComp と wCompList・row/col-sum の到達
--------------------------------------------------------------------------------


-- 816：wAdd の wBool は “OR” になる（multi-head の到達だけ残す）
theorem ex816 (R S : WRel α β) :
    wBool (wAdd R S) = maskW (relAdd (wSupp R) (wSupp S)) := by
  -- TODO
  -- ヒント：
  --   * wBool の定義
  --   * ex612：wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S)
  sorry


-- 817：wCompList を wBool しても、到達（∃ witness）は relCompList(keys, supp, supp) に一致
theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wBool (wCompList keys R S) = wReachComp keys R S := by
  -- TODO
  -- ヒント：
  --   * wReachComp の定義
  --   * ex621：wSupp (wCompList ...) = relCompList keys (wSupp R) (wSupp S)
  --   * wBool の定義
  sorry


-- 818：wReachComp の support は relCompList(keys, supp, supp)
theorem ex818 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wReachComp keys R S) = relCompList keys (wSupp R) (wSupp S) := by
  -- TODO
  -- ヒント：wReachComp の定義と ex613
  sorry


-- 819：Rel の count 合成を wBool すると、wReachComp（maskW で lifted したもの）と一致
theorem ex819 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    wBool (wCountComp keys R S) = wReachComp keys (maskW R) (maskW S) := by
  -- TODO
  -- ヒント：
  --   * ex805：wBool (wCountComp keys R S) = maskW (relCompList keys R S)
  --   * wReachComp の定義（supp (maskW R) = R, supp (maskW S) = S）
  --   * ex613
  sorry


-- 820：wBool にしても rowSum>0（到達性）は変わらない
-- （重みの大小は捨てるが、存在は保たれる）
theorem ex820 (keys : List β) (R : WRel α β) (a : α) :
    (wRowSum keys (wBool R) a > 0) ↔ (wRowSum keys R a > 0) := by
  -- TODO
  -- ヒント：
  --   * ex710：rowSum>0 ↔ ∃ b∈keys, R a b >0
  --   * ex796：wSupp (wBool R) = wSupp R
  sorry


--------------------------------------------------------------------------------
-- 821〜825：colSum 版・spec と wBool の相性・固定点（wId / wGraph）
--------------------------------------------------------------------------------


-- 821：wBool にしても colSum>0（到達性）は変わらない
theorem ex821 (keys : List α) (R : WRel α β) (b : β) :
    (wColSum keys (wBool R) b > 0) ↔ (wColSum keys R b > 0) := by
  -- TODO
  -- ヒント：ex712 と ex796
  sorry


-- 822：spec は wBool しても保たれる（仕様外は 0 のまま）
theorem ex822 (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wBool R) T := by
  -- TODO
  -- ヒント：
  --   * ex691：WSpec ↔ support ⊆ T
  --   * ex796：support(wBool)=support
  sorry


-- 823：spec を満たすなら、wBool もその spec でマスクして変わらない
theorem ex823 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wMask (wBool R) T = wBool R := by
  -- TODO
  -- ヒント：
  --   * ex822 で WSpec (wBool R) T
  --   * ex758（WSpec X T → wMask X T = X）を X:=wBool R に適用
  sorry


-- 824：wReachComp は両側を wBool に置き換えても不変（到達だけを見るので）
theorem ex824 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp keys (wBool R) (wBool S) = wReachComp keys R S := by
  -- TODO
  -- ヒント：
  --   * wReachComp は supp だけを見る
  --   * ex796 を 2 回使う
  sorry


-- 825：wId / wGraph は 0/1 行列なので wBool の固定点
theorem ex825_id :
    wBool (wId α) = wId α := by
  -- TODO
  -- ヒント：wId の定義（maskW (relId α)）と ex812
  sorry


theorem ex825_graph (f : α → β) :
    wBool (wGraph f) = wGraph f := by
  -- TODO
  -- ヒント：wGraph の定義（maskW (relGraph f)）と ex812
  sorry


end TL
