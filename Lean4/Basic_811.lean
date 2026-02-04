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
-- keysの中にR a b > 0 ∧ S b c > 0 a となるような b が存在すれば 1、そうでなければ 0
noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  maskW (relCompList keys (wSupp R) (wSupp S))
-- noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
--   fun a c => if (∃ b, b ∈ keys ∧ (R a b > 0) ∧ (S b c > 0)) then 1 else 0

--------------------------------------------------------------------------------
-- 811〜815：wBool の基本代数（idempotent / transpose / Hadamard / scale）
--------------------------------------------------------------------------------

-- 811：wBool は 2 回かけても同じ（idempotent）
theorem ex811 (R : WRel α β) :
    wBool (wBool R) = wBool R := by
  -- TODO
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
  -- ヒント：
  --   * wBool の定義
  --   * ex612：wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S)
  funext a1 b1
  dsimp [relAdd, wBool, wAdd, maskW, wSupp]
  by_cases hRa1b1 : R a1 b1 > 0
  have h1 : R a1 b1 > 0 ∨ S a1 b1 > 0 :=
    Or.inl hRa1b1
  rw [if_pos h1]
  have h2 : R a1 b1 + S a1 b1 > 0 := by
    rw [gt_iff_lt]
    rw [Nat.add_pos_iff_pos_or_pos]
    left
    rw [←gt_iff_lt]
    exact hRa1b1
  rw [if_pos h2]
  by_cases hSa1b1 : S a1 b1 > 0
  have h3 : R a1 b1 > 0 ∨ S a1 b1 > 0 :=
    Or.inr hSa1b1
  rw [if_pos h3]
  have h4 : R a1 b1 + S a1 b1 > 0 := by
    rw [gt_iff_lt]
    rw [Nat.add_pos_iff_pos_or_pos]
    right
    rw [←gt_iff_lt]
    exact hSa1b1
  rw [if_pos h4]
  have h5 : ¬ (R a1 b1 > 0 ∨ S a1 b1 > 0) := by
    intro h5
    obtain h5_1 | h5_2 := h5
    apply hRa1b1
    exact h5_1
    apply hSa1b1
    exact h5_2
  rw [if_neg h5]
  have h6 : R a1 b1 + S a1 b1 = 0 := by
    rw [Nat.add_eq_zero_iff]
    constructor
    rw [Nat.eq_zero_of_not_pos hRa1b1]
    rw [Nat.eq_zero_of_not_pos hSa1b1]
  rw [h6]
  rw [if_neg]
  intro h7
  contradiction

-- 817：wCompList を wBool しても、到達（∃ witness）は relCompList(keys, supp, supp) に一致
theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wBool (wCompList keys R S) = wReachComp keys R S := by
  -- ヒント：
  --   * wReachComp の定義
  --   * ex621：wSupp (wCompList ...) = relCompList keys (wSupp R) (wSupp S)
  --   * wBool の定義

  -- def relCompList {α β γ : Type} (keys : List β) (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  --   fun a c => ∃ b, b ∈ keys ∧ R a b ∧ S b c
  -- noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   maskW (relCompList keys (wSupp R) (wSupp S))

  funext a1 c1
  dsimp [wBool, wCompList, wReachComp, maskW, wSupp, relCompList]
  by_cases h : ∃ b, b ∈ keys ∧ (R a1 b > 0) ∧ (S b c1 > 0)
  rw [if_pos h]
  obtain ⟨b1, hb1_in_keys, hR_ab1, hS_b1c1⟩ := h
  induction keys with
  | nil =>
    contradiction
  | cons b2 keys_tail ih =>
    dsimp [wsum]
    by_cases h_b1_eq_b2 : b1 = b2
    -- b1 = b2 の場合
    rw [←h_b1_eq_b2]
    have h2 : (R a1 b1 * S b1 c1 + wsum keys_tail fun b => R a1 b * S b c1) > 0 := by
      rw [gt_iff_lt]
      apply Nat.add_pos_iff_pos_or_pos.mpr
      left
      apply Nat.mul_pos
      rw [←gt_iff_lt]
      exact hR_ab1
      rw [←gt_iff_lt]
      exact hS_b1c1
    rw [if_pos h2]
    -- b1 ≠ b2 の場合
    obtain h3 :=
      List.mem_of_ne_of_mem h_b1_eq_b2 hb1_in_keys
    obtain ih2 := ih h3
    clear ih
    have h4 : (wsum keys_tail fun b => R a1 b * S b c1) > 0 := by
      by_cases h4_1 : (wsum keys_tail fun b => R a1 b * S b c1) > 0
      exact h4_1
      rw [if_neg h4_1] at ih2
      contradiction
    have h5 : (R a1 b2 * S b2 c1 + wsum keys_tail fun b => R a1 b * S b c1) > 0 := by
      rw [gt_iff_lt]
      apply Nat.add_pos_iff_pos_or_pos.mpr
      right
      exact h4
    rw [if_pos h5]
  rw [if_neg h]
  have h6 : (wsum keys fun b => R a1 b * S b c1) = 0 := by
    induction keys with
    | nil =>
      dsimp [wsum]
    | cons b2 keys_tail ih =>
      dsimp [wsum]
      rw [Nat.add_eq_zero_iff]
      constructor

      -- cons.left
      apply Nat.mul_eq_zero.mpr
      have h7 : ¬(R a1 b2 > 0 ∧ S b2 c1 > 0) := by
        intro h7_1
        apply h
        exists b2
        constructor
        apply List.mem_cons_self
        exact h7_1
      by_cases h7_2 : R a1 b2 = 0
      left
      exact h7_2
      obtain h8 := Nat.pos_iff_ne_zero.mpr h7_2
      have h9 : ¬ (S b2 c1 > 0) := by
        intro h9_1
        apply h7
        constructor
        exact h8
        exact h9_1
      right
      apply Nat.eq_zero_of_not_pos
      exact h9

      -- cons.right
      apply ih
      intro h10
      apply h
      obtain ⟨b3, hb3_in_keys, hR_ab3, hS_b3c1⟩ := h10
      exists b3
      constructor
      apply List.mem_cons_of_mem
      exact hb3_in_keys
      constructor
      exact hR_ab3
      exact hS_b3c1
  rw [h6]
  rw [if_neg]
  intro h7
  contradiction

-- 818：wReachComp の support は relCompList(keys, supp, supp)
theorem ex818 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wReachComp keys R S) = relCompList keys (wSupp R) (wSupp S) := by
  -- ヒント：wReachComp の定義と ex613
  dsimp [wReachComp]

-- theorem ex613 (M : Rel α β) :
--     wSupp (maskW M) = M
  obtain hEx613 :=
    ex613 (relCompList keys (wSupp R) (wSupp S))
  rw [hEx613]

-- 819：Rel の count 合成を wBool すると、wReachComp（maskW で lifted したもの）と一致
theorem ex819 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    wBool (wCountComp keys R S) = wReachComp keys (maskW R) (maskW S) := by
  -- ヒント：
  --   * ex805：wBool (wCountComp keys R S) = maskW (relCompList keys R S)
  --   * wReachComp の定義（supp (maskW R) = R, supp (maskW S) = S）
  --   * ex613

  -- theorem ex805 (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     wBool (wCountComp keys R S) = maskW (relCompList keys R S)
  obtain hEx805 :=
    ex805 keys R S
  rw [hEx805]
  clear hEx805
  dsimp [wReachComp]

  obtain hEx613_R :=
    ex613 R
  obtain hEx613_S :=
    ex613 S
  rw [hEx613_R]
  rw [hEx613_S]

-- 820：wBool にしても rowSum>0（到達性）は変わらない
-- （重みの大小は捨てるが、存在は保たれる）
theorem ex820 (keys : List β) (R : WRel α β) (a : α) :
    (wRowSum keys (wBool R) a > 0) ↔ (wRowSum keys R a > 0) := by
  -- ヒント：
  --   * ex710：rowSum>0 ↔ ∃ b∈keys, R a b >0
  --   * ex796：wSupp (wBool R) = wSupp R

  -- theorem ex710 (keys : List β) (R : WRel α β) (a : α) :
  --     wRowSum keys R a > 0 ↔ ∃ b, b ∈ keys ∧ R a b > 0 := by
  obtain hEx710_bool :=
    ex710 keys (wBool R) a
  obtain hEx710_R :=
    ex710 keys R a
  rw [hEx710_bool]
  rw [hEx710_R]
  clear hEx710_bool
  clear hEx710_R
  constructor
  intro h1
  obtain ⟨b1, hb1_in_keys, hR_a_b1⟩ := h1
  exists b1
  constructor
  exact hb1_in_keys
  rw [wBool, maskW, wSupp] at hR_a_b1
  by_cases hR_a_b1_pos : R a b1 > 0
  exact hR_a_b1_pos
  rw [if_neg hR_a_b1_pos] at hR_a_b1
  contradiction
  intro h2
  obtain ⟨b2, hb2_in_keys, hR_a_b2⟩ := h2
  exists b2
  constructor
  exact hb2_in_keys
  rw [wBool, maskW, wSupp]
  rw [if_pos hR_a_b2]
  rw [gt_iff_lt]
  exact Nat.zero_lt_one

--------------------------------------------------------------------------------
-- 821〜825：colSum 版・spec と wBool の相性・固定点（wId / wGraph）
--------------------------------------------------------------------------------

-- 821：wBool にしても colSum>0（到達性）は変わらない
theorem ex821 (keys : List α) (R : WRel α β) (b : β) :
    (wColSum keys (wBool R) b > 0) ↔ (wColSum keys R b > 0) := by
  -- ヒント：ex712 と ex796

  -- theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
  --     wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0 := by
  obtain hEx712_wBool_R :=
    ex712 keys (wBool R) b
  obtain hEx712_R :=
    ex712 keys R b
  rw [hEx712_wBool_R]
  rw [hEx712_R]
  clear hEx712_wBool_R
  clear hEx712_R
  constructor
  intro h1
  obtain ⟨a1, ha1_in_keys, hR_a1_b⟩ := h1
  exists a1
  constructor
  exact ha1_in_keys
  rw [wBool, maskW, wSupp] at hR_a1_b
  by_cases hR_a1_b_pos : R a1 b > 0
  exact hR_a1_b_pos
  rw [if_neg hR_a1_b_pos] at hR_a1_b
  contradiction
  intro h2
  obtain ⟨a2, ha2_in_keys, hR_a2_b⟩ := h2
  exists a2
  constructor
  exact ha2_in_keys
  rw [wBool, maskW, wSupp]
  rw [if_pos hR_a2_b]
  rw [gt_iff_lt]
  exact Nat.zero_lt_one

-- 822：spec は wBool しても保たれる（仕様外は 0 のまま）
theorem ex822 (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wBool R) T := by
  -- ヒント：
  --   * ex691：WSpec ↔ support ⊆ T
  --   * ex796：support(wBool)=support
  intro hWSpec_R_T

  -- theorem ex691 (R : WRel α β) (T : Rel α β) :
  --     WSpec R T ↔ (wSupp R ⊆ T)
  obtain hEx691_R_T :=
    ex691 R T
  rw [hEx691_R_T] at hWSpec_R_T
  clear hEx691_R_T

  obtain hEx691_wBool_R_T :=
    ex691 (wBool R) T
  rw [hEx691_wBool_R_T]
  clear hEx691_wBool_R_T

  -- theorem ex796 (R : WRel α β) :
  --     wSupp (wBool R) = wSupp R := by
  obtain hEx796 :=
    ex796 R
  rw [hEx796]
  clear hEx796

  exact hWSpec_R_T

-- 823：spec を満たすなら、wBool もその spec でマスクして変わらない
theorem ex823 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wMask (wBool R) T = wBool R := by
  -- ヒント：
  --   * ex822 で WSpec (wBool R) T
  --   * ex758（WSpec X T → wMask X T = X）を X:=wBool R に適用

  -- theorem ex822 (R : WRel α β) (T : Rel α β) :
  --     WSpec R T → WSpec (wBool R) T := by
  obtain hEx822 :=
    ex822 R T
  intro hWSpec_R_T
  have hWSpec_wBool_R_T :=
    hEx822 hWSpec_R_T
  clear hEx822

  -- theorem ex758 (R : WRel α β) (T : Rel α β) :
  --     WSpec R T → wMask R T = R := by
  obtain hEx758 :=
    ex758 (wBool R) T hWSpec_wBool_R_T
  apply hEx758

-- 824：wReachComp は両側を wBool に置き換えても不変（到達だけを見るので）
theorem ex824 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp keys (wBool R) (wBool S) = wReachComp keys R S := by
  -- ヒント：
  --   * wReachComp は supp だけを見る
  --   * ex796 を 2 回使う
  dsimp [wReachComp]
  -- theorem ex796 (R : WRel α β) :
  --     wSupp (wBool R) = wSupp R := by
  obtain hEx796_R :=
    ex796 R
  obtain hEx796_S :=
    ex796 S
  rw [hEx796_R]
  rw [hEx796_S]

-- 825：wId / wGraph は 0/1 行列なので wBool の固定点
theorem ex825_id :
    wBool (wId α) = wId α := by
  -- ヒント：wId の定義（maskW (relId α)）と ex812
  -- theorem ex812 (M : Rel α β) :
  --     wBool (maskW M) = maskW M
  dsimp [wId]
  obtain hEx812 :=
    ex812 (relId α)
  apply hEx812

theorem ex825_graph (f : α → β) :
    wBool (wGraph f) = wGraph f := by
  -- ヒント：wGraph の定義（maskW (relGraph f)）と ex812
  -- theorem ex812 (M : Rel α β) :
  --     wBool (maskW M) = maskW M
  dsimp [wGraph]
  obtain hEx812 :=
    ex812 (relGraph f)
  apply hEx812

end TL
