--------------------------------------------------------------------------------
-- Basic_871.lean
-- 演習問題 871〜885（fast-track 9：wReachComp / wsumW を “OR-AND 半環” として扱う）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 856〜870 は Basic_856 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_856

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε ι : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wOr：0/1 の OR）
--------------------------------------------------------------------------------

-- OR（到達の和）：重みは捨て、>0 だけ残す
noncomputable def wOr (R S : WRel α β) : WRel α β :=
  wBool (wAdd R S)

--------------------------------------------------------------------------------
-- 871〜875：wOr の代数（comm / assoc / idem / zero）
--------------------------------------------------------------------------------

-- 871：support(wOr) は論理和（∨）
theorem ex871 (R S : WRel α β) :
    wSupp (wOr R S) = relAdd (wSupp R) (wSupp S) := by
  -- ヒント：
  --   * wOr の定義
  --   * ex816（wBool (wAdd ...) = maskW (relAdd ...)）
  --   * ex613（support(maskW M)=M）
  funext a1 b1
  dsimp [wOr, wBool, wAdd, wSupp, relAdd, maskW]
  by_cases h1 : R a1 b1 + S a1 b1 > 0
  rw [if_pos h1]
  rw [gt_iff_lt] at h1
  rw [Nat.add_pos_iff_pos_or_pos] at h1
  apply propext
  constructor
  intro h2
  exact h1
  intro h2
  apply Nat.zero_lt_one
  rw [if_neg h1]
  apply propext
  constructor
  intro h3
  contradiction
  intro h4
  apply False.elim
  apply h1
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  exact h4

-- 872：wOr は可換
theorem ex872 (R S : WRel α β) :
    wOr R S = wOr S R := by
  -- ヒント：funext; dsimp [wOr, wAdd]; Nat.add_comm
  funext a1 b1
  dsimp [wOr, wAdd, wBool, maskW, wSupp]
  by_cases h1 : R a1 b1 + S a1 b1 > 0
  rw [if_pos h1]
  rw [if_pos]
  rw [Nat.add_comm]
  exact h1
  rw [if_neg h1]
  rw [if_neg]
  rw [Nat.add_comm]
  exact h1

-- 873：wOr は結合的
theorem ex873 (R S T : WRel α β) :
    wOr (wOr R S) T = wOr R (wOr S T) := by
  -- ヒント：Nat.add_assoc と ex811（wBool の冪等性）など
  funext a1 b1
  dsimp [wOr, wAdd, wBool, maskW, wSupp]
  by_cases h1 : 0 < R a1 b1
  by_cases h2 : 0 < S a1 b1
  by_cases h3 : 0 < T a1 b1
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h2
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h3
  obtain h3_1 := Nat.eq_zero_of_not_pos h3
  clear h3
  rw [h3_1]
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  exact h2
  rw [gt_iff_lt]
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h1
  obtain h2_1 := Nat.eq_zero_of_not_pos h2
  clear h2
  rw [h2_1]
  rw [Nat.add_zero]
  rw [Nat.zero_add]
  by_cases h3 : 0 < T a1 b1
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  exact h3
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  exact h1
  obtain h3_1 := Nat.eq_zero_of_not_pos h3
  clear h3
  rw [h3_1]
  rw [Nat.add_zero]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h1
  rw [gt_iff_lt]
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  exact h1
  obtain h1_1 := Nat.eq_zero_of_not_pos h1
  clear h1
  rw [h1_1]
  rw [Nat.zero_add]
  rw [Nat.zero_add]
  by_cases h2 : 0 < S a1 b1
  by_cases h3 : 0 < T a1 b1
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h3
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h3
  obtain h3_1 := Nat.eq_zero_of_not_pos h3
  clear h3
  rw [h3_1]
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  obtain h2_1 := Nat.eq_zero_of_not_pos h2
  clear h2
  rw [h2_1]
  by_cases h3 : 0 < T a1 b1
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h3
  rw [if_neg]
  rw [Nat.zero_add]
  rw [gt_iff_lt]
  exact h3
  intro h4
  have h4_2 : R a1 b1 + S a1 b1 = 0 := by
    rw [h1_1, h2_1]
  have h4_3 :=
    Nat.ne_zero_iff_zero_lt.mpr h4
  contradiction
  obtain h3_1 := Nat.eq_zero_of_not_pos h3
  clear h3
  rw [h3_1]
  rw [Nat.zero_add]
  rw [Nat.add_zero]

-- 874：wOr は冪等（R ∨ R = R の 0/1 版）
theorem ex874 (R : WRel α β) :
    wOr R R = wBool R := by
  -- ヒント：support が同じことを示して wBool に落とす（ex796 / ex816）
  funext a1 b1
  dsimp [wOr, wAdd, wBool, maskW, wSupp]
  by_cases h1: R a1 b1 > 0
  rw [if_pos h1]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h1
  obtain h2 :=
    Nat.eq_zero_of_not_pos h1
  clear h1
  rw [h2]

-- 875：wZero は wOr の単位元（ただし結果は wBool R）
theorem ex875 (R : WRel α β) :
    wOr R (wZero α β) = wBool R := by
  -- ヒント：wAdd R 0 = R, wOr 定義
  funext a1 b1
  dsimp [wOr, wAdd, wBool, wZero, maskW, wSupp]

--------------------------------------------------------------------------------
-- 876〜880：wReachComp と wOr の相互作用（分配・zero）
--------------------------------------------------------------------------------

-- 876：reach は wOr（左）に分配する
theorem ex876 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    wReachComp keys (wOr R R') S
      =
    wOr (wReachComp keys R S) (wReachComp keys R' S) := by
  -- ヒント：wReachComp は support だけを見る（ex818） + ex871
  funext a1 c1
  dsimp [wReachComp, wOr, wSupp, relCompList, relAdd, maskW, wBool, wAdd]

  by_cases h1 :
    ∃ b, b ∈ keys ∧ (if R a1 b + R' a1 b > 0 then 1 else 0) > 0 ∧ S b c1 > 0
  -- pos
  obtain ⟨b1, h2, h3, h4⟩ := h1
  have h3_1 : R a1 b1 + R' a1 b1 > 0 := by
    by_cases h_ : R a1 b1 + R' a1 b1 > 0
    exact h_
    rw [if_neg h_] at h3
    contradiction
  clear h3

  rw [gt_iff_lt] at h3_1
  rw [Nat.add_pos_iff_pos_or_pos] at h3_1
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain h3_1_1 | h3_1_2 := h3_1
  left
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  right
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  exists b1
  constructor
  exact h2
  rw [if_pos]
  constructor
  apply Nat.zero_lt_one
  exact h4
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain h3_2 | h3_3 := h3_1
  left
  exact h3_2
  right
  exact h3_3
  rw [if_neg]
  rw [if_neg]
  intro h5
  apply h1
  clear h1
  rw [gt_iff_lt] at h5
  rw [Nat.add_pos_iff_pos_or_pos] at h5
  obtain h5_1 | h5_2 := h5
  have h5_3 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h5_1
    contradiction
  clear h5_1
  obtain ⟨b1, h6, h7, h8⟩ := h5_3
  exists b1
  constructor
  exact h6
  rw [if_pos]
  constructor
  apply Nat.zero_lt_one
  exact h8
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h7
  have h5_4 : ∃ b, b ∈ keys ∧ R' a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R' a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h5_2
    contradiction
  clear h5_2
  obtain ⟨b1, h6, h7, h8⟩ := h5_4
  exists b1
  constructor
  exact h6
  rw [if_pos]
  constructor
  apply Nat.zero_lt_one
  exact h8
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h7
  intro h9
  apply h1
  clear h1
  obtain ⟨b2, h10, h11, h12⟩ := h9
  have h11_1 : R a1 b2 + R' a1 b2 > 0 := by
    by_cases h_ : R a1 b2 + R' a1 b2 > 0
    exact h_
    rw [if_neg h_] at h11
    contradiction
  clear h11
  exists b2
  rw [if_pos]
  constructor
  exact h10
  constructor
  apply Nat.zero_lt_one
  exact h12
  exact h11_1

-- 877：reach は wOr（右）に分配する
theorem ex877 (keys : List β) (R : WRel α β) (S S' : WRel β γ) :
    wReachComp keys R (wOr S S')
      =
    wOr (wReachComp keys R S) (wReachComp keys R S') := by

  -- ヒント：wReachComp は support だけを見る（ex818） + ex871
  funext a1 c1
  dsimp [wReachComp, wOr, wSupp, relCompList, relAdd, maskW, wBool, wAdd]

  by_cases h1 :
    ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if S b c1 + S' b c1 > 0 then 1 else 0) > 0

  -- pos
  obtain ⟨b1, h2, h3, h4⟩ := h1
  have h4_1 : S b1 c1 + S' b1 c1 > 0 := by
    by_cases h_ : S b1 c1 + S' b1 c1 > 0
    exact h_
    rw [if_neg h_] at h4
    contradiction
  clear h4
  rw [gt_iff_lt] at h4_1
  rw [Nat.add_pos_iff_pos_or_pos] at h4_1
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain h4_2 | h4_3 := h4_1
  left
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  right
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  exists b1
  constructor
  exact h2
  constructor
  exact h3
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  exact h4_1
  rw [if_neg]
  rw [if_neg]
  intro h5
  apply h1
  rw [gt_iff_lt] at h5
  rw [Nat.add_pos_iff_pos_or_pos] at h5
  obtain h5_1 | h5_2 := h5
  have h5_3 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h5_1
    contradiction
  clear h5_1
  obtain ⟨b1, h6, h7, h8⟩ := h5_3
  exists b1
  constructor
  exact h6
  constructor
  exact h7
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h8
  have h5_4 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S' b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S' b c1 > 0
    exact h_
    rw [if_neg h_] at h5_2
    contradiction
  clear h5_2
  obtain ⟨b1, h6, h7, h8⟩ := h5_4
  exists b1
  constructor
  exact h6
  constructor
  exact h7
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact h8
  intro h9
  apply h1
  obtain ⟨b2, h10, h11, h12⟩ := h9
  have h12_1 : S b2 c1 + S' b2 c1 > 0 := by
    by_cases h_ : S b2 c1 + S' b2 c1 > 0
    exact h_
    rw [if_neg h_] at h12
    contradiction
  clear h12
  exists b2
  constructor
  exact h10
  constructor
  exact h11
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h12_1

-- 878：zero と reach（左が 0）
theorem ex878 (keys : List β) (S : WRel β γ) :
    wReachComp keys (wZero α β) S = wZero α γ := by
  -- ヒント：wSupp(wZero)=False → relCompList が空
  funext a1 c1
  dsimp [wReachComp, wZero, wSupp, relCompList, maskW]
  rw [if_neg]
  intro h1
  obtain ⟨b1, h2, h3, h4⟩ := h1
  contradiction

-- 879：zero と reach（右が 0）
theorem ex879 (keys : List β) (R : WRel α β) :
    wReachComp keys R (wZero β γ) = wZero α γ := by
  -- ヒント：wSupp(wZero)=False → relCompList が空
  funext a1 c1
  dsimp [wReachComp, wZero, wSupp, relCompList, maskW]
  rw [if_neg]
  intro h1
  obtain ⟨b1, h2, h3, h4⟩ := h1
  contradiction

-- 880：reach の結果は常に 0/1（wBool の固定点）
theorem ex880 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wBool (wReachComp keys R S) = wReachComp keys R S := by
  -- ヒント：wReachComp は maskW で定義されているので ex812
  funext a1 c1
  dsimp [wReachComp, wBool, maskW, wSupp, relCompList]
  by_cases h1 :
    ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
  rw [if_pos h1]
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  contradiction

--------------------------------------------------------------------------------
-- 881〜885：wsumW と reach（OR-和との分配・graph 特別ケース）
--------------------------------------------------------------------------------

-- 881：reach は wsumW（左）に分配する
theorem ex881 (keysβ : List β) (keysι : List ι)
    (F : ι → WRel α β) (S : WRel β γ) :
    wReachComp keysβ (wsumW keysι F) S
      =
    wsumW keysι (fun i => wReachComp keysβ (F i) S) := by
  -- ヒント：support で示すのが楽：ex818 + ex846
  funext a1 c1
  dsimp [wReachComp, wsumW, wSupp, relCompList, maskW, wBool, wAdd]
  conv =>
    conv =>
      lhs
      arg 1
      arg 1
      intro b1
      rhs
      arg 1
      arg 1
      arg 1
      rw [ex606]
    conv =>
      rhs
      arg 1
      rw [ex606]

  by_cases h1 :
    ∃ b1, b1 ∈ keysβ ∧ (if ∃ x, x ∈ keysι ∧ F x a1 b1 > 0 then 1 else 0) > 0 ∧ S b1 c1 > 0

  -- pos
  rw [if_pos h1]
  obtain ⟨b2, h2, h3, h4⟩ := h1
  have h3_1 : ∃ x, x ∈ keysι ∧ F x a1 b2 > 0 := by
    by_cases h_ : ∃ x, x ∈ keysι ∧ F x a1 b2 > 0
    exact h_
    rw [if_neg h_] at h3
    contradiction
  clear h3
  obtain ⟨i1, h5, h6⟩ := h3_1
  rw [if_pos]
  exists i1
  constructor
  exact h5
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b2

  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h6
  apply h1
  obtain ⟨b2, h7, h8⟩ := h6
  have h8_1 : ∃ b, b ∈ keysβ ∧ F b2 a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keysβ ∧ F b2 a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h8
    contradiction
  clear h8
  obtain ⟨b3, h9, h10, h11⟩ := h8_1
  exists b3
  constructor
  exact h9
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b2
  exact h11

-- 882：keys がすべて含むなら wId は本当の右単位になる
theorem ex882 (keysβ : List β) (R : WRel α β) :
    (∀ b : β, b ∈ keysβ) →
      wReachComp keysβ R (wId β) = wBool R := by
  -- ヒント：ex842 の RHS で b∈keysβ を消す
  intro h1
  funext a1 b1
  dsimp [wReachComp, wId, wBool, wSupp, relCompList, maskW, relId]
  by_cases h2 :
    ∃ b, b ∈ keysβ ∧ R a1 b > 0 ∧ (if b = b1 then 1 else 0) > 0

  -- pos
  rw [if_pos h2]
  obtain ⟨b2, h3, h4, h5⟩ := h2
  have h5_1 : b2 = b1 := by
    by_cases h_ : b2 = b1
    exact h_
    rw [if_neg h_] at h5
    contradiction
  clear h5
  rw [if_pos]
  rw [←h5_1]
  exact h4

  -- neg
  rw [if_neg h2]
  rw [if_neg]
  intro h6
  apply h2
  exists b1
  obtain h7 := h1 b1
  constructor
  exact h7
  constructor
  exact h6
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

-- 883：keys がすべて含むなら wId は本当の左単位になる
theorem ex883 (keysα : List α) (R : WRel α β) :
    (∀ a : α, a ∈ keysα) →
      wReachComp keysα (wId α) R = wBool R := by
  -- ヒント：ex841 の RHS で a∈keysα を消す
  intro h1
  funext a1 b1
  dsimp [wReachComp, wId, wBool, wSupp, relCompList, maskW, relId]
  by_cases h2 :
    ∃ b, b ∈ keysα ∧ (if a1 = b then 1 else 0) > 0 ∧ R b b1 > 0

  -- pos
  rw [if_pos h2]
  obtain ⟨b2, h3, h4, h5⟩ := h2
  have h4_1 : a1 = b2 := by
    by_cases h_ : a1 = b2
    exact h_
    rw [if_neg h_] at h4
    contradiction
  clear h4
  rw [if_pos]
  rw [h4_1]
  exact h5

  -- neg
  rw [if_neg h2]
  rw [if_neg]
  intro h6
  apply h2
  exists a1
  obtain h7 := h1 a1
  constructor
  exact h7
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  exact h6

-- 884：graph を右に置いた reach の support（存在条件）
theorem ex884 (keys : List β) (R : WRel α β) (g : β → γ) :
    wSupp (wReachComp keys R (wGraph g))
      =
    (fun a c => ∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by
  -- ヒント：ex818 + wSupp(wGraph g)=relGraph g
  funext a1 c1
  dsimp [wReachComp, wGraph, wSupp, relCompList, relGraph, maskW]
  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if g b = c1 then 1 else 0) > 0

  -- pos
  rw [if_pos h1]
  obtain ⟨b1, h2, h3, h4⟩ := h1
  have h4_1 : g b1 = c1 := by
    by_cases h_ : g b1 = c1
    exact h_
    rw [if_neg h_] at h4
    contradiction
  clear h4
  apply propext
  constructor
  intro h5
  exists b1
  intro h6
  apply Nat.zero_lt_one

  -- neg
  rw [if_neg h1]
  apply propext
  constructor
  intro h7
  contradiction
  intro h8
  obtain ⟨b2, h9, h10, h11⟩ := h8
  apply False.elim
  apply h1
  exists b2
  constructor
  exact h9
  constructor
  exact h10
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h11

-- 885：graph を右に置いた reach は “列の行選択” の OR-和（Basic_841 の復習）
theorem ex885 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    wsumW keys (fun b =>
      wMask (fun a _ => wBool R a b) (fun _ c => g b = c)) := by
  -- ヒント：Basic_841.ex843
  funext a1 c1
  dsimp [wReachComp, wGraph, wsumW, wMask, wBool, wSupp, relCompList, relGraph, maskW, wAdd]
  conv =>
    rhs
    arg 1
    rw [ex606]

  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if g b = c1 then 1 else 0) > 0

  -- pos
  rw [if_pos h1]
  obtain ⟨b2, h2, h3, h4⟩ := h1
  have h4_1 : g b2 = c1 := by
    by_cases h_ : g b2 = c1
    exact h_
    rw [if_neg h_] at h4
    contradiction
  clear h4
  rw [if_pos]
  exists b2
  constructor
  exact h2
  rw [gt_iff_lt]
  apply Nat.mul_pos
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h3
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h4_1

  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h5
  apply h1
  obtain ⟨b2, h6, h7⟩ := h5
  rw [gt_iff_lt] at h7
  have  h7_1 : 0 < R a1 b2 := by
    by_cases h_ : 0 < R a1 b2
    exact h_
    rw [if_neg h_] at h7
    rw [Nat.zero_mul] at h7
    contradiction
  have  h7_2 : g b2 = c1 := by
    by_cases h_ : g b2 = c1
    exact h_
    rw [if_neg h_] at h7
    contradiction
  clear h7
  exists b2
  constructor
  exact h6
  constructor
  exact h7_1
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h7_2

end TL
