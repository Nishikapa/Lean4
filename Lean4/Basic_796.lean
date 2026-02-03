--------------------------------------------------------------------------------
-- Basic_796.lean
-- 演習問題 796〜810（fast-track 4：WRel の 0/1 化 / Rel↔WRel ブリッジ /
--                   wCountComp の計算規則）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 781〜795 は Basic_781 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_781

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wBool：WRel を 0/1 に潰す）
--------------------------------------------------------------------------------

-- WRel を “到達だけ残す” 0/1 行列に潰す（重みの大小は捨てて >0 だけ残す）
noncomputable def wBool (R : WRel α β) : WRel α β :=
  maskW (wSupp R)

--------------------------------------------------------------------------------
-- 796〜800：wBool と wCompList の到達（support）不変性
--------------------------------------------------------------------------------

-- 796：wBool は support を変えない
theorem ex796 (R : WRel α β) :
    wSupp (wBool R) = wSupp R := by
  -- ヒント：wBool の定義と ex613
  funext a1 b1
  dsimp [wBool, wSupp, maskW]
  by_cases h : R a1 b1 > 0

  -- pos
  rw [if_pos h]
  apply propext
  constructor
  intro h1
  exact h
  intro h2
  rw [gt_iff_lt]
  apply Nat.zero_lt_one

  -- neg
  rw [if_neg h]
  apply propext
  constructor
  intro h3
  contradiction
  intro h4
  contradiction

-- 797：wBool R ≤ R（0/1 化は元より小さい）
theorem ex797 (R : WRel α β) :
    WLe (wBool R) R := by
  -- ヒント：
  --   * dsimp [WLe, wBool, maskW]
  --   * by_cases h : R a b > 0（or R a b = 0）
  --   * Nat.pos_iff_ne_zero など
  dsimp [WLe, wBool, maskW, wSupp]
  intro a1 b1
  by_cases h : R a1 b1 > 0
  -- pos
  rw [if_pos h]
  apply Nat.pos_iff_ne_zero.mpr
  apply Nat.ne_of_gt
  rw [←gt_iff_lt]
  exact h
  -- neg
  rw [if_neg h]
  apply Nat.zero_le (R a1 b1)

-- 798：左を wBool に置き換えても wCompList の support は変わらない
theorem ex798 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys (wBool R) S) = wSupp (wCompList keys R S) := by
  -- ヒント：ex621 と ex796 を使う

  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)
  obtain hEx621 :=
    ex621 keys (wBool R) S
  dsimp [attnWRel] at hEx621
  rw [hEx621]
  clear hEx621

  -- theorem ex796 (R : WRel α β) :
  --     wSupp (wBool R) = wSupp R := by
  obtain hEx796 :=
    ex796 R
  rw [hEx796]
  clear hEx796

  rw [←ex621]
  dsimp [attnWRel]

-- 799：右を wBool に置き換えても wCompList の support は変わらない
theorem ex799 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys R (wBool S)) = wSupp (wCompList keys R S) := by

  -- ヒント：ex621 と ex796
  obtain hEx621 :=
    ex621 keys R (wBool S)
  dsimp [attnWRel] at hEx621
  rw [hEx621]
  clear hEx621

  obtain hEx796 :=
    ex796 S
  rw [hEx796]
  clear hEx796

  rw [←ex621]
  dsimp [attnWRel]

-- 800：両側を wBool にしても wCompList の support は変わらない
theorem ex800 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys (wBool R) (wBool S)) = wSupp (wCompList keys R S) := by
  -- ヒント：ex798 / ex799 からでも、ex621 + ex796 を 2 回でも

  -- theorem ex798 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wSupp (wCompList keys (wBool R) S) = wSupp (wCompList keys R S)

  obtain hEx798 :=
    ex798 keys R (wBool S)
  rw [hEx798]
  clear hEx798

  -- theorem ex799 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wSupp (wCompList keys R (wBool S)) = wSupp (wCompList keys R S)
  obtain hEx799 :=
    ex799 keys R S
  rw [hEx799]

--------------------------------------------------------------------------------
-- 801〜805：Rel と WRel のブリッジ（maskW / wMask / wCountComp）
--------------------------------------------------------------------------------

-- 801：0/1 行列 maskW M が R 以下であること ↔ M ⊆ support(R)
theorem ex801 (M : Rel α β) (R : WRel α β) :
    WLe (maskW M) R ↔ (M ⊆ wSupp R) := by
  -- ヒント：
  --   * dsimp [WLe, maskW, wSupp]
  --   * by_cases hM : M a b
  --   * Nat.pos_iff_ne_zero など
  dsimp [WLe, maskW, wSupp, RelLe]
  constructor

  -- mp
  intro h a1 b1 hM
  obtain h2 := h a1 b1
  rw [if_pos hM] at h2
  apply Nat.pos_iff_ne_zero.mpr
  apply Nat.ne_of_gt
  exact h2

  -- mpr
  intro h a1 b1
  obtain hM := h a1 b1
  by_cases hM2 : M a1 b1

  -- pos
  rw [if_pos hM2]
  obtain h3 := hM hM2
  exact h3

  -- neg
  rw [if_neg hM2]
  apply Nat.zero_le

-- 802：mask したものは必ず「mask の関係」を spec として満たす
theorem ex802 (R : WRel α β) (M : Rel α β) :
    WSpec (wMask R M) M := by
  -- ヒント：by classical; dsimp [WSpec, wMask, maskW]; by_cases (M a b); simp
  dsimp [WSpec, wMask, maskW]
  intro a1 b1 hM
  rw [if_neg hM]
  rw [Nat.mul_zero]

-- 803：mask の support は「元の support ∧ M」
theorem ex803 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) = relMul (wSupp R) M := by
  -- ヒント：by classical; funext a b; by_cases h : M a b <;>
  --   simp [wSupp, wMask, maskW, relMul, h]
  funext a1 b1
  dsimp [wSupp, wMask, maskW, relMul]
  by_cases h : M a1 b1
  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  apply propext
  constructor
  intro h1
  constructor
  exact h1
  exact h
  intro h2
  obtain ⟨hR, hM⟩ := h2
  exact hR
  rw [if_neg h]
  rw [Nat.mul_zero]
  apply propext
  constructor
  intro h3
  contradiction
  intro h4
  obtain ⟨hR, hM⟩ := h4
  contradiction

-- 804：0/1 化（wBool）は mask と可換
theorem ex804 (R : WRel α β) (M : Rel α β) :
    wBool (wMask R M) = wMask (wBool R) M := by
  -- ヒント：
  --   * wBool の定義：maskW (wSupp _)
  --   * ex803 で support(wMask) を relMul に
  --   * ex784（wMask (maskW A) B = maskW (A ∧ B)）があるならそれも使える
  funext a1 b1
  dsimp [wBool, wMask, maskW, wSupp]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  rw [Nat.mul_one]
  by_cases hR : R a1 b1 > 0
  rw [if_pos hR]
  rw [if_neg hR]
  rw [if_neg hM]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [if_neg]
  intro h2
  contradiction

-- 805：wCountComp の 0/1 化は relCompList（存在）に一致する
theorem ex805 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    wBool (wCountComp keys R S) = maskW (relCompList keys R S) := by
  -- ヒント：wBool の定義 → ex787（support(wCountComp)=relCompList）→ ex613
  funext a1 c1
  dsimp [wBool]
  -- theorem ex787 (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     wSupp (wCountComp keys R S) = relCompList keys R S := by
  obtain hEx787 :=
    ex787 keys R S
  rw [hEx787]

--------------------------------------------------------------------------------
-- 806〜810：wCountComp の計算規則（keys の分割 / singleton / 結合）
--------------------------------------------------------------------------------

-- 806：keys を append すると個数は足し算に分解できる
theorem ex806 (keys₁ keys₂ : List β) (R : Rel α β) (S : Rel β γ) :
    wCountComp (keys₁ ++ keys₂) R S
      =
    wAdd (wCountComp keys₁ R S) (wCountComp keys₂ R S) := by
  -- ヒント：
  --   * funext a c; dsimp [wCountComp, wCompList, wAdd]
  --   * ex536（wsum (xs++ys) = ...）
  funext a1 c1
  dsimp [wCountComp, wCompList, wAdd, wsum]
  obtain hEx536 :=
    ex536 keys₁ keys₂ (fun b => maskW R a1 b * maskW S b c1)
  rw [hEx536]

-- 807：空 keys の wCountComp は wZero
theorem ex807 (R : Rel α β) (S : Rel β γ) :
    wCountComp ([] : List β) R S = wZero α γ := by
  -- ヒント：ex721 か、dsimp [wCountComp, wCompList, wZero, wsum]
  dsimp [wCountComp]
  rw [ex721]

-- 808：singleton keys の wCountComp は 0/1（∧）そのもの
theorem ex808 (b : β) (R : Rel α β) (S : Rel β γ) :
    wCountComp [b] R S = maskW (fun a c => R a b ∧ S b c) := by
  -- ヒント：
  --   * dsimp [wCountComp]
  --   * ex722（wCompList [b] ...）
  --   * (if R then 1 else 0) * (if S then 1 else 0) の整理は ex786 の形
  dsimp [wCountComp]
  -- theorem ex722 (b : β) (R : WRel α β) (S : WRel β γ) :
  --     wCompList [b] R S = (fun a c => R a b * S b c) := by
  rw [ex722]
  funext a1 c1
  dsimp [maskW]
  by_cases hR : R a1 b
  rw [if_pos hR]
  by_cases hS : S b c1
  rw [if_pos hS]
  rw [if_pos ⟨hR, hS⟩]
  rw [if_neg hS]
  have hNeg : ¬ (R a1 b ∧ S b c1) := by
    intro h1
    obtain ⟨hR2, hS2⟩ := h1
    contradiction
  rw [if_neg hNeg]
  rw [if_neg hR]
  have hNeg2 : ¬ (R a1 b ∧ S b c1) := by
    intro h2
    obtain ⟨hR3, hS3⟩ := h2
    contradiction
  rw [if_neg hNeg2]
  rw [Nat.zero_mul]

-- 809：graph を左に置いた wCountComp は “行選択” の count 版になる（rowSum で観察）
theorem ex809 (keysb : List β) (keysg : List γ)
    (f : α → β) (S : Rel β γ) (a : α) :
    keysb.Nodup →
      wRowSum keysg (wCountComp keysb (relGraph f) S) a
        =
      (if f a ∈ keysb then wRowSum keysg (maskW S) (f a) else 0) := by
  -- ヒント：
  --   * wCountComp の定義で (maskW (relGraph f)) は wGraph f
  --   * ex795 を W := maskW S に適用
  dsimp [wCountComp]
  intro hNodup

  -- def relGraph (f : α → β) : Rel α β := fun a b => f a = b
  -- noncomputable def wGraph {α β : Type} (f : α → β) : WRel α β :=
  --   maskW (relGraph f)

  -- theorem ex795 (keys : List β) (keysg : List γ)
  --     (f : α → β) (W : WRel β γ) (a : α) :
  --     keys.Nodup →
  --       wRowSum keysg (wCompList keys (wGraph f) W) a
  --         =
  --       (if f a ∈ keys then wRowSum keysg W (f a) else 0) := by
  obtain hEx795 :=
    ex795 keysb keysg f (maskW S) a hNodup
  dsimp [wGraph] at hEx795
  rw [hEx795]

-- 810：wCountComp を 3 段にするとき、wCompList の結合則で “(b,g) の個数” を整理できる
theorem ex810 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    wCompList keysg (wCountComp keysβ R S) (maskW T)
      =
    wCompList keysβ (maskW R) (wCountComp keysg S T) := by
  -- ヒント：wCountComp を展開して ex780 を使うだけ
  funext a1 d1
  dsimp [wCountComp]
  -- theorem ex780 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
  --     wCompList keysg (wCompList keysβ R S) T
  --       =
  --     wCompList keysβ R (wCompList keysg S T) := by
  obtain hEx780 :=
    ex780
      keysβ keysg (maskW R) (maskW S) (maskW T)
  rw [hEx780]

end TL
