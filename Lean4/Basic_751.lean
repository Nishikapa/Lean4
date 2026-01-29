--------------------------------------------------------------------------------
-- Basic_751.lean
-- 演習問題 751〜765（fast-track：row/col-sum と wCompList の関係 / WSpec の計算規則の強化）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 701〜750 は Basic_701 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_701

namespace TL

-- NOTE:
-- ex761/ex762 のステートメント中に `if a ∈ keys then ...` が出てくるため、
-- `Decidable (a ∈ keys)` が必要です。
-- Lean4 では Lean3 の `local attribute ...` 構文は使えないので、
-- `attribute [local instance] ...` で Prop の決定可能性をローカルに入れます。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 751〜754：row/col-sum と wCompList（「行和・列和を押し込む」）
--------------------------------------------------------------------------------

theorem wsum_comm {X Y : Type} (xs : List X) (ys : List Y) (f : X → Y → Nat) :
    wsum xs (fun x => wsum ys (fun y => f x y))
      =
    wsum ys (fun y => wsum xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    dsimp [wsum]
    symm
    rw [ex607]
    intro y hy
    rfl
  | cons x1 xs_tail ih =>
    dsimp [wsum]
    rw [ex537]
    rw [ih]


-- 751：rowSum を wCompList の内側へ押し込む（有限版 Fubini）
--   Σ_{c∈keysg} (Σ_{b∈keysβ} R a b * S b c)
-- = Σ_{b∈keysβ} R a b * (Σ_{c∈keysg} S b c)
theorem ex751 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    wRowSum keysg (wCompList keysβ R S) a
      =
    wsum keysβ (fun b => R a b * wRowSum keysg S b) := by
  -- TODO
  -- ヒント：
  --   * dsimp [wRowSum, wCompList] で展開
  --   * keysg で帰納法（head/tail）
  --   * 途中で必要になる「wsum は点ごとの + に分配する」補題は、その場で keysβ で帰納して作る

  dsimp [wRowSum, wCompList]

  conv =>
    rhs
    arg 2
    intro b
    rw [ex539 keysg (fun b_1 => S b b_1) (R a b)]

  rw [wsum_comm]

-- 752：colSum を wCompList の内側へ押し込む（有限版 Fubini）
theorem ex752 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c : γ) :
    wColSum keysα (wCompList keysβ R S) c
      =
    wsum keysβ (fun b => wColSum keysα R b * S b c) := by
  -- TODO
  -- ヒント：
  --   * dsimp [wColSum, wCompList] で展開
  --   * keysα で帰納法（head/tail）
  --   * 途中で必要になる「wsum は点ごとの + に分配する」補題は、その場で keysβ で帰納して作る
  dsimp [wColSum, wCompList]
  conv =>
    rhs
    arg 2
    intro b
    rw [ex538]

  rw [wsum_comm]

-- 753：rowSum>0 の条件（2段の witness に分解）
theorem ex753 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    wRowSum keysg (wCompList keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ R a b > 0 ∧ wRowSum keysg S b > 0 := by
  -- TODO
  -- ヒント：
  --   * ex751 で書き換え
  --   * ex606（wsum>0 ↔ ∃ mem ∧ 項>0）を xs:=keysβ, f:=fun b => R a b * wRowSum keysg S b に
  --   * ex608（積>0 ↔ 両方>0）で分解

  -- theorem ex751 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (a : α) :
  --     wRowSum keysg (wCompList keysβ R S) a
  --       =
  --     wsum keysβ (fun b => R a b * wRowSum keysg S b) := by
  rw [ex751]

  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  rw [ex606]

  -- theorem ex608 (m n : Nat) :
  --     (m * n > 0) ↔ (m > 0 ∧ n > 0) := by
  constructor

  -- mp
  intro hExists1
  obtain ⟨b1, hb_in, hb_pos⟩ := hExists1
  rw [ex608] at hb_pos
  exists b1

  -- mpr
  intro hExists2
  obtain ⟨b2, hContains1, h1⟩ := hExists2
  exists b2
  constructor
  exact hContains1
  rw [ex608]
  exact h1

-- 754：colSum>0 の条件（2段の witness に分解）
theorem ex754 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c : γ) :
    wColSum keysα (wCompList keysβ R S) c > 0
      ↔
    ∃ b, b ∈ keysβ ∧ wColSum keysα R b > 0 ∧ S b c > 0 := by
  -- TODO
  -- ヒント：
  --   * ex752 で書き換え
  --   * ex606 と ex608 を使う（項は (wColSum keysα R b * S b c)）

  -- theorem ex752 (keysα : List α) (keysβ : List β)
  --     (R : WRel α β) (S : WRel β γ) (c : γ) :
  --     wColSum keysα (wCompList keysβ R S) c
  --       =
  --     wsum keysβ (fun b => wColSum keysα R b * S b c)
  rw [ex752]

  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  rw [ex606]

  constructor

  -- mp
  intro hExists1
  obtain ⟨b1, hb_in, hb_pos⟩ := hExists1
  exists b1
  constructor
  exact hb_in
  rw [ex608] at hb_pos
  exact hb_pos

  -- mpr
  intro hExists2
  obtain ⟨b2, hContains1, h1⟩ := hExists2
  exists b2
  constructor
  exact hContains1
  rw [ex608]
  exact h1

--------------------------------------------------------------------------------
-- 755〜760：WSpec の “計算規則” を強化（↔ にする・マスク簡約など）
--------------------------------------------------------------------------------

-- 755：同じ spec をもつ 2 つを足したら、その spec は “ちょうど” 両方の spec（↔）
theorem ex755 (R S : WRel α β) (T : Rel α β) :
    WSpec (wAdd R S) T ↔ (WSpec R T ∧ WSpec S T) := by
  -- TODO
  -- ヒント：
  --   * dsimp [WSpec, wAdd]
  --   * Nat.add_eq_zero_iff を使うと “=0” が両方 “=0” に分解できる
  dsimp [WSpec, wAdd]
  constructor

  -- mp
  intro hSpec
  constructor
  intro a1 b1 hT
  obtain hSpec1 := hSpec a1 b1 hT
  rw [Nat.add_eq_zero_iff] at hSpec1
  obtain ⟨hR_zero, hS_zero⟩ := hSpec1
  exact hR_zero
  intro a2 b2 hT2
  obtain hSpec2 := hSpec a2 b2 hT2
  rw [Nat.add_eq_zero_iff] at hSpec2
  obtain ⟨hR2_zero, hS2_zero⟩ := hSpec2
  exact hS2_zero

  -- mpr
  intro hSpecs
  obtain ⟨hSpecR, hSpecS⟩ := hSpecs
  intro a3 b3 hT3
  rw [Nat.add_eq_zero_iff]
  constructor
  obtain hSpecR1 := hSpecR a3 b3 hT3
  exact hSpecR1
  obtain hSpecS1 := hSpecS a3 b3 hT3
  exact hSpecS1

-- 756：t>0 のとき、スカラー倍の spec は元と同値
theorem ex756 (t : Nat) (R : WRel α β) (T : Rel α β) :
    t > 0 → (WSpec (wScale t R) T ↔ WSpec R T) := by
  -- TODO
  -- ヒント：
  --   * dsimp [WSpec, wScale]
  --   * (→) : “t * R a b = 0” から R a b = 0 を取り出す（t>0 なので Nat.mul_eq_zero で）
  --   * (←) : R a b = 0 なら t * R a b = 0
  intro hT_pos
  obtain hT_not_zero :=
    Nat.pos_iff_ne_zero.mp hT_pos
  dsimp [WSpec, wScale]
  constructor

  -- mp
  intro hSpec1
  intro a1 b1 hT1
  obtain hSpecR1 := hSpec1 a1 b1 hT1
  rw [Nat.mul_eq_zero] at hSpecR1
  obtain h1 | h2 := hSpecR1
  contradiction
  exact h2

  -- mpr
  intro hSpec2
  intro a2 b2 hT2
  obtain hSpecR2 := hSpec2 a2 b2 hT2
  rw [hSpecR2]
  rw [Nat.mul_zero]

-- 757：transpose の spec は定義展開だけで ↔ が出る
theorem ex757 (R : WRel α β) (T : Rel α β) :
    WSpec (wTrans R) (relTrans T) ↔ WSpec R T := by
  -- TODO
  -- ヒント：dsimp [WSpec, wTrans, relTrans] で全部同じ形になる
  dsimp [WSpec, wTrans, relTrans]
  constructor
  -- mp
  intro hSpec1
  intro a1 b1 hT1
  obtain hSpecR1 := hSpec1 b1 a1 hT1
  exact hSpecR1
  -- mpr
  intro hSpec2
  intro a2 b2 hT2
  obtain hSpecR2 := hSpec2 b2 a2 hT2
  exact hSpecR2

-- 758：spec を満たす R は、自分の spec でマスクしても変わらない
theorem ex758 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wMask R T = R := by
  -- TODO
  -- ヒント：
  --   by classical; funext a b; by_cases h : T a b <;> simp [WSpec, wMask, maskW, h]
  intro hSpec
  funext a1 b1
  dsimp [wMask, maskW]
  dsimp [WSpec] at hSpec
  obtain hSpec1 := hSpec a1 b1
  by_cases hT : T a1 b1
  rw [if_pos hT]
  rw [Nat.mul_one]
  rw [if_neg hT]
  obtain hSpecR1 := hSpec1 hT
  rw [hSpecR1]

-- 759：spec を満たすなら support は T との ∧ で不変（support = support ∧ T）
theorem ex759 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wSupp R = relMul (wSupp R) T := by
  -- TODO
  -- ヒント：
  --   funext a b; apply propext; constructor
  --   * (→) : hSupp から ⟨hSupp, (T a b)⟩ を作る（T でないと spec と矛盾）
  --   * (←) : ∧ の左射影
  intro hSpec
  dsimp [WSpec] at hSpec
  funext a1 b1
  obtain hSpec1 := hSpec a1 b1
  dsimp [wSupp, relMul]
  apply propext
  constructor

  -- mp
  intro hSupp1
  obtain hSupp2 := Nat.ne_of_gt hSupp1
  constructor
  exact hSupp1
  by_cases hT : T a1 b1
  exact hT
  obtain hSpecR1 := hSpec1 hT
  contradiction

  -- mpr
  intro hAnd
  obtain ⟨hSupp2, hT2⟩ := hAnd
  exact hSupp2

-- 760：wId は “relId の外は 0” の spec を満たす
theorem ex760 :
    WSpec (wId α) (relId α) := by
  -- ヒント：by classical; intro a b hnot; simp [WSpec, wId, wMask, maskW, relId] at *
  intro a1 b1 hNotId
  dsimp [WSpec, wId, relId] at hNotId
  dsimp [wId, wMask, maskW, relId]
  rw [if_neg hNotId]

--------------------------------------------------------------------------------
-- 761〜765：0/1 行列（wId / wGraph）と row/col-sum の相性（Nodup 前提で 0/1 になる）
--------------------------------------------------------------------------------

-- 761：keys.Nodup なら、wId の rowSum は 0/1（a ∈ keys なら 1、それ以外は 0）
theorem ex761 (keys : List α) (a : α) :
    keys.Nodup →
      wRowSum keys (wId α) a = (if a ∈ keys then 1 else 0) := by
  -- TODO
  -- ヒント：
  --   * keys で帰納法
  --   * Nodup の cons 展開（List.nodup_cons）と mem_cons を使う
  --   * if と等式は by_cases で分ける
  intro hNodup
  dsimp [wRowSum, wId, maskW, wMask, relId]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons k1 ks ks_ih =>
    dsimp [wsum]
    rw [List.nodup_cons] at hNodup
    obtain ⟨hK1_notin, hKs_nodup⟩ := hNodup
    by_cases hMem : a = k1

    -- case: a = k1
    rw [if_pos hMem]
    rw [hMem]
    rw [if_pos List.mem_cons_self]
    rw [Nat.add_comm]
    rw [Nat.add_one_inj]
    rw [←hMem]
    rw [hMem] at ks_ih
    rw [if_neg hK1_notin] at ks_ih
    rw [←hMem] at ks_ih
    apply ks_ih
    exact hKs_nodup

    -- case: a ≠ k1
    rw [if_neg hMem]
    rw [Nat.zero_add]
    by_cases hIn : a ∈ ks
    obtain hIn2 :=
      List.mem_cons_of_mem k1 hIn
    rw [if_pos hIn2]
    rw [if_pos hIn] at ks_ih
    apply ks_ih
    exact hKs_nodup
    obtain hNotIn2 :=
      List.not_mem_cons_of_ne_of_not_mem hMem hIn
    rw [if_neg hNotIn2]
    rw [if_neg hIn] at ks_ih
    apply ks_ih
    exact hKs_nodup

-- 762：keys.Nodup なら、wGraph の rowSum も 0/1（f a ∈ keys なら 1、それ以外は 0）
theorem ex762 (keys : List β) (f : α → β) (a : α) :
    keys.Nodup →
      wRowSum keys (wGraph f) a = (if f a ∈ keys then 1 else 0) := by
  -- ヒント：ex761 とほぼ同じ（wGraph の定義を展開すると “if f a = b then 1 else 0”）
  intro hNodup
  dsimp [wRowSum, wGraph, maskW, wMask, relGraph]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons k1 ks ks_ih =>
    rw [List.nodup_cons] at hNodup
    obtain ⟨hK1_notin, hKs_nodup⟩ := hNodup
    dsimp [wsum]
    by_cases hEqFaK1 : f a = k1
    rw [if_pos hEqFaK1]
    rw [hEqFaK1]
    rw [if_pos List.mem_cons_self]
    rw [Nat.add_comm]
    rw [Nat.add_one_inj]
    rw [hEqFaK1] at ks_ih
    -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
    --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
    obtain hEx607 :=
      ex607 ks (fun b => if k1 = b then 1 else 0)
    rw [hEx607]
    intro b hb_in
    by_cases hEqK1B : k1 = b
    rw [←hEqK1B] at hb_in
    contradiction
    rw [if_neg hEqK1B]
    rw [if_neg hEqFaK1]
    rw [Nat.zero_add]
    by_cases hIn : f a ∈ ks
    obtain hIn2 :=
      List.mem_cons_of_mem k1 hIn
    rw [if_pos hIn2]
    rw [if_pos hIn] at ks_ih
    apply ks_ih
    exact hKs_nodup
    rw [if_neg hIn] at ks_ih
    obtain hNotIn2 :=
      List.not_mem_cons_of_ne_of_not_mem hEqFaK1 hIn
    rw [if_neg hNotIn2]
    apply ks_ih
    exact hKs_nodup

-- 763：keys で rowSum を取るなら、右側 “b∈keys” マスクは消せる
theorem ex763 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys (wMask R (relInKeys (α:=α) keys)) a = wRowSum keys R a := by
  -- ヒント：
  --   * dsimp [wRowSum]
  --   * ex601（wsum ext）か keys での帰納法
  --   * b∈keys のとき relInKeys は True なので maskW=1
  dsimp [wRowSum, wMask, maskW, relInKeys]
  apply ex601
  intro b1 hb_in
  rw [if_pos hb_in]
  rw [Nat.mul_one]

-- 764：keys で colSum を取るなら、左側 “a∈keys” マスクは消せる
theorem ex764 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys (wMask R (fun a _ => a ∈ keys)) b = wColSum keys R b := by
  -- ヒント：ex763 の colSum 版（keys で帰納するのが楽）
  dsimp [wColSum, wMask, maskW]
  apply ex601
  intro a1 ha_in
  rw [if_pos ha_in]
  rw [Nat.mul_one]

-- 765：spec を満たす R なら、rowSum は keys を T でフィルタしたのと同じ（重み 0 なので落ちる）
theorem ex765 (keys : List β) (R : WRel α β) (T : Rel α β) (a : α) :
    WSpec R T →
      wRowSum keys R a
        =
      wRowSum keys (wMask R T) a := by
  -- TODO
  -- ヒント：ex758（wMask R T = R）を使って終わり
  intro hSpec
  obtain hEx758 := ex758 R T hSpec
  rw [hEx758]

end TL
