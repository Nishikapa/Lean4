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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

-- 756：t>0 のとき、スカラー倍の spec は元と同値
theorem ex756 (t : Nat) (R : WRel α β) (T : Rel α β) :
    t > 0 → (WSpec (wScale t R) T ↔ WSpec R T) := by
  -- TODO
  -- ヒント：
  --   * dsimp [WSpec, wScale]
  --   * (→) : “t * R a b = 0” から R a b = 0 を取り出す（t>0 なので Nat.mul_eq_zero で）
  --   * (←) : R a b = 0 なら t * R a b = 0
  sorry

-- 757：transpose の spec は定義展開だけで ↔ が出る
theorem ex757 (R : WRel α β) (T : Rel α β) :
    WSpec (wTrans R) (relTrans T) ↔ WSpec R T := by
  -- TODO
  -- ヒント：dsimp [WSpec, wTrans, relTrans] で全部同じ形になる
  sorry

-- 758：spec を満たす R は、自分の spec でマスクしても変わらない
theorem ex758 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wMask R T = R := by
  -- TODO
  -- ヒント：
  --   by classical; funext a b; by_cases h : T a b <;> simp [WSpec, wMask, maskW, h]
  sorry

-- 759：spec を満たすなら support は T との ∧ で不変（support = support ∧ T）
theorem ex759 (R : WRel α β) (T : Rel α β) :
    WSpec R T → wSupp R = relMul (wSupp R) T := by
  -- TODO
  -- ヒント：
  --   funext a b; apply propext; constructor
  --   * (→) : hSupp から ⟨hSupp, (T a b)⟩ を作る（T でないと spec と矛盾）
  --   * (←) : ∧ の左射影
  sorry

-- 760：wId は “relId の外は 0” の spec を満たす
theorem ex760 :
    WSpec (wId α) (relId α) := by
  -- TODO
  -- ヒント：by classical; intro a b hnot; simp [WSpec, wId, wMask, maskW, relId] at *
  sorry

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
  sorry

-- 762：keys.Nodup なら、wGraph の rowSum も 0/1（f a ∈ keys なら 1、それ以外は 0）
theorem ex762 (keys : List β) (f : α → β) (a : α) :
    keys.Nodup →
      wRowSum keys (wGraph f) a = (if f a ∈ keys then 1 else 0) := by
  -- TODO
  -- ヒント：ex761 とほぼ同じ（wGraph の定義を展開すると “if f a = b then 1 else 0”）
  sorry

-- 763：keys で rowSum を取るなら、右側 “b∈keys” マスクは消せる
theorem ex763 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys (wMask R (relInKeys (α:=α) keys)) a = wRowSum keys R a := by
  -- TODO
  -- ヒント：
  --   * dsimp [wRowSum]
  --   * ex601（wsum ext）か keys での帰納法
  --   * b∈keys のとき relInKeys は True なので maskW=1
  sorry

-- 764：keys で colSum を取るなら、左側 “a∈keys” マスクは消せる
theorem ex764 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys (wMask R (fun a _ => a ∈ keys)) b = wColSum keys R b := by
  -- TODO
  -- ヒント：ex763 の colSum 版（keys で帰納するのが楽）
  sorry

-- 765：spec を満たす R なら、rowSum は keys を T でフィルタしたのと同じ（重み 0 なので落ちる）
theorem ex765 (keys : List β) (R : WRel α β) (T : Rel α β) (a : α) :
    WSpec R T →
      wRowSum keys R a
        =
      wRowSum keys (wMask R T) a := by
  -- TODO
  -- ヒント：ex758（wMask R T = R）を使って終わり
  sorry

end TL
