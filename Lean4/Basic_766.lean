--------------------------------------------------------------------------------
-- Basic_766.lean
-- 演習問題 766〜780（fast-track 2：col-sum の 0/1 化 / wCompList の結合則 /
--                   WSpec による keys-filtering）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 751〜765 は Basic_751 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_751

namespace TL

-- NOTE:
-- `if a ∈ keys then ...` や `decide (∃ ...)` を使うため、Prop の決定可能性が必要です。
-- Lean4 では Lean3 の `local attribute ...` は使えないので、
-- `attribute [local instance] ...` を使います。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 766〜770：col-sum の 0/1 化（wId / wGraph）
--------------------------------------------------------------------------------

-- 766：keys.Nodup なら、wId の colSum も 0/1（a ∈ keys なら 1、それ以外は 0）
theorem ex766 (keys : List α) (a : α) :
    keys.Nodup →
      wColSum keys (wId α) a = (if a ∈ keys then 1 else 0) := by
  -- TODO
  -- ヒント：
  --   * ex761（rowSum 版）＋ ex709（transposeで row/col 入替）を使うのが楽
  --   * あるいは keys で帰納して ex761 と同型に解いてもよい
  sorry

-- 767：wGraph の colSum>0 ↔ ∃ a∈keys, f a = b
theorem ex767 (keys : List α) (f : α → β) (b : β) :
    wColSum keys (wGraph f) b > 0
      ↔
    ∃ a, a ∈ keys ∧ f a = b := by
  -- TODO
  -- ヒント：ex712 を R := wGraph f に適用し、wGraph の定義を展開
  sorry

-- 768：keys.Nodup かつ keys 上で f が単射なら、wGraph の colSum は 0/1
theorem ex768 (keys : List α) (f : α → β) (b : β) :
    keys.Nodup →
    (∀ a₁ a₂, a₁ ∈ keys → a₂ ∈ keys → f a₁ = f a₂ → a₁ = a₂) →
      wColSum keys (wGraph f) b
        =
      (if (∃ a, a ∈ keys ∧ f a = b) then 1 else 0) := by
  -- TODO
  -- ヒント：
  --   * keys で帰納
  --   * 「∃a∈(x::xs), ...」の分解（head と tail）
  --   * 単射仮定で「同じ b に当たる a が 2 個は無い」を作る
  --   * 最後は Nat の計算（0/1）に帰着
  sorry

-- 769：keys.Nodup かつ keys が α 全体を含むなら、wId の rowSum は常に 1
theorem ex769 (keys : List α) (a : α) :
    keys.Nodup →
    (∀ x : α, x ∈ keys) →
      wRowSum keys (wId α) a = 1 := by
  -- TODO
  -- ヒント：ex761 で (if a∈keys then 1 else 0) にして if_pos
  sorry

-- 770：keys.Nodup かつ keys が {f a} を全て含むなら、wGraph の rowSum は常に 1
theorem ex770 (keys : List β) (f : α → β) (a : α) :
    keys.Nodup →
    (∀ x : α, f x ∈ keys) →
      wRowSum keys (wGraph f) a = 1 := by
  -- TODO
  -- ヒント：ex762 で if にして if_pos
  sorry

--------------------------------------------------------------------------------
-- 771〜775：wId と wCompList を row/col-sum で観察する
--------------------------------------------------------------------------------

-- 771：左に wId を置く縮約は「a∈keysα のときだけ行が生きる」→ rowSum も if で表せる
theorem ex771 (keysα : List α) (keysg : List γ) (R : WRel α γ) (a : α) :
    wRowSum keysg (wCompList keysα (wId α) R) a
      =
    (if a ∈ keysα then wRowSum keysg R a else 0) := by
  -- TODO
  -- ヒント：
  --   * ex672 で wCompList keysα (wId α) R を wMask に落とす
  --   * その後 by_cases (a∈keysα) で場合分け
  --   * false 側は「全項 0」→ rowSum=0（ex711 など）
  sorry

-- 772：右に wId を置く縮約は「b∈keys の列だけ残る」→ 同じ keys で rowSum を取るなら元と同じ
theorem ex772 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys (wCompList keys R (wId β)) a = wRowSum keys R a := by
  -- TODO
  -- ヒント：
  --   * ex673 で wMask R (relInKeys keys)
  --   * ex763 で「keys で rowSum を取るならその mask は消える」
  sorry

-- 773：左に wId を置く縮約も「同じ keys で colSum を取るなら元と同じ」
theorem ex773 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys (wCompList keys (wId α) R) b = wColSum keys R b := by
  -- TODO
  -- ヒント：
  --   * ex672 で wMask R (fun a _ => a∈keys)
  --   * ex764 で「keys で colSum を取るならその mask は消える」
  sorry

-- 774：S の各行の rowSum（keysg で見たもの）が keysβ 上で全部 0 なら、合成の rowSum も 0
theorem ex774 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    (∀ b, b ∈ keysβ → wRowSum keysg S b = 0) →
      wRowSum keysg (wCompList keysβ R S) a = 0 := by
  -- TODO
  -- ヒント：
  --   * ex751 で wRowSum を押し込む
  --   * ex711（wsum=0 ↔ 全項=0）を使って各項を 0 にする（Nat.mul_zero）
  sorry

-- 775：R の各列の colSum（keysα で見たもの）が keysβ 上で全部 0 なら、合成の colSum も 0
theorem ex775 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c : γ) :
    (∀ b, b ∈ keysβ → wColSum keysα R b = 0) →
      wColSum keysα (wCompList keysβ R S) c = 0 := by
  -- TODO
  -- ヒント：
  --   * ex752 で wColSum を押し込む
  --   * ex711 / ex713 系（wsum=0 ↔ 全項=0）＋ Nat.zero_mul
  sorry

--------------------------------------------------------------------------------
-- 776〜779：WSpec による keys-filtering（「spec の外は落としてよい」）
--------------------------------------------------------------------------------

-- 776：WSpec を満たすなら、rowSum は keys を T(a,·) で filter しても同じ
theorem ex776 (keys : List β) (R : WRel α β) (T : Rel α β) (a : α) :
    WSpec R T →
      wRowSum keys R a
        =
      wRowSum (keys.filter (fun b => decide (T a b))) R a := by
  -- TODO
  -- ヒント：
  --   * keys で帰納
  --   * head で T a b の真偽により filter が b を残すか落とすか分かれる
  --   * ¬T a b の場合は WSpec で R a b = 0 に落ちる
  sorry

-- 777：WSpec を満たすなら、colSum も keys を T(·,b) で filter して同じ
theorem ex777 (keys : List α) (R : WRel α β) (T : Rel α β) (b : β) :
    WSpec R T →
      wColSum keys R b
        =
      wColSum (keys.filter (fun a => decide (T a b))) R b := by
  -- TODO
  -- ヒント：ex776 の colSum 版（keys で帰納が楽）
  sorry

-- 778：入力/出力が spec を持つなら、合成も relCompList-spec を持つ → 出力 keys を filter してよい
theorem ex778 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : Rel α β) (U : Rel β γ) (a : α) :
    WSpec R T → WSpec S U →
      wRowSum keysg (wCompList keysβ R S) a
        =
      wRowSum (keysg.filter (fun c => decide (relCompList keysβ T U a c)))
              (wCompList keysβ R S) a := by
  -- TODO
  -- ヒント：
  --   * ex746 で WSpec (wCompList ...) (relCompList ...)
  --   * それを ex776 に投入（R := wCompList ... , T := relCompList ...）
  sorry

-- 779：rowSum>0 を “2段 witness” (b と c) まで分解する（より具体的な到達条件）
theorem ex779 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    wRowSum keysg (wCompList keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ R a b > 0 ∧ S b c > 0 := by
  -- TODO
  -- ヒント：
  --   * ex753 で b まで出す
  --   * wRowSum keysg S b > 0 を ex710 で c まで出す
  --   * ∃ の並べ替えを整理
  sorry

--------------------------------------------------------------------------------
-- 780：wCompList の結合則（2段 witness の “重みレベル” 版）
--------------------------------------------------------------------------------

-- 780：wCompList の結合（Σ の並べ替え・分配の重み版）
theorem ex780 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wCompList keysg (wCompList keysβ R S) T
      =
    wCompList keysβ R (wCompList keysg S T) := by
  -- TODO
  -- ヒント：
  --   * funext a d; dsimp [wCompList]
  --   * keysg で帰納（外側の wsum）
  --   * 途中で必要になる：
  --       (wsum keysβ f) * k = wsum keysβ (fun b => f b * k)
  --     のような補題（keysβ で帰納してその場で作る）
  --   * Nat.mul_add / Nat.add_assoc / Nat.mul_assoc / Nat.mul_left_comm など
  sorry

end TL
