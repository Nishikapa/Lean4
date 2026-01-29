--------------------------------------------------------------------------------
-- Basic_781.lean
-- 演習問題 781〜795（fast-track 3：Rel を 0/1 テンソルとして扱う / count-semantics /
--                   graph による行選択の重み版）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 766〜780 は Basic_766 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_766

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wCountComp：Rel 合成の “件数” を数える WRel）
--------------------------------------------------------------------------------

-- keys 上で「中間 witness の個数」を数える合成（0/1 行列の積）
--   wCountComp keys R S a c = #{ b∈keys | R a b ∧ S b c }
-- （ただし keys に重複があると重複分も数える：wsum は List 上の和だから）
noncomputable def wCountComp (keys : List β) (R : Rel α β) (S : Rel β γ) : WRel α γ :=
  wCompList keys (maskW R) (maskW S)

--------------------------------------------------------------------------------
-- 781〜785：Rel を 0/1 テンソル（maskW）として見たときの基本対応
--------------------------------------------------------------------------------

-- 781：0/1 行列（maskW M）が spec T を満たす ↔ 元の関係が T に含まれる
-- （「仕様の外は 0」=「仕様の外は False」）
theorem ex781 (M T : Rel α β) :
    WSpec (maskW M) T ↔ (M ⊆ T) := by
  -- TODO
  -- ヒント：
  --   * ex691（WSpec ↔ wSupp ⊆ T）
  --   * ex613（wSupp (maskW M) = M）
  sorry

-- 782：0/1 行列同士の WLe は、元の関係の包含と同値
-- （0/1 なので「≤」は「1 なら右も 1」を意味する）
theorem ex782 (M N : Rel α β) :
    WLe (maskW M) (maskW N) ↔ (M ⊆ N) := by
  -- TODO
  -- ヒント：
  --   * dsimp [WLe, maskW]
  --   * by_cases (M a b), by_cases (N a b)
  --   * Nat.succ_le_succ_iff / Nat.not_succ_le_zero などでも可
  sorry

-- 783：0/1 行列の Hadamard 積は論理積（∧）に対応する（重みレベルで完全一致）
theorem ex783 (M N : Rel α β) :
    wMul (maskW M) (maskW N) = maskW (relMul M N) := by
  -- TODO
  -- ヒント：by classical; funext a b; by_cases hM : M a b <;> by_cases hN : N a b <;>
  --          simp [wMul, maskW, relMul, hM, hN]
  sorry

-- 784：0/1 行列を関係 N で mask するのは、関係の ∧ を取って 0/1 化するのと同じ
theorem ex784 (M N : Rel α β) :
    wMask (maskW M) N = maskW (relMul M N) := by
  -- TODO
  -- ヒント：
  --   * ex725（wMask R M = wMul R (maskW M)）
  --   * ex783 を使う
  sorry

-- 785：transpose は maskW と可換（関係側も transpose する）
theorem ex785 (M : Rel α β) :
    wTrans (maskW M) = maskW (relTrans M) := by
  -- TODO
  -- ヒント：by classical; funext b a; simp [wTrans, maskW, relTrans]
  sorry

--------------------------------------------------------------------------------
-- 786〜790：wCountComp（「witness の個数」）と relCompList（存在）
--------------------------------------------------------------------------------

-- 786：wCountComp の展開：積の 0/1 をまとめて ∧ の 0/1 にできる
--   (if M then 1 else 0) * (if N then 1 else 0) = if (M ∧ N) then 1 else 0
theorem ex786 (keys : List β) (R : Rel α β) (S : Rel β γ) (a : α) (c : γ) :
    wCountComp keys R S a c
      =
    wsum keys (fun b => if (R a b ∧ S b c) then 1 else 0) := by
  -- TODO
  -- ヒント：
  --   * dsimp [wCountComp, wCompList, maskW]
  --   * keys で帰納
  --   * 各 b で by_cases (R a b) と by_cases (S b c)
  --   * Nat.mul_one / Nat.mul_zero / Nat.zero_mul
  sorry

-- 787：support（>0）は「witness が存在する」だけを見るので relCompList に一致
-- （重みは “数” だが、>0 は “存在” に潰れる）
theorem ex787 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    wSupp (wCountComp keys R S) = relCompList keys R S := by
  -- TODO
  -- ヒント：
  --   * ex621（wSupp (wCompList keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)）
  --   * QK := maskW R, KV := maskW S
  --   * ex613（wSupp (maskW M) = M）
  sorry

-- 788：keys.Nodup かつ witness が高々 1 個なら、「個数」は 0/1 化（存在なら 1）
-- （“存在” と “個数” が一致する典型条件）
theorem ex788 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    keys.Nodup →
    (∀ a c b₁ b₂,
        b₁ ∈ keys → b₂ ∈ keys →
        R a b₁ → S b₁ c →
        R a b₂ → S b₂ c →
        b₁ = b₂) →
      wCountComp keys R S = maskW (relCompList keys R S) := by
  -- TODO
  -- ヒント：
  --   * funext a c
  --   * ex786 で wsum (if (R a b ∧ S b c) then 1 else 0) の形へ
  --   * keys.Nodup と “witness 一意性” から、true になる b は高々 1 個
  --   * ∃ があるなら wsum は 1、ないなら 0
  --   * RHS は maskW（= if ∃ witness then 1 else 0）
  sorry

-- 789：graph（左が関数）なら witness は自動的に一意 → wCountComp は 0/1 で “行選択”
-- （keys.Nodup で重複カウントが無い前提）
theorem ex789 (keys : List β) (f : α → β) (S : Rel β γ) :
    keys.Nodup →
      wCountComp keys (relGraph f) S
        =
      maskW (fun a c => f a ∈ keys ∧ S (f a) c) := by
  -- TODO
  -- ヒント：
  --   * ex788 を R:=relGraph f に適用（witness の一意性は自明）
  --   * relCompList keys (relGraph f) S a c は「∃b∈keys, f a = b ∧ S b c」
  --     なので b を f a に潰して (f a ∈ keys ∧ S (f a) c) に整理
  sorry

-- 790：graph-graph なら “関数合成 + keys マスク” の 0/1 版になる
theorem ex790 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
      wCountComp keys (relGraph f) (relGraph g)
        =
      maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  -- ヒント：
  --   * ex789 に S := relGraph g を入れる
  --   * relGraph g (f a) c は g (f a) = c
  sorry

--------------------------------------------------------------------------------
-- 791〜795：wCountComp を row/col-sum で観察（“2段 witness” と行選択）
--------------------------------------------------------------------------------

-- 791：rowSum>0（到達）が “b と c の 2段 witness” に分解できる（Rel 版）
theorem ex791 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (a : α) :
    wRowSum keysg (wCountComp keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ R a b ∧ S b c := by
  -- TODO
  -- ヒント：
  --   * ex710（rowSum>0 ↔ ∃c∈keysg, (..) a c >0）
  --   * (..) := wCountComp keysβ R S
  --   * ex787 で support を relCompList に落として、∃ の並べ替え
  sorry

-- 792：colSum>0（到達）が “a と b の 2段 witness” に分解できる（Rel 版）
theorem ex792 (keysα : List α) (keysβ : List β)
    (R : Rel α β) (S : Rel β γ) (c : γ) :
    wColSum keysα (wCountComp keysβ R S) c > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ a, a ∈ keysα ∧ R a b ∧ S b c := by
  -- TODO
  -- ヒント：
  --   * ex712（colSum>0 ↔ ∃a∈keysα, (..) a c >0）
  --   * ex787 で relCompList にして整理
  sorry

-- 793：rowSum を押し込む（Rel 版）：到達先 c を全て足すと “(b,c) の組の個数” を数える
--   Σ_c #{b | R a b ∧ S b c} = Σ_b ( [R a b] * Σ_c [S b c] )
theorem ex793 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (a : α) :
    wRowSum keysg (wCountComp keysβ R S) a
      =
    wsum keysβ (fun b => (if R a b then 1 else 0) * wRowSum keysg (maskW S) b) := by
  -- TODO
  -- ヒント：
  --   * ex751 を QK := maskW R, KV := maskW S に適用
  --   * wCountComp の定義へ戻す
  sorry

-- 794：colSum を押し込む（Rel 版）
theorem ex794 (keysα : List α) (keysβ : List β)
    (R : Rel α β) (S : Rel β γ) (c : γ) :
    wColSum keysα (wCountComp keysβ R S) c
      =
    wsum keysβ (fun b => wColSum keysα (maskW R) b * (if S b c then 1 else 0)) := by
  -- TODO
  -- ヒント：ex752 を QK := maskW R, KV := maskW S に適用して整理
  sorry

-- 795：graph を左に置くと “行選択” になる：rowSum も if で表せる（重み版）
theorem ex795 (keys : List β) (keysg : List γ)
    (f : α → β) (W : WRel β γ) (a : α) :
    keys.Nodup →
      wRowSum keysg (wCompList keys (wGraph f) W) a
        =
      (if f a ∈ keys then wRowSum keysg W (f a) else 0) := by
  -- TODO
  -- ヒント：
  --   * ex727（wCompList keys (wGraph f) W = wMask (fun a c => W (f a) c) (f a∈keys)）
  --   * それを wRowSum して、by_cases (f a ∈ keys)
  --   * true 側は mask が全部 1 なので wRowSum がそのまま
  --   * false 側は全項 0 → rowSum=0（ex711）
  sorry

end TL
