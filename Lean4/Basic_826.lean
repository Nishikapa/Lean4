--------------------------------------------------------------------------------
-- Basic_826.lean
-- 演習問題 826〜840（fast-track 6：wReachComp の代数 / 単調性 / identity / graph）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 811〜825 は Basic_811 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_811

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 826〜830：wReachComp の代数（keys / 単調性 / OR 分配 / 結合）
--------------------------------------------------------------------------------

-- 826：keys の単調性（候補が増えるほど reach も増える）
--   keys ⊆ keys' なら reach(keys) ≤ reach(keys')
--   ※ List なので ⊆ は「mem の包含」として書く
--
-- ヒント：ex817（wReachComp=maskW(relCompList ...)）
--        + ex655（relCompList の単調性：keys の包含）
--        + ex782（maskW の WLe ↔ 関係包含）
theorem ex826 (keys keys' : List β) (R : WRel α β) (S : WRel β γ) :
    (∀ b, b ∈ keys → b ∈ keys') →
      WLe (wReachComp keys R S) (wReachComp keys' R S) := by
  -- TODO
  sorry

-- 827：R/S の単調性（R≤R', S≤S' なら reach も ≤）
--
-- ヒント：ex615（WLe→support包含）→ ex656（relCompList の単調性）
--        → ex817 / ex782

theorem ex827 (keys : List β) (R R' : WRel α β) (S S' : WRel β γ) :
    WLe R R' → WLe S S' →
      WLe (wReachComp keys R S) (wReachComp keys R' S') := by
  -- TODO
  sorry

-- 828：左の wAdd（multi-head）に対する reach の分配（OR）
--
-- ヒント：ex817 → wSupp(wAdd)=relAdd（ex612）→ relCompList の分配（ex657）
theorem ex828 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    wReachComp keys (wAdd R R') S
      =
    maskW (relAdd (relCompList keys (wSupp R)  (wSupp S))
                  (relCompList keys (wSupp R') (wSupp S))) := by
  -- TODO
  sorry

-- 829：右の wAdd に対する reach の分配（OR）
--
-- ヒント：ex817 → wSupp(wAdd)=relAdd（ex612）→ relCompList の分配（ex658）
theorem ex829 (keys : List β) (R : WRel α β) (S S' : WRel β γ) :
    wReachComp keys R (wAdd S S')
      =
    maskW (relAdd (relCompList keys (wSupp R) (wSupp S))
                  (relCompList keys (wSupp R) (wSupp S'))) := by
  -- TODO
  sorry

-- 830：wReachComp の結合（keys を 2 段にしても同じ reach）
--
-- ヒント：ex817/ex818 で relCompList に落として ex659（関係の結合）を使う

theorem ex830 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wReachComp keysg (wReachComp keysβ R S) T
      =
    wReachComp keysβ R (wReachComp keysg S T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 831〜835：wId / wGraph と wReachComp（到達の “行選択/列選択”）
--------------------------------------------------------------------------------

-- 831：左に wId を置いた reach は「a∈keysα のときだけ行が生きる」
--
-- ヒント：ex817 + ex671（support(wId)=relId）で relCompList を簡約

theorem ex831 (keysα : List α) (R : WRel α γ) :
    wReachComp keysα (wId α) R
      =
    maskW (fun a c => a ∈ keysα ∧ wSupp R a c) := by
  -- TODO
  sorry

-- 832：右に wId を置いた reach は「b∈keysβ の列だけ残る」
--
-- ヒント：ex817 + ex671 で relCompList を簡約（witness が b になる）

theorem ex832 (keysβ : List β) (R : WRel α β) :
    wReachComp keysβ R (wId β)
      =
    maskW (fun a b => b ∈ keysβ ∧ wSupp R a b) := by
  -- TODO
  sorry

-- 833：左が graph なら witness は b=f a に潰れる（reach 版）
--
-- ヒント：ex817 + ex676（support(wGraph)=relGraph）で relCompList を簡約

theorem ex833 (keys : List β) (f : α → β) (S : WRel β γ) :
    wReachComp keys (wGraph f) S
      =
    maskW (fun a c => f a ∈ keys ∧ wSupp S (f a) c) := by
  -- TODO
  sorry

-- 834：右が graph なら「g b = c」で到達先が潰れる（reach 版）
--
-- ヒント：ex817 + ex676 で relCompList を展開して整理

theorem ex834 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    maskW (fun a c => ∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by
  -- TODO
  sorry

-- 835：graph-graph の reach は「関数合成 + keys マスク」
--
-- ヒント：ex833 に S:=wGraph g を入れて wSupp(wGraph g)=relGraph g を使う

theorem ex835 (keys : List β) (f : α → β) (g : β → γ) :
    wReachComp keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 836〜840：keys 条件を強めた簡約・特別ケース
--------------------------------------------------------------------------------

-- 836：keys が {f a} を全て含むなら、mask が消えて graph 合成そのもの（reach 版）
--
-- ヒント：ex835 の RHS を (∀a, f a∈keys) で簡約して wGraph にする

theorem ex836 (keys : List β) (f : α → β) (g : β → γ) :
    (∀ a : α, f a ∈ keys) →
      wReachComp keys (wGraph f) (wGraph g)
        =
      wGraph (fun a => g (f a)) := by
  -- TODO
  sorry

-- 837：wId-wId の reach（keys でフィルタされた恒等）
--
-- ヒント：ex817 + ex671 で relCompList を計算

theorem ex837 (keys : List α) :
    wReachComp keys (wId α) (wId α)
      =
    maskW (fun a a' => a = a' ∧ a ∈ keys) := by
  -- TODO
  sorry

-- 838：reach の spec は support⊆ で読める（wReachComp 版の ex691）
--
-- ヒント：ex691 + ex818（support(wReachComp)=relCompList ...）

theorem ex838 (keys : List β) (R : WRel α β) (S : WRel β γ) (T : Rel α γ) :
    WSpec (wReachComp keys R S) T ↔
      (relCompList keys (wSupp R) (wSupp S) ⊆ T) := by
  -- TODO
  sorry

-- 839：rowSum>0（reach 行和）は “2段 witness” (b と c) に分解できる
--
-- ヒント：ex820（rowSum>0 不変）＋ ex779（wCompList の 2段 witness）

theorem ex839 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    wRowSum keysg (wReachComp keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ wSupp R a b ∧ wSupp S b c := by
  -- TODO
  sorry

-- 840：colSum>0（reach 列和）も “2段 witness” (a と b) に分解できる
--
-- ヒント：ex821（colSum>0 不変）→ ex754（b まで）→ ex712（a まで）

theorem ex840 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c : γ) :
    wColSum keysα (wReachComp keysβ R S) c > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ a, a ∈ keysα ∧ wSupp R a b ∧ wSupp S b c := by
  -- TODO
  sorry

end TL
