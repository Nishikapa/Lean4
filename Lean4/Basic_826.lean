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

  intro h1
  dsimp [wReachComp]

  -- theorem ex782 (M N : Rel α β) :
  --     WLe (maskW M) (maskW N) ↔ (M ⊆ N) := by
  obtain hEx782 :=
    ex782 (relCompList keys (wSupp R) (wSupp S)) (relCompList keys' (wSupp R) (wSupp S))
  rw [hEx782]
  clear hEx782

  -- theorem ex655 (keys keys' : List β) (R : Rel α β) (S : Rel β γ) :
  --     (∀ b, b ∈ keys → b ∈ keys') →
  --       relCompList keys R S ⊆ relCompList keys' R S := by
  obtain hEx655 :=
     ex655 keys keys' (wSupp R) (wSupp S) h1

  apply hEx655

-- 827：R/S の単調性（R≤R', S≤S' なら reach も ≤）
--
-- ヒント：ex615（WLe→support包含）→ ex656（relCompList の単調性）
--        → ex817 / ex782

theorem ex827 (keys : List β) (R R' : WRel α β) (S S' : WRel β γ) :
    WLe R R' → WLe S S' →
      WLe (wReachComp keys R S) (wReachComp keys R' S') := by

  -- theorem ex615 (R S : WRel α β) :
  --     WLe R S → (wSupp R ⊆ wSupp S) := by
  obtain hEx615_1 :=
    ex615 R R'
  obtain hEx615_2 :=
    ex615 S S'
  intro h1 h2
  obtain hSupp1 := hEx615_1 h1
  obtain hSupp2 := hEx615_2 h2

  -- theorem ex656 (keys : List β) (R R' : Rel α β) (S S' : Rel β γ) :
  --     (R ⊆ R') → (S ⊆ S') →
  --       relCompList keys R S ⊆ relCompList keys R' S' := by
  obtain hEx656 :=
    ex656 keys (wSupp R) (wSupp R') (wSupp S) (wSupp S') hSupp1 hSupp2
  clear hEx615_1 hEx615_2 hSupp1 hSupp2

  -- theorem ex782 (M N : Rel α β) :
  --     WLe (maskW M) (maskW N) ↔ (M ⊆ N) := by
  rw [←ex782] at hEx656
  dsimp [wReachComp]
  apply hEx656

-- 828：左の wAdd（multi-head）に対する reach の分配（OR）
--
-- ヒント：ex817 → wSupp(wAdd)=relAdd（ex612）→ relCompList の分配（ex657）
theorem ex828 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    wReachComp keys (wAdd R R') S
      =
    maskW (relAdd (relCompList keys (wSupp R)  (wSupp S))
                  (relCompList keys (wSupp R') (wSupp S))) := by

  -- theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wBool (wCompList keys R S) = wReachComp keys R S
  obtain hEx817 :=
    ex817 keys (wAdd R R') S
  rw [←hEx817]
  clear hEx817

  -- theorem ex657 (keys : List β) (R R' : Rel α β) (S : Rel β γ) :
  --     relCompList keys (relAdd R R') S
  --       =
  --     relAdd (relCompList keys R S) (relCompList keys R' S) := by
  obtain hEx657 :=
    ex657 keys (wSupp R) (wSupp R') (wSupp S)
  rw [←hEx657]
  clear hEx657

  -- theorem ex612 (R S : WRel α β) :
  --     wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S) := by
  obtain hEx612 :=
    ex612 R R'
  rw [←hEx612]
  clear hEx612
  dsimp [wBool]
  funext a1 c1
  dsimp [maskW, wSupp, wCompList, wAdd, relCompList]
  induction keys with
  | nil =>
    dsimp [wsum]
    rw [if_neg]
    rw [if_neg]
    intro h1
    obtain ⟨b1,hContains,h2,h3⟩ := h1
    contradiction
    intro h4
    contradiction
  | cons b1 keysTail ih =>
    dsimp [wsum]

    have h5 : ((wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0) ↔ (∃ b, b ∈ keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0) := by
      --by_cases h5_1 : (wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0
      constructor
      intro h5_1
      rw [if_pos h5_1] at ih
      by_cases h5_2 : ∃ b, b ∈ keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0
      exact h5_2
      rw [if_neg h5_2] at ih
      contradiction
      intro h5_3
      rw [if_pos h5_3] at ih
      by_cases h5_4 : (wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0
      rw [if_pos h5_4] at ih
      exact h5_4
      rw [if_neg h5_4] at ih
      contradiction

    clear ih

    by_cases h6 : ((R a1 b1 + R' a1 b1) * S b1 c1 + wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0
    -- pos
    rw [if_pos h6]
    rw [gt_iff_lt] at h6
    rw [Nat.add_pos_iff_pos_or_pos] at h6
    obtain h6_1 | h6_2 := h6
    obtain h6_3 := Nat.pos_of_mul_pos_left h6_1
    obtain h6_4 := Nat.pos_of_mul_pos_right h6_1
    clear h6_1

    have h7 : ∃ b, b ∈ b1 :: keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0 := by
      exists b1
      constructor
      apply List.mem_cons_self
      constructor
      exact h6_4
      exact h6_3
    rw [if_pos h7]
    rw [←gt_iff_lt] at h6_2
    rw [h5] at h6_2
    clear h5
    obtain ⟨b2,hContains,hRSumPos,hSPos⟩ := h6_2
    have h8 : ∃ b, b ∈ b1 :: keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0 := by
      exists b2
      constructor
      apply List.mem_cons_of_mem
      exact hContains
      constructor
      exact hRSumPos
      exact hSPos
    rw [if_pos h8]

    -- neg
    rw [if_neg h6]

    have h9 : ¬(∃ b, b ∈ b1 :: keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0) := by
      intro h9_1
      obtain ⟨b2,hContains,hRSumPos,hSPos⟩ := h9_1
      apply h6
      rw [gt_iff_lt]
      rw [Nat.add_pos_iff_pos_or_pos]
      by_cases h10 : b2 = b1
      left
      apply Nat.mul_pos
      rw [←gt_iff_lt]
      rw [←h10]
      exact hRSumPos
      rw [←gt_iff_lt]
      rw [←h10]
      exact hSPos
      obtain h11 :=
        List.mem_of_ne_of_mem h10 hContains

      have h12 : ∃ b, b ∈ keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0 := by
        exists b2

      rw [←h5] at h12

      right
      exact h12
    rw [if_neg h9]

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
