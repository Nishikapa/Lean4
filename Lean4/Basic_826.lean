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

    have h5 :
      ((wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0) ↔
      (∃ b, b ∈ keysTail ∧ R a1 b + R' a1 b > 0 ∧ S b c1 > 0) := by
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

    by_cases h6 :
      ((R a1 b1 + R' a1 b1) * S b1 c1 + wsum keysTail fun b => (R a1 b + R' a1 b) * S b c1) > 0
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

  -- theorem ex658 (keys : List β) (R : Rel α β) (S S' : Rel β γ) :
  --     relCompList keys R (relAdd S S')
  --       =
  --     relAdd (relCompList keys R S) (relCompList keys R S') := by
  obtain hEx658 :=
    ex658 keys (wSupp R) (wSupp S) (wSupp S')

  rw [←hEx658]
  clear hEx658

  -- wReachComp keys R (wAdd S S') =
  -- maskW (relCompList keys (wSupp R) (relAdd (wSupp S) (wSupp S')))

  -- theorem ex612 (R S : WRel α β) :
  --     wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S) := by
  obtain hEx612 :=
    ex612 S S'

  rw [←hEx612]
  clear hEx612

  -- wReachComp keys R (wAdd S S') =
  -- maskW (relCompList keys (wSupp R) (wSupp (wAdd S S')))

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- noncomputable def wBool (R : WRel α β) : WRel α β :=
  --   maskW (wSupp R)

  -- theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wBool (wCompList keys R S) = wReachComp keys R S := by
  obtain hEx817 :=
    ex817 keys R (wAdd S S')

  rw [←hEx817]
  clear hEx817

  -- wBool (wCompList keys R (wAdd S S')) =
  -- maskW (relCompList keys (wSupp R) (wSupp (wAdd S S')))

  dsimp [wBool]
  funext a1 c1
  dsimp [maskW, wSupp, wCompList, wAdd, relCompList]
  induction keys with
  | nil =>
    dsimp [wsum]
    rw [if_neg]
    have h1 : ¬(∃ b, b ∈ [] ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0) := by
      intro h1_1
      obtain ⟨b1,hContains,hRPos,hSPos⟩ := h1_1
      contradiction
    rw [if_neg h1]
    intro h2
    contradiction
  | cons b1 keysTail ih =>
    dsimp [wsum]

    have h3 : (wsum keysTail fun b => R a1 b * (S b c1 + S' b c1)) > 0 ↔
      (∃ b, b ∈ keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0 ) := by
      constructor
      intro h3_1
      rw [if_pos h3_1] at ih
      by_cases h3_2 : ∃ b, b ∈ keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0
      exact h3_2
      rw [if_neg h3_2] at ih
      contradiction
      intro h3_3
      rw [if_pos h3_3] at ih
      by_cases h3_4 : (wsum keysTail fun b => R a1 b * (S b c1 + S' b c1)) > 0
      exact h3_4
      rw [if_neg h3_4] at ih
      contradiction
    clear ih

    by_cases h4 : (wsum keysTail fun b => R a1 b * (S b c1 + S' b c1)) > 0
    -- pos
    obtain ⟨b2, hContains1, h5_3, h5_4⟩ := h3.mp h4

    have h6 : (R a1 b1 * (S b1 c1 + S' b1 c1) + wsum keysTail fun b => R a1 b * (S b c1 + S' b c1)) > 0 := by
      rw [gt_iff_lt]
      rw [Nat.add_pos_iff_pos_or_pos]
      right
      exact h4

    rw [if_pos h6]

    have h7 : ∃ b, b ∈ b1 :: keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0 := by
      exists b2
      constructor
      apply List.mem_cons_of_mem
      exact hContains1
      constructor
      exact h5_3
      exact h5_4

    rw [if_pos h7]

    -- neg
    have h8 : ¬(∃ b, b ∈ keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0) := by
      intro h8_1
      obtain ⟨b2, hContains1, h5_3, h5_4⟩ := h8_1
      apply h4
      rw [h3]
      exists b2

    by_cases h9 : (R a1 b1 * (S b1 c1 + S' b1 c1) + wsum keysTail fun b => R a1 b * (S b c1 + S' b c1)) > 0

    rw [if_pos h9]

    obtain h11 :=  Nat.eq_zero_of_not_pos h4
    clear h4

    rw [h11] at h9
    rw [Nat.add_zero] at h9
    obtain h12 := Nat.pos_of_mul_pos_left h9
    obtain h13 := Nat.pos_of_mul_pos_right h9
    clear h9

    have h10 : ∃ b, b ∈ b1 :: keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0 := by
      exists b1
      constructor
      apply List.mem_cons_self
      constructor
      exact h13
      exact h12
    rw [if_pos h10]

    obtain ⟨h14, h15⟩ := Nat.add_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h9)
    clear h9
    rw [h14]
    rw [h15]
    rw [Nat.zero_add]
    rw [if_neg]
    rw [Nat.mul_eq_zero] at h14

    have h16 : ¬ ∃ b, b ∈ b1 :: keysTail ∧ R a1 b > 0 ∧ S b c1 + S' b c1 > 0 := by
      intro h16_1
      obtain ⟨b2, hContains1, h5_3, h5_4⟩ := h16_1
      apply h8
      exists b2
      constructor
      by_cases h17 : b2 = b1
      rw [gt_iff_lt] at h5_3
      rw [Nat.pos_iff_ne_zero] at h5_3
      rw [gt_iff_lt] at h5_4
      rw [Nat.pos_iff_ne_zero] at h5_4
      rw [h17] at h5_3
      rw [h17] at h5_4
      obtain h14_1| h14_2 := h14
      contradiction
      contradiction
      obtain h18 :=
        List.mem_of_ne_of_mem h17 hContains1
      exact h18
      constructor
      exact h5_3
      exact h5_4
    rw [if_neg h16]
    intro h19
    contradiction

-- 830：wReachComp の結合（keys を 2 段にしても同じ reach）
--
-- ヒント：ex817/ex818 で relCompList に落として ex659（関係の結合）を使う

theorem ex830 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wReachComp keysg (wReachComp keysβ R S) T
      =
    wReachComp keysβ R (wReachComp keysg S T) := by

  dsimp [wReachComp]
  funext a1 d1
  dsimp [maskW, relCompList, wSupp]
  by_cases h1 :
    (∃ b, b ∈ keysg ∧ (if ∃ b_1, b_1 ∈ keysβ ∧ R a1 b_1 > 0 ∧ S b_1 b > 0 then 1 else 0) > 0 ∧ T b d1 > 0)
  obtain ⟨g1, hContains1, h1_2, h1_3⟩ := h1
  have h1_4 : ∃ b_1, b_1 ∈ keysβ ∧ R a1 b_1 > 0 ∧ S b_1 g1 > 0 := by
    by_cases h1_4_1 : ∃ b_1, b_1 ∈ keysβ ∧ R a1 b_1 > 0 ∧ S b_1 g1 > 0
    exact h1_4_1
    rw [if_neg h1_4_1] at h1_2
    contradiction
  clear h1_2
  obtain ⟨b1, hContains2, h1_5, h1_6⟩ := h1_4
  by_cases h2 :
    (∃ b_1, b_1 ∈ keysβ ∧ R a1 b_1 > 0 ∧ S b_1 g1 > 0)
  obtain ⟨b2, hContains3, h2_2, h2_3⟩ := h2
  rw [if_pos]
  rw [if_pos]
  exists b2
  constructor
  exact hContains3
  constructor
  exact h2_2
  rw [if_pos]
  apply Nat.zero_lt_one
  exists g1
  exists g1
  constructor
  exact hContains1
  constructor
  by_cases h3 : ∃ b, b ∈ keysβ ∧ R a1 b > 0 ∧ S b g1 > 0
  rw [if_pos h3]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  rw [if_neg h3]
  apply False.elim
  apply h3
  exists b2
  exact h1_3
  rw [if_pos]
  rw [if_pos]
  exists b1
  constructor
  exact hContains2
  constructor
  exact h1_5
  rw [if_pos]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  exists g1
  exists g1
  constructor
  exact hContains1
  constructor
  rw [if_pos]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  exists b1
  exact h1_3
  rw [if_neg]
  rw [if_neg]
  intro h5
  obtain ⟨b3, hContains5, h5_2, h5_3⟩ := h5
  have h5_4 : ∃ b, b ∈ keysg ∧ S b3 b > 0 ∧ T b d1 > 0 := by
    by_cases h5_4_1 : ∃ b, b ∈ keysg ∧ S b3 b > 0 ∧ T b d1 > 0
    exact h5_4_1
    rw [if_neg h5_4_1] at h5_3
    contradiction
  obtain ⟨g2, hContains6, h5_5, h5_6⟩ := h5_4
  clear h5_3
  apply h1
  exists g2
  constructor
  exact hContains6
  constructor
  rw [if_pos]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  exists b3
  exact h5_6
  intro h6
  obtain ⟨g3, hContains6, h6_2, h6_3⟩ := h6
  apply h1
  exists g3
  constructor
  exact hContains6
  constructor
  by_cases h7 : ∃ b, b ∈ keysβ ∧ R a1 b > 0 ∧ S b g3 > 0
  rw [if_pos h7]
  rw [gt_iff_lt]
  apply Nat.zero_lt_one
  rw [if_neg h7]
  rw [if_neg h7] at h6_2
  contradiction
  exact h6_3

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

  funext a1 c1
  dsimp [wReachComp, maskW, wSupp, wId, relCompList]

  by_cases h1 : (∃ b, b ∈ keysα ∧ (if b = a1 then 1 else 0) > 0 ∧ R b c1 > 0)
  obtain ⟨a2, hContains, h1_2, h1_3⟩ := h1
  have h2 : a2 = a1 := by
    by_cases h2_1 : a2 = a1
    exact h2_1
    rw [if_neg] at h1_2
    contradiction
    intro h2_2
    apply h2_1
    rw [h2_2]
  clear h1_2
  rw [h2] at hContains
  rw [h2] at h1_3
  rw [if_pos]
  rw [if_pos]
  constructor
  exact hContains
  exact h1_3
  exists a2
  constructor
  rw [h2]
  exact hContains
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [relId]
  rw [h2]
  rw [h2]
  exact h1_3
  rw [if_neg]
  rw [if_neg]
  intro h4
  obtain ⟨hContains2, h4_2⟩ := h4
  apply h1
  exists a1
  constructor
  exact hContains2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  exact h4_2
  intro h5
  obtain ⟨a3, hContains3, h5_2, h5_3⟩ := h5
  apply h1
  exists a3
  constructor
  exact hContains3
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [relId] at h5_2
  have h5_4 : a1 = a3 := by
    by_cases h5_4_1 : a1 = a3
    exact h5_4_1
    rw [if_neg] at h5_2
    contradiction
    exact h5_4_1
  clear h5_2
  rw [h5_4]
  exact h5_3

-- 832：右に wId を置いた reach は「b∈keysβ の列だけ残る」
--
-- ヒント：ex817 + ex671 で relCompList を簡約（witness が b になる）

theorem ex832 (keysβ : List β) (R : WRel α β) :
    wReachComp keysβ R (wId β)
      =
    maskW (fun a b => b ∈ keysβ ∧ wSupp R a b) := by
  funext a1 b1
  dsimp [wReachComp, maskW, wSupp, wId, relCompList, relId]
  by_cases h1 : ∃ b, b ∈ keysβ ∧ R a1 b > 0 ∧ (if b = b1 then 1 else 0) > 0
  obtain ⟨b2, hContains, h1_2, h1_3⟩ := h1
  have h1_4 : b2 = b1 := by
    by_cases h1_4_1 : b2 = b1
    exact h1_4_1
    rw [if_neg h1_4_1] at h1_3
    contradiction
  clear h1_3
  rw [if_pos]
  rw [h1_4] at hContains
  rw [h1_4] at h1_2
  rw [if_pos]
  constructor
  exact hContains
  exact h1_2
  exists b2
  constructor
  exact hContains
  constructor
  exact h1_2
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [h1_4]
  rw [if_neg]
  rw [if_neg]
  intro h4
  obtain ⟨hContains2, h4_2⟩ := h4
  apply h1
  exists b1
  constructor
  exact hContains2
  constructor
  exact h4_2
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  intro h5
  obtain ⟨b3, hContains3, h5_2, h5_3⟩ := h5
  apply h1
  exists b3

-- 833：左が graph なら witness は b=f a に潰れる（reach 版）
--
-- ヒント：ex817 + ex676（support(wGraph)=relGraph）で relCompList を簡約

theorem ex833 (keys : List β) (f : α → β) (S : WRel β γ) :
    wReachComp keys (wGraph f) S
      =
    maskW (fun a c => f a ∈ keys ∧ wSupp S (f a) c) := by
  funext a1 c1
  dsimp [wReachComp, maskW, wSupp, wGraph, relCompList, relGraph]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ S b c1 > 0
  obtain ⟨b1, hContains, h1_2, h1_3⟩ := h1
  have h2 : b1 = f a1 := by
    by_cases h2_1 : b1 = f a1
    exact h2_1
    rw [if_neg] at h1_2
    contradiction
    intro h2_2
    apply h2_1
    rw [h2_2]
  clear h1_2
  rw [if_pos]
  rw [if_pos]
  rw [h2] at hContains
  rw [h2] at h1_3
  constructor
  exact hContains
  exact h1_3
  exists b1
  constructor
  exact hContains
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [h2]
  exact h1_3
  rw [if_neg]
  rw [if_neg]
  intro h4
  obtain ⟨hContains2, h4_2⟩ := h4
  apply h1
  exists (f a1)
  constructor
  exact hContains2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  exact h4_2
  intro h5
  obtain ⟨b2, hContains3, h5_2, h5_3⟩ := h5
  apply h1
  exists b2

-- 834：右が graph なら「g b = c」で到達先が潰れる（reach 版）
--
-- ヒント：ex817 + ex676 で relCompList を展開して整理

theorem ex834 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    maskW (fun a c => ∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by
  funext a1 c1
  dsimp [wReachComp, maskW, wSupp, wGraph, relCompList, relGraph]
  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if g b = c1 then 1 else 0) > 0
  obtain ⟨b1, hContains, h1_2, h1_3⟩ := h1
  have h2 : g b1 = c1 := by
    by_cases h2_1 : g b1 = c1
    exact h2_1
    rw [if_neg h2_1] at h1_3
    contradiction
  clear h1_3
  rw [if_pos]
  rw [if_pos]
  exists b1
  exists b1
  constructor
  exact hContains
  constructor
  exact h1_2
  rw [if_pos h2]
  apply Nat.zero_lt_one
  rw [if_neg]
  rw [if_neg]
  intro h4
  obtain ⟨b2, hContains2, h4_2, h4_3⟩ := h4
  apply h1
  exists b2
  constructor
  exact hContains2
  constructor
  exact h4_2
  rw [if_pos h4_3]
  apply Nat.zero_lt_one
  intro h5
  obtain ⟨b3, hContains3, h5_2, h5_3⟩ := h5
  apply h1
  exists b3

-- 835：graph-graph の reach は「関数合成 + keys マスク」
--
-- ヒント：ex833 に S:=wGraph g を入れて wSupp(wGraph g)=relGraph g を使う

theorem ex835 (keys : List β) (f : α → β) (g : β → γ) :
    wReachComp keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  funext a1 c1
  dsimp [wReachComp, maskW, wSupp, wGraph, relCompList, relGraph]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ (if g b = c1 then 1 else 0) > 0
  obtain ⟨b1, hContains, h1_2, h1_3⟩ := h1
  have h2 : b1 = f a1 := by
    by_cases h2_1 : b1 = f a1
    exact h2_1
    rw [if_neg] at h1_2
    contradiction
    intro h2_2
    apply h2_1
    rw [h2_2]
  clear h1_2
  have h3: g b1 = c1 := by
    by_cases h3_1 : g b1 = c1
    exact h3_1
    rw [if_neg] at h1_3
    contradiction
    intro h3_2
    apply h3_1
    rw [h3_2]
  clear h1_3
  rw [if_pos]
  rw [if_pos]
  rw [←h2]
  constructor
  exact hContains
  rw [←h3]
  exists b1
  constructor
  exact hContains
  rw [if_pos]
  rw [if_pos]
  constructor
  apply Nat.zero_lt_one
  apply Nat.zero_lt_one
  exact h3
  rw [h2]
  rw [if_neg]
  rw [if_neg]
  intro h5
  obtain ⟨hContains2, h5_2⟩ := h5
  apply h1
  exists (f a1)
  constructor
  exact hContains2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [h5_2]
  intro h6
  obtain ⟨b2, hContains3, h6_2, h6_3⟩ := h6
  apply h1
  have h6_4 : b2 = f a1 := by
    by_cases h6_4_1 : b2 = f a1
    exact h6_4_1
    rw [if_neg] at h6_2
    contradiction
    intro h6_4_2
    apply h6_4_1
    rw [h6_4_2]
  clear h6_2
  have h6_5 : g b2 = c1 := by
    by_cases h6_5_1 : g b2 = c1
    exact h6_5_1
    rw [if_neg] at h6_3
    contradiction
    intro h6_5_2
    apply h6_5_1
    rw [h6_5_2]
  clear h6_3
  exists b2
  rw [←h6_4]
  rw [h6_5]
  constructor
  exact hContains3
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

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
  intro hAll
  funext a1 c1
  dsimp [wReachComp, wGraph, maskW, wSupp, relCompList, relGraph]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ (if g b = c1 then 1 else 0) > 0
  obtain ⟨b1, hContains, h1_2, h1_3⟩ := h1
  have h1_4 : b1 = f a1 := by
    by_cases h2_1 : b1 = f a1
    exact h2_1
    rw [if_neg] at h1_2
    contradiction
    intro h2_2
    apply h2_1
    rw [h2_2]
  clear h1_2
  have h1_5 : g b1 = c1 := by
    by_cases h3_1 : g b1 = c1
    exact h3_1
    rw [if_neg] at h1_3
    contradiction
    intro h3_2
    apply h3_1
    rw [h3_2]
  clear h1_3
  rw [if_pos]
  rw [if_pos]
  rw [←h1_4]
  rw [←h1_5]
  exists b1
  constructor
  exact hContains
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [h1_4]
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [h1_5]
  rw [if_neg]
  rw [if_neg]
  intro h5
  obtain ⟨hContains2, h5_2⟩ := h5
  apply h1
  obtain h2 := hAll a1
  exists (f a1)
  constructor
  exact h2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  intro h6
  obtain ⟨b2, hContains3, h6_2, h6_3⟩ := h6
  apply h1
  have h6_4 : b2 = f a1 := by
    by_cases h6_4_1 : b2 = f a1
    exact h6_4_1
    rw [if_neg] at h6_2
    contradiction
    intro h6_4_2
    apply h6_4_1
    rw [h6_4_2]
  clear h6_2
  have h6_5 : g b2 = c1 := by
    by_cases h6_5_1 : g b2 = c1
    exact h6_5_1
    rw [if_neg] at h6_3
    contradiction
    intro h6_5_2
    apply h6_5_1
    rw [h6_5_2]
  clear h6_3
  exists b2
  rw [←h6_4]
  rw [h6_5]
  constructor
  exact hContains3
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

-- 837：wId-wId の reach（keys でフィルタされた恒等）
--
-- ヒント：ex817 + ex671 で relCompList を計算

theorem ex837 (keys : List α) :
    wReachComp keys (wId α) (wId α)
      =
    maskW (fun a a' => a = a' ∧ a ∈ keys) := by
  funext a1 a2
  dsimp [wReachComp, wId, maskW, wSupp, relCompList, relId]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if a1 = b then 1 else 0) > 0 ∧ (if b = a2 then 1 else 0) > 0
  obtain ⟨b1, hContains, h1_2, h1_3⟩ := h1
  have h1_4 : b1 = a1 := by
    by_cases h2_1 : b1 = a1
    exact h2_1
    rw [if_neg] at h1_2
    contradiction
    intro h2_2
    apply h2_1
    rw [h2_2]
  clear h1_2
  have h1_5 : b1 = a2 := by
    by_cases h3_1 : b1 = a2
    exact h3_1
    rw [if_neg] at h1_3
    contradiction
    intro h3_2
    apply h3_1
    rw [h3_2]
  clear h1_3
  rw [if_pos]
  rw [if_pos]
  rw [←h1_4]
  rw [←h1_5]
  constructor
  rfl
  exact hContains
  rw [←h1_4]
  rw [←h1_5]
  exists b1
  constructor
  exact hContains
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_neg]
  rw [if_neg]
  intro h5
  obtain ⟨hContains2, h5_2⟩ := h5
  apply h1
  rw [←hContains2]
  exists a1
  constructor
  exact h5_2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  intro h6
  obtain ⟨b2, hContains3, h6_2, h6_3⟩ := h6
  apply h1
  have h6_4 : b2 = a1 := by
    by_cases h6_4_1 : b2 = a1
    exact h6_4_1
    rw [if_neg] at h6_2
    contradiction
    intro h6_4_2
    apply h6_4_1
    rw [h6_4_2]
  clear h6_2
  have h6_5 : b2 = a2 := by
    by_cases h6_5_1 : b2 = a2
    exact h6_5_1
    rw [if_neg] at h6_3
    contradiction
    intro h6_5_2
    apply h6_5_1
    rw [h6_5_2]
  clear h6_3
  rw [←h6_4]
  rw [←h6_5]
  exists b2
  constructor
  exact hContains3
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

-- 838：reach の spec は support⊆ で読める（wReachComp 版の ex691）
--
-- ヒント：ex691 + ex818（support(wReachComp)=relCompList ...）

theorem ex838 (keys : List β) (R : WRel α β) (S : WRel β γ) (T : Rel α γ) :
    WSpec (wReachComp keys R S) T ↔
      (relCompList keys (wSupp R) (wSupp S) ⊆ T) := by
  dsimp [WSpec, wReachComp, wSupp, relCompList, maskW]
  constructor
  intro h1
  intro a1 c1 h2
  obtain h1_2 := h1 a1 c1
  clear h1
  obtain ⟨b1, h2_2, h2_3, h2_4⟩ := h2
  dsimp [wSupp] at *
  have h2 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0 := by
    exists b1
  by_cases h3 : T a1 c1
  exact h3
  obtain h1_3 := h1_2 h3
  have h1_4 : ¬ (∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0) := by
    by_cases h1_4_1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
    rw [if_pos h1_4_1] at h1_3
    contradiction
    exact h1_4_1
  clear h1_2 h1_3
  contradiction
  intro h4
  dsimp [RelLe, relCompList, wSupp] at h4
  intro a1 c1 h5
  rw [if_neg]
  intro h6
  apply h5
  apply h4
  exact h6

-- 839：rowSum>0（reach 行和）は “2段 witness” (b と c) に分解できる
--
-- ヒント：ex820（rowSum>0 不変）＋ ex779（wCompList の 2段 witness）

theorem ex839 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a1 : α) :
    wRowSum keysg (wReachComp keysβ R S) a1 > 0
      ↔
    ∃ b1, b1 ∈ keysβ ∧ ∃ c1, c1 ∈ keysg ∧ wSupp R a1 b1 ∧ wSupp S b1 c1 := by

  -- theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wBool (wCompList keys R S) = wReachComp keys R S
  obtain hEx817
   := ex817 keysβ R S
  rw [←hEx817]
  clear hEx817

  -- theorem ex820 (keys : List β) (R : WRel α β) (a : α) :
  --     (wRowSum keys (wBool R) a > 0) ↔ (wRowSum keys R a > 0)
  --      wRowSum keysg (wBool (wCompList keysβ R S)) a1 > 0
  obtain hEx820
   := ex820 keysg (wCompList keysβ R S) a1
  rw [hEx820]
  clear hEx820

-- theorem ex779 (keysβ : List β) (keysg : List γ)
--     (R : WRel α β) (S : WRel β γ) (a : α) :
--     wRowSum keysg (wCompList keysβ R S) a > 0
--       ↔
--     ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ R a b > 0 ∧ S b c > 0

-- wRowSum keysg (wCompList keysβ R S) a1 > 0
  obtain hEx779
   := ex779 keysβ keysg R S a1
  rw [hEx779]
  clear hEx779

  constructor
  intro h1
  obtain ⟨b1, hContains1, g1, hContains2, h1_3, h1_4⟩ := h1
  exists b1
  constructor
  exact hContains1
  exists g1
  intro h2
  obtain ⟨b2, hContains2, g2, ⟨h2_4, h2_5, h2_6⟩⟩ := h2
  exists b2
  constructor
  exact hContains2
  exists g2

-- 840：colSum>0（reach 列和）も “2段 witness” (a と b) に分解できる
--
-- ヒント：ex821（colSum>0 不変）→ ex754（b まで）→ ex712（a まで）

theorem ex840 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c1 : γ) :
    wColSum keysα (wReachComp keysβ R S) c1 > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ a, a ∈ keysα ∧ wSupp R a b ∧ wSupp S b c1 := by

  -- theorem ex817 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wBool (wCompList keys R S) = wReachComp keys R S
  obtain hEx817
   := ex817 keysβ R S
  rw [←hEx817]
  clear hEx817

  -- theorem ex821 (keys : List α) (R : WRel α β) (b : β) :
  --     (wColSum keys (wBool R) b > 0) ↔ (wColSum keys R b > 0) := by
  obtain hEx821
   := ex821 keysα (wCompList keysβ R S) c1
  rw [hEx821]
  clear hEx821

  -- theorem ex754 (keysα : List α) (keysβ : List β)
  --     (R : WRel α β) (S : WRel β γ) (c : γ) :
  --     wColSum keysα (wCompList keysβ R S) c > 0
  --       ↔
  --     ∃ b, b ∈ keysβ ∧ wColSum keysα R b > 0 ∧ S b c > 0 := by
  obtain hEx754
   := ex754 keysα keysβ R S c1
  rw [hEx754]
  clear hEx754

  -- theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
  --     wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0 := by
  conv =>
    lhs
    arg 1
    ext b
    rhs
    lhs
    rw [ex712 keysα R b]

  constructor
  intro h1
  obtain ⟨b1, hContains1, h1_3, h1_4⟩ := h1
  obtain ⟨a1, hContains2, h1_5⟩ := h1_3
  exists b1
  constructor
  exact hContains1
  exists a1
  intro h2
  obtain ⟨b2, hContains2, a2, hContains3, h2_5, h2_6⟩ := h2
  dsimp [wSupp] at *
  exists b2
  constructor
  exact hContains2
  constructor
  exists a2
  exact h2_6

end TL
