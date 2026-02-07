--------------------------------------------------------------------------------
-- Basic_856.lean
-- 演習問題 856〜870（fast-track 8：wsumW の代数 / wReachComp への分配 / 計算規則）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 841〜855 は Basic_841 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_841

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε ι : Type}

--------------------------------------------------------------------------------
-- 856〜860：wsumW の基本性質（固定点 / 単調性 / ext）
--------------------------------------------------------------------------------

-- 856：wsumW は 0/1 行列なので wBool の固定点
-- （wBool をもう一度かけても変わらない）
theorem ex856 (keys : List ι) (F : ι → WRel α γ) :
    wBool (wsumW keys F)
      =
    wsumW keys F := by
  -- ヒント：wsumW の定義と ex811（wBool idempotent）
  funext a1 c1
  dsimp [wsumW]
  -- theorem ex811 (R : WRel α β) :
  --     wBool (wBool R) = wBool R := by
  obtain hEx811 :=
    ex811 fun a c => wsum keys fun b => F b a c
  rw [hEx811]

-- 857：i ∈ keys なら、その項（の 0/1 化）は wsumW 以下
-- （“OR-和” は各項を含む）
theorem ex857 (keys : List ι) (F : ι → WRel α γ) (i : ι) :
    i ∈ keys →
      WLe (wBool (F i)) (wsumW keys F) := by
  -- ヒント：support で示す（ex615 / ex846）

  intro h1
  dsimp [WLe]
  dsimp [wsumW]
  intro a1 c1
  dsimp [wBool, wSupp, maskW]

  by_cases h2 : F i a1 c1 > 0
  rw [if_pos h2]

  induction keys with
  | nil =>
    dsimp [wsum]
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum]
    by_cases h3 : i = b1
    rw [←h3]
    rw [if_pos]
    apply Nat.zero_lt_succ
    rw [gt_iff_lt]
    apply Nat.add_pos_iff_pos_or_pos.mpr
    left
    exact h2
    obtain h4 := List.mem_of_ne_of_mem h3 h1
    obtain ih2 := ih h4
    have h5 : (wsum bs fun b => F b a1 c1) > 0 := by
      by_cases h5_1 : (wsum bs fun b => F b a1 c1) > 0
      exact h5_1
      rw [if_neg h5_1] at ih2
      contradiction
    rw [if_pos]
    apply Nat.le_refl
    apply Nat.add_pos_iff_pos_or_pos.mpr
    right
    exact h5
  rw [if_neg]
  apply Nat.zero_le
  exact h2

-- 858：keys の単調性（候補が増えるほど OR-和も増える）
theorem ex858 (keys keys' : List ι) (F : ι → WRel α γ) :
    (∀ i, i ∈ keys → i ∈ keys') →
      WLe (wsumW keys F)
          (wsumW keys' F) := by
  -- ヒント：ex846 の ∃ 形で support の包含を示す
  intro h1 a1 g1
  dsimp [wsumW, wBool, maskW, wSupp]
  by_cases h2 : (wsum keys fun b => F b a1 g1) > 0
  rw [if_pos h2]
  rw [if_pos]
  apply Nat.le_refl
  obtain hEx601_1 :=
    ex606 keys (fun b => F b a1 g1)
  obtain hEx601_2 :=
    ex606 keys' (fun b => F b a1 g1)
  rw [hEx601_1] at h2
  rw [hEx601_2]
  clear hEx601_1 hEx601_2
  obtain ⟨i1, h3, h4⟩ := h2
  exists i1
  obtain h2 := h1 i1
  constructor
  apply h2
  exact h3
  exact h4
  rw [if_neg]
  apply Nat.zero_le
  exact h2

-- 859：wsumW の ext（keys 上で項が一致すれば wsumW も一致）
theorem ex859 (keys : List ι) (F G : ι → WRel α γ) :
    (∀ i, i ∈ keys → F i = G i) →
      wsumW keys F
        =
      wsumW keys G := by
  -- ヒント：funext a c; wsum の項ごとの一致（keys で帰納）
  intro h1
  funext a1 c1
  dsimp [wsumW]
  dsimp [wBool, maskW, wSupp]

  obtain hEx601_1 :=
    ex606 keys (fun b => F b a1 c1)
  obtain hEx601_2 :=
    ex606 keys (fun b => G b a1 c1)
  rw [hEx601_1, hEx601_2]
  clear hEx601_1 hEx601_2

  by_cases h2 : ∃ x, x ∈ keys ∧ F x a1 c1 > 0
  rw [if_pos]
  obtain ⟨i1, h3, h4⟩ := h2
  rw [if_pos]
  exists i1
  constructor
  exact h3
  obtain h5 := h1 i1 h3
  rw [←h5]
  exact h4
  exact h2
  rw [if_neg]
  rw [if_neg]
  intro h6
  apply h2
  obtain ⟨i2, h7, h8⟩ := h6
  exists i2
  constructor
  exact h7
  obtain h9 := h1 i2 h7
  rw [h9]
  exact h8
  intro h10
  apply h2
  obtain ⟨i3, h11, h12⟩ := h10
  exists i3

-- 860：重複は OR-和では意味を持たない（keys ++ keys は keys と同じ）
theorem ex860 (keys : List ι) (F : ι → WRel α γ) :
    wsumW (keys ++ keys) F
      =
    wsumW keys F := by
  -- ヒント：ex849（append）と ex811 / ex816（OR の冪等性）
  funext a1 c1
  dsimp [wsumW, wBool, wSupp, maskW]
  obtain hEx606_1 :=
    ex606 (keys ++ keys) (fun b => F b a1 c1)
  obtain hEx606_2 :=
    ex606 keys (fun b => F b a1 c1)
  rw [hEx606_1, hEx606_2]
  clear hEx606_1 hEx606_2
  by_cases h1 : ∃ x, x ∈ keys ∧ F x a1 c1 > 0
  obtain ⟨i1, h2, h3⟩ := h1
  rw [if_pos]
  rw [if_pos]
  exists i1
  exists i1
  constructor
  apply List.mem_append_left
  exact h2
  exact h3
  rw [if_neg]
  rw [if_neg]
  intro h4
  apply h1
  obtain ⟨i2, h5, h6⟩ := h4
  exists i2
  intro h7
  apply h1
  obtain ⟨i3, h8, h9⟩ := h7
  exists i3
  constructor
  rw [List.mem_append] at h8
  rw [or_self] at h8
  exact h8
  exact h9

--------------------------------------------------------------------------------
-- 861〜865：row/col-sum と reach への分配
--------------------------------------------------------------------------------

-- 861：rowSum>0 は wsumW で “OR” 分配する
theorem ex861 (keysι : List ι) (keysg : List γ)
    (F : ι → WRel α γ) (a : α) :
    wRowSum keysg (wsumW keysι F) a > 0
      ↔
    ∃ i, i ∈ keysι ∧ wRowSum keysg (F i) a > 0 := by
  -- ヒント：
  --   * ex710（rowSum>0 ↔ ∃c∈keysg, ... >0）
  --   * ex846（support(wsumW)=∃i∈keysι, ... >0）
  dsimp [wRowSum]
  obtain hEx606_1 :=
    ex606 keysg (fun b => wsumW keysι F a b)
  rw [hEx606_1]
  clear hEx606_1

  conv =>
    rhs
    arg 1
    intro g1
    rhs
    rw [ex606]

  dsimp [wsumW, wSupp, wBool, maskW]

  conv =>
    lhs
    rhs
    intro x
    rhs
    arg 1
    arg 1
    rw [ex606]

  constructor
  intro h1
  obtain ⟨g1, h2, h3⟩ := h1
  have h4 : ∃ x, x ∈ keysι ∧ F x a g1 > 0 := by
    by_cases h4_ : ∃ x, x ∈ keysι ∧ F x a g1 > 0
    exact h4_
    rw [if_neg h4_] at h3
    contradiction
  clear h3
  obtain ⟨i1, h5, h6⟩ := h4
  exists i1
  constructor
  exact h5
  -- exists g1
  -- intro h7
  -- obtain ⟨i2, h8, h9⟩ := h7
  -- obtain ⟨g2, h10, h11⟩ := h9
  -- exists g2
  -- constructor
  -- exact h10
  -- have h12 : ∃ x, x ∈ keysι ∧ F x a g2 > 0 := by
  --   exists i2
  -- rw [if_pos h12]
  --apply Nat.zero_lt_one
  sorry













-- 862：colSum>0 も wsumW で “OR” 分配する
theorem ex862 (keysι : List ι) (keysα : List α)
    (F : ι → WRel α γ) (c : γ) :
    wColSum keysα (wsumW keysι F) c > 0
      ↔
    ∃ i, i ∈ keysι ∧ wColSum keysα (F i) c > 0 := by
  -- TODO
  -- ヒント：ex712 と ex846
  sorry

-- 863：reach は右の wsumW に分配する（OR の分配）
theorem ex863 (keysβ : List β) (keysι : List ι)
    (R : WRel α β) (F : ι → WRel β γ) :
    wReachComp keysβ R (wsumW keysι F)
      =
    wsumW keysι
      (fun i => wReachComp keysβ R (F i)) := by
  -- TODO
  -- ヒント：
  --   * wReachComp は support だけを見る（maskW ∘ relCompList）
  --   * support(wsumW)=∃i∈keysι, support(F i)
  --   * relCompList は右引数の OR に分配（ex658 の “List 版” を keysι で帰納）
  sorry

-- 864：reach は左の wsumW にも分配する（OR の分配）
theorem ex864 (keysβ : List β) (keysι : List ι)
    (F : ι → WRel α β) (S : WRel β γ) :
    wReachComp keysβ (wsumW keysι F) S
      =
    wsumW keysι
      (fun i => wReachComp keysβ (F i) S) := by
  -- TODO
  -- ヒント：ex863 の左版（relCompList の左 OR 分配＝ex657 を List で回す）
  sorry

-- 865：wReachComp の append（keys を分割すると OR に分解できる）
theorem ex865 (keys₁ keys₂ : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp (keys₁ ++ keys₂) R S
      =
    wBool (wAdd (wReachComp keys₁ R S) (wReachComp keys₂ R S)) := by
  -- TODO
  -- ヒント：
  --   * wReachComp の定義（maskW ∘ relCompList）
  --   * relCompList の append 分解（keys の ∃ は OR）
  --   * 0/1 化は wBool でまとめる
  sorry

--------------------------------------------------------------------------------
-- 866〜870：wReachComp の計算規則（empty / singleton / graph など）
--------------------------------------------------------------------------------

-- 866：空 keys の reach は wZero
theorem ex866 (R : WRel α β) (S : WRel β γ) :
    wReachComp ([] : List β) R S = wZero α γ := by
  -- TODO
  -- ヒント：wReachComp の定義で relCompList [] ... は False
  sorry

-- 867：singleton keys の reach は “その 1 点 b を witness にした到達”
theorem ex867 (b : β) (R : WRel α β) (S : WRel β γ) :
    wReachComp [b] R S
      =
    maskW (fun a c => wSupp R a b ∧ wSupp S b c) := by
  -- TODO
  -- ヒント：wReachComp の定義で relCompList [b] を展開
  sorry

-- 868：reach は wBool を両側に入れても不変（到達だけを見るので）
theorem ex868 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp keys (wBool R) (wBool S) = wReachComp keys R S := by
  -- TODO
  -- ヒント：ex824 を使えばよい
  sorry

-- 869：右が graph の reach は、列選択テンソルの OR-和（wsumW）で表せる
theorem ex869 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    wsumW keys
      (fun b => wMask (fun a c => wBool R a b) (fun _ c => g b = c)) := by
  -- TODO
  -- ヒント：Basic_841 の ex843 をそのまま使う
  sorry

-- 870：keys が {f a} を全て含むなら、graph 合成の reach は単なる関数合成の graph（reach 版）
theorem ex870 (keys : List β) (f : α → β) (g : β → γ) :
    (∀ a : α, f a ∈ keys) →
      wReachComp keys (wGraph f) (wGraph g)
        =
      wGraph (fun a => g (f a)) := by
  -- TODO
  -- ヒント：ex836（reach の graph-graph 合成で mask を消す）
  sorry

end TL
