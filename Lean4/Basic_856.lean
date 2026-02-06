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
  -- TODO
  -- ヒント：wsumW の定義と ex811（wBool idempotent）
  sorry

-- 857：i ∈ keys なら、その項（の 0/1 化）は wsumW 以下
-- （“OR-和” は各項を含む）
theorem ex857 (keys : List ι) (F : ι → WRel α γ) (i : ι) :
    i ∈ keys →
      WLe (wBool (F i)) (wsumW keys F) := by
  -- TODO
  -- ヒント：support で示す（ex615 / ex846）
  sorry

-- 858：keys の単調性（候補が増えるほど OR-和も増える）
theorem ex858 (keys keys' : List ι) (F : ι → WRel α γ) :
    (∀ i, i ∈ keys → i ∈ keys') →
      WLe (wsumW keys F)
          (wsumW keys' F) := by
  -- TODO
  -- ヒント：ex846 の ∃ 形で support の包含を示す
  sorry

-- 859：wsumW の ext（keys 上で項が一致すれば wsumW も一致）
theorem ex859 (keys : List ι) (F G : ι → WRel α γ) :
    (∀ i, i ∈ keys → F i = G i) →
      wsumW keys F
        =
      wsumW keys G := by
  -- TODO
  -- ヒント：funext a c; wsum の項ごとの一致（keys で帰納）
  sorry

-- 860：重複は OR-和では意味を持たない（keys ++ keys は keys と同じ）
theorem ex860 (keys : List ι) (F : ι → WRel α γ) :
    wsumW (keys ++ keys) F
      =
    wsumW keys F := by
  -- TODO
  -- ヒント：ex849（append）と ex811 / ex816（OR の冪等性）
  sorry

--------------------------------------------------------------------------------
-- 861〜865：row/col-sum と reach への分配
--------------------------------------------------------------------------------

-- 861：rowSum>0 は wsumW で “OR” 分配する
theorem ex861 (keysι : List ι) (keysg : List γ)
    (F : ι → WRel α γ) (a : α) :
    wRowSum keysg (wsumW keysι F) a > 0
      ↔
    ∃ i, i ∈ keysι ∧ wRowSum keysg (F i) a > 0 := by
  -- TODO
  -- ヒント：
  --   * ex710（rowSum>0 ↔ ∃c∈keysg, ... >0）
  --   * ex846（support(wsumW)=∃i∈keysι, ... >0）
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
