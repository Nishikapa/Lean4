--------------------------------------------------------------------------------
-- Basic_871.lean
-- 演習問題 871〜885（fast-track 9：wReachComp / wsumW を “OR-AND 半環” として扱う）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 856〜870 は Basic_856 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_856

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε ι : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wOr：0/1 の OR）
--------------------------------------------------------------------------------

-- OR（到達の和）：重みは捨て、>0 だけ残す
noncomputable def wOr (R S : WRel α β) : WRel α β :=
  wBool (wAdd R S)

--------------------------------------------------------------------------------
-- 871〜875：wOr の代数（comm / assoc / idem / zero）
--------------------------------------------------------------------------------

-- 871：support(wOr) は論理和（∨）
theorem ex871 (R S : WRel α β) :
    wSupp (wOr R S) = relAdd (wSupp R) (wSupp S) := by
  -- TODO
  -- ヒント：
  --   * wOr の定義
  --   * ex816（wBool (wAdd ...) = maskW (relAdd ...)）
  --   * ex613（support(maskW M)=M）
  sorry

-- 872：wOr は可換
theorem ex872 (R S : WRel α β) :
    wOr R S = wOr S R := by
  -- TODO
  -- ヒント：funext; dsimp [wOr, wAdd]; Nat.add_comm
  sorry

-- 873：wOr は結合的
theorem ex873 (R S T : WRel α β) :
    wOr (wOr R S) T = wOr R (wOr S T) := by
  -- TODO
  -- ヒント：Nat.add_assoc と ex811（wBool の冪等性）など
  sorry

-- 874：wOr は冪等（R ∨ R = R の 0/1 版）
theorem ex874 (R : WRel α β) :
    wOr R R = wBool R := by
  -- TODO
  -- ヒント：support が同じことを示して wBool に落とす（ex796 / ex816）
  sorry

-- 875：wZero は wOr の単位元（ただし結果は wBool R）
theorem ex875 (R : WRel α β) :
    wOr R (wZero α β) = wBool R := by
  -- TODO
  -- ヒント：wAdd R 0 = R, wOr 定義
  sorry

--------------------------------------------------------------------------------
-- 876〜880：wReachComp と wOr の相互作用（分配・zero）
--------------------------------------------------------------------------------

-- 876：reach は wOr（左）に分配する
theorem ex876 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    wReachComp keys (wOr R R') S
      =
    wOr (wReachComp keys R S) (wReachComp keys R' S) := by
  -- TODO
  -- ヒント：wReachComp は support だけを見る（ex818） + ex871
  sorry

-- 877：reach は wOr（右）に分配する
theorem ex877 (keys : List β) (R : WRel α β) (S S' : WRel β γ) :
    wReachComp keys R (wOr S S')
      =
    wOr (wReachComp keys R S) (wReachComp keys R S') := by
  -- TODO
  -- ヒント：wReachComp は support だけを見る（ex818） + ex871
  sorry

-- 878：zero と reach（左が 0）
theorem ex878 (keys : List β) (S : WRel β γ) :
    wReachComp keys (wZero α β) S = wZero α γ := by
  -- TODO
  -- ヒント：wSupp(wZero)=False → relCompList が空
  sorry

-- 879：zero と reach（右が 0）
theorem ex879 (keys : List β) (R : WRel α β) :
    wReachComp keys R (wZero β γ) = wZero α γ := by
  -- TODO
  -- ヒント：wSupp(wZero)=False → relCompList が空
  sorry

-- 880：reach の結果は常に 0/1（wBool の固定点）
theorem ex880 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wBool (wReachComp keys R S) = wReachComp keys R S := by
  -- TODO
  -- ヒント：wReachComp は maskW で定義されているので ex812
  sorry

--------------------------------------------------------------------------------
-- 881〜885：wsumW と reach（OR-和との分配・graph 特別ケース）
--------------------------------------------------------------------------------

-- 881：reach は wsumW（左）に分配する
theorem ex881 (keysβ : List β) (keysι : List ι)
    (F : ι → WRel α β) (S : WRel β γ) :
    wReachComp keysβ (wsumW keysι F) S
      =
    wsumW keysι (fun i => wReachComp keysβ (F i) S) := by
  -- TODO
  -- ヒント：support で示すのが楽：ex818 + ex846
  sorry

-- 882：keys がすべて含むなら wId は本当の右単位になる
theorem ex882 (keysβ : List β) (R : WRel α β) :
    (∀ b : β, b ∈ keysβ) →
      wReachComp keysβ R (wId β) = wBool R := by
  -- TODO
  -- ヒント：ex842 の RHS で b∈keysβ を消す
  sorry

-- 883：keys がすべて含むなら wId は本当の左単位になる
theorem ex883 (keysα : List α) (R : WRel α β) :
    (∀ a : α, a ∈ keysα) →
      wReachComp keysα (wId α) R = wBool R := by
  -- TODO
  -- ヒント：ex841 の RHS で a∈keysα を消す
  sorry

-- 884：graph を右に置いた reach の support（存在条件）
theorem ex884 (keys : List β) (R : WRel α β) (g : β → γ) :
    wSupp (wReachComp keys R (wGraph g))
      =
    (fun a c => ∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by
  -- TODO
  -- ヒント：ex818 + wSupp(wGraph g)=relGraph g
  sorry

-- 885：graph を右に置いた reach は “列の行選択” の OR-和（Basic_841 の復習）
theorem ex885 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    wsumW keys (fun b =>
      wMask (fun a c => wBool R a b) (fun _ c => g b = c)) := by
  -- TODO
  -- ヒント：Basic_841.ex843
  sorry

end TL
