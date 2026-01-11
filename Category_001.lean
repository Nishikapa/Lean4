
-- 圏論演習問題 001〜020（Lean4 + mathlib4）

-- 使い方：
-- * 各 `sorry` を埋めてください。
-- * まずは `simp` / `simpa` / `rfl` を試すと解けるものが多いです。
-- * notations: `X ⟶ Y`, `𝟙 X`, `f ≫ g`, `C ⥤ D`, `𝟭 C`, `F ⋙ G`, `X ≅ Y`, `⊤_ C` などを使います。

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open scoped CategoryTheory
open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheoryExercises

universe v u v₁ u₁ v₂ u₂ v₃ u₃

/-! ############################################################
  演習問題 001〜006：圏の基本（恒等射・合成・結合律）
############################################################ -/

section Exercises001_006

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

-- 演習問題001
-- 右単位律：f ≫ 𝟙 = f
-- ヒント: `simp`
theorem ex001 (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  sorry

-- 演習問題002
-- 左単位律：𝟙 ≫ f = f
-- ヒント: `simp`
theorem ex002 (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  sorry

-- 演習問題003
-- 結合律：(f ≫ g) ≫ h = f ≫ (g ≫ h)
-- ヒント: `simp [Category.assoc]` または `simpa using (Category.assoc f g h)`
theorem ex003 (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  sorry

-- 演習問題004
-- 恒等射を途中に挿入しても変わらない
-- ヒント: `simp` （必要なら `simp [Category.assoc]`）
theorem ex004 (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ 𝟙 Y ≫ g = f ≫ g := by
  sorry

-- 演習問題005
-- 両側に恒等射を挟んでも変わらない
-- ヒント: `simp`
theorem ex005 (f : X ⟶ Y) :
    𝟙 X ≫ f ≫ 𝟙 Y = f := by
  sorry

-- 演習問題006
-- 等式の右側 whisker（=≫）: f=g なら f≫h = g≫h
-- ヒント: `simpa using (w =≫ h)` （`=≫` は「右から合成する」操作）
theorem ex006 {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by
  sorry

end Exercises001_006

/-! ############################################################
  演習問題 007〜010：反対圏（op / unop）
############################################################ -/

section Exercises007_010

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

-- 演習問題007
-- 反対圏への `op` は恒等射を保つ
-- ヒント: `simp`
theorem ex007 (X : C) : (𝟙 X).op = 𝟙 (Opposite.op X) := by
  sorry

-- 演習問題008
-- 反対圏への `op` は合成の順序を反転する
-- ヒント: `simp`
theorem ex008 (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).op = g.op ≫ f.op := by
  sorry

-- 演習問題009
-- `op` して `unop` すると元に戻る（射版）
-- ヒント: `simp`
theorem ex009 (f : X ⟶ Y) : f.op.unop = f := by
  sorry

-- 演習問題010
-- `unop` して `op` すると元に戻る（射版、ただし反対圏の射）
-- ヒント: `simp`
theorem ex010 {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f := by
  sorry

end Exercises007_010

/-! ############################################################
  演習問題 011〜014：関手（map / obj / 合成）
############################################################ -/

section Exercises011_014

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

variable {X Y Z : C}

-- 演習問題011
-- 関手は恒等射を保つ
-- ヒント: `simp`
theorem ex011 (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  sorry

-- 演習問題012
-- 関手は合成を保つ
-- ヒント: `simp`
theorem ex012 (F : C ⥤ D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  sorry

-- 演習問題013
-- 恒等関手（𝟭 C）の map はそのまま
-- ヒント: `simp`
theorem ex013 (f : X ⟶ Y) :
    (𝟭 C).map f = f := by
  sorry

-- 演習問題014
-- 合成関手（F ⋙ G）の map の展開
-- ヒント: `simp`
theorem ex014 (F : C ⥤ D) (G : D ⥤ E) (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  sorry

end Exercises011_014

/-! ############################################################
  演習問題 015〜018：自然変換（app / naturality / 合成）
############################################################ -/

section Exercises015_018

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (F G H : C ⥤ D)
variable {X Y : C}

-- 演習問題015
-- 自然変換 η の成分 η.app X を「項」として取り出す
-- ヒント: `exact η.app X`
def ex015 (η : F ⟶ G) (X : C) : F.obj X ⟶ G.obj X := by
  sorry

-- 演習問題016
-- 自然性（naturality）
-- ヒント: `simpa using (η.naturality f)` または `simp` でも可
theorem ex016 (η : F ⟶ G) (f : X ⟶ Y) :
    F.map f ≫ η.app Y = η.app X ≫ G.map f := by
  sorry

-- 演習問題017
-- 恒等自然変換の成分
-- ヒント: `simp`
theorem ex017 {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    ((𝟙 F : F ⟶ F)).app X = 𝟙 (F.obj X) := by
  sorry

-- 演習問題018
-- 自然変換の縦合成（≫）の成分
-- ヒント: `simp`
theorem ex018 (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
    (η ≫ θ).app X = η.app X ≫ θ.app X := by
  sorry

end Exercises015_018

/-! ############################################################
  演習問題 019〜020：同型と終対象
############################################################ -/

section Exercises019_020

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

-- 演習問題019
-- 同型 i : X ≅ Y について、i.hom ≫ i.inv = 𝟙 X
-- ヒント: `simp`
theorem ex019 (i : X ≅ Y) : i.hom ≫ i.inv = 𝟙 X := by
  sorry

-- 演習問題020
-- 終対象への射は一意（終対象の普遍性の「一意性」部分）
-- ヒント: `simpa using (terminal.hom_ext f g)`
theorem ex020 [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C) :
    f = g := by
  sorry

end Exercises019_020

end CategoryTheoryExercises
