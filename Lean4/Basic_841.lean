--------------------------------------------------------------------------------
-- Basic_841.lean
-- 演習問題 841〜855（fast-track 7：reach-sum semantics / wId・wGraph と到達テンソル）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 826〜840 は Basic_826 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_826

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wsumW：WRel の “OR-和”）
--------------------------------------------------------------------------------

-- keys 上で「各 b の行列を足してから 0/1 に潰す」和
-- （0/1 行列を入れたときは “OR” に対応する）
--
--   wsumW keys F a c = if (Σ b∈keys, F b a c) > 0 then 1 else 0
noncomputable def wsumW (keys : List β) (F : β → WRel α γ) : WRel α γ :=
  wBool (fun a c => wsum keys (fun b => F b a c))

--------------------------------------------------------------------------------
-- 841〜845：wsumW の基本計算規則 / reach を “OR-和” で表す
--------------------------------------------------------------------------------

-- 841：空の OR-和は 0
theorem ex841 (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) ([] : List β) F = wZero α γ := by
  -- ヒント：
  --   * funext a c; dsimp [wsumW, wBool]; dsimp [wsum]
  --   * wBool で 0 は 0/1 に潰しても 0
  funext a1 c1
  dsimp [wsumW, wBool, wsum, maskW, wSupp, wZero]
  rw [if_neg]
  intro h
  contradiction

-- 842：cons の計算（1 項 + tail の OR-和）
theorem ex842 (b : β) (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: keys) F
      =
    wBool (wAdd (F b) (fun a c => wsum keys (fun b => F b a c))) := by
  -- ヒント：
  --   * dsimp [wsumW]; dsimp [wsum]
  --   * funext a c; rfl まで持っていく
  funext a1 c1
  dsimp [wsumW, wBool, wsum, maskW, wSupp, wAdd]

-- 843：右が graph の reach は “各 b の列選択” を OR-和したもの
theorem ex843 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    wsumW keys (fun b => wMask (fun a c => wBool R a b) (fun _ c => g b = c)) := by
  -- ヒント：
  --   * wsumW の定義を展開すると “各 b について足す”
  --   * 0/1 同士の和→最後に wBool（maskW）へ
  --   * まずは “support（到達）” で同値を示す方が楽

  funext a1 c1
  dsimp [wReachComp, wsumW, wBool, wGraph, wMask, wSupp, wAdd, maskW, relCompList, relGraph]
  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  -- obtain hEx606 :=
  --   ex606
  conv =>
    rhs
    arg 1
    rw [ex606]
  by_cases h1 :
    ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if g b = c1 then 1 else 0) > 0
  rw [if_pos h1]
  obtain ⟨b0, hMem, hR, hG⟩ := h1
  have hG2 : g b0 = c1 := by
    by_cases hG2_1 : g b0 = c1
    exact hG2_1
    rw [if_neg hG2_1] at hG
    contradiction
  clear hG
  rw [if_pos]
  exists b0
  constructor
  exact hMem
  rw [← hG2]
  rw [if_pos]
  rw [if_pos]
  rw [Nat.mul_one]
  apply Nat.zero_lt_one
  rfl
  exact hR
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  obtain ⟨b1, hMem, h3⟩ := h2
  rw [gt_iff_lt] at h3
  have  h3_1: g b1 = c1 := by
    by_cases h3_1_ : g b1 = c1
    exact h3_1_
    rw [if_neg h3_1_] at h3
    contradiction
  have h3_2 : R a1 b1 > 0 := by
    by_cases h3_2_ : R a1 b1 > 0
    exact h3_2_
    rw [if_neg h3_2_] at h3
    rw [Nat.zero_mul] at h3
    contradiction
  clear h3
  apply h1
  exists b1
  constructor
  exact hMem
  constructor
  exact h3_2
  rw [h3_1]
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

-- 844：一般版：reach は “各 b の AND（固定 b）” を OR-和したもの
theorem ex844 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp keys R S
      =
    wsumW keys (fun b =>
      wMask (fun a c => wBool R a b) (fun _ c => wSupp S b c)) := by
  -- ヒント：
  --   * ex833（reach = maskW(∃ b∈keys, ... )）を使うと楽
  --   * wsumW は「∃ b∈keys, 項>0」を表していることを示す（ex606 を使う）
  --   * wMask で “S b c > 0” を掛けていると思えばよい

  funext a1 c1
  dsimp [wReachComp, maskW, relCompList, wsumW, wBool, wSupp, wMask]

  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0)
  -- wsum keys fun b => (if R a1 b > 0 then 1 else 0) * if S b c1 > 0 then 1 else 0

  conv =>
    rhs
    arg 1
    rw [ex606]

  by_cases h1 :
    ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0

  rw [if_pos h1]
  obtain ⟨b0, hMem, hR, hS⟩ := h1
  rw [if_pos]
  exists b0
  constructor
  exact hMem
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hS
  exact hR
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  obtain ⟨b1, hMem, h3⟩ := h2
  have h3_1 : R a1 b1 > 0 := by
    by_cases h3_1 : R a1 b1 > 0
    exact h3_1
    rw [if_neg h3_1] at h3
    rw [Nat.zero_mul] at h3
    contradiction
  have h3_2 : S b1 c1 > 0 := by
    by_cases h3_2 : S b1 c1 > 0
    exact h3_2
    rw [if_neg h3_2] at h3
    rw [Nat.mul_zero] at h3
    contradiction
  clear h3
  apply h1
  exists b1

-- 845：wsumW の意味論：OR-和の 0/1 は「どれか 1 つでも >0」
theorem ex845 (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) keys F
      =
    maskW (fun a c => ∃ b, b ∈ keys ∧ F b a c > 0) := by
  -- ヒント：
  --   * dsimp [wsumW, wBool, maskW, wSupp]
  --   * ex606 を xs:=keys, f:=fun b => F b a c に適用
  --   * funext a c; by_cases h : (∃ b, b ∈ keys ∧ F b a c > 0)
  --     で if の枝をそろえる
  funext a1 c1
  dsimp [wsumW, wBool, maskW, wSupp]
  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0)
   --    (wsum keys fun b => F b a1 c1) >
  obtain hEx606 :=
    ex606 keys fun b => F b a1 c1
  rw [hEx606]

--------------------------------------------------------------------------------
-- 846〜850：wId / wGraph と reach を wsumW で観察（行選択・列選択）
--------------------------------------------------------------------------------

-- 846：右が wId の reach は「列 b を選ぶテンソル」を OR-和したもの
theorem ex846 (keys : List β) (R : WRel α β) :
    wReachComp keys R (wId β)
      =
    wsumW keys (fun b => wMask (fun a c => wBool R a b) (fun _ c => b = c)) := by
  -- ヒント：
  --   * ex843 に g := fun b => b を入れる
  --   * wGraph (fun b => b) = wId β（定義展開で示せる）

  have h1 : wGraph (fun b => b) = wId β := by
    funext b1 c1
    dsimp [wGraph, wId, wBool, maskW, relGraph, relId]

  rw [←h1]

  -- theorem ex843 (keys : List β) (R : WRel α β) (g : β → γ) :
  --     wReachComp keys R (wGraph g)
  --       =
  --     wsumW keys (fun b => wMask (fun a c => wBool R a b) (fun _ c => g b = c)) := by
  obtain hEx843 :=
    ex843 keys R (fun b => b)
  rw [hEx843]

-- 847：左が wId の reach を wsumW で書く（行を 1 本ずつ OR-和）
theorem ex847 (keys : List α) (S : WRel α γ) :
    wReachComp keys (wId α) S
      =
    wsumW keys (fun a0 =>
      wMask (fun a c => if a = a0 then 1 else 0) (fun _ c => wSupp S a0 c)) := by
  -- ヒント：
  --   * ex844 に R := wId α を入れる
  --   * wBool (wId α) a a0 は if a = a0 then 1 else 0

  have h1 : ∀ a1 a2, (wBool (wId α) a1 a2) = (if a1 = a2 then 1 else 0) := by
    intro a1 a2
    dsimp [wId, wBool, maskW, relId, wSupp]
    by_cases hEq : a1 = a2
    rw [hEq]
    rw [if_pos]
    rw [if_pos]
    rfl
    rw [if_pos]
    apply Nat.zero_lt_one
    rfl
    rw [if_neg]
    rw [if_neg]
    intro h1_1
    contradiction
    intro h1_2
    apply hEq
    rw [if_neg hEq] at h1_2
    contradiction

  conv =>
    rhs
    arg 2
    intro a1 c1
    arg 1
    intro a2 c2
    rw [←h1]

  -- theorem ex844 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wReachComp keys R S
  --       =
  --     wsumW keys (fun b =>
  --       wMask (fun a c => wBool R a b) (fun _ c => wSupp S b c)) := by
  obtain hEx844 :=
    ex844 keys (wId α) S
  rw [←hEx844]

-- 848：左が graph の reach（行選択の到達版）
theorem ex848 (keys : List β) (f : α → β) (S : WRel β γ) :
    wReachComp keys (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys) := by
  -- ヒント：
  --   * これは ex832 と同じステートメント（再掲）
  --   * もしくは ex844（sum 版）から、graph の一意性で b を f a に潰す

  -- theorem ex844 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wReachComp keys R S
  --       =
  --     wsumW keys (fun b =>
  --       wMask (fun a c => wBool R a b) (fun _ c => wSupp S b c)) := by
  obtain hEx844 :=
    ex844 keys (wGraph f) S
  rw [hEx844]
  clear hEx844
  funext a1 c1
  dsimp [wsumW, wBool, maskW, wSupp, wMask, wGraph, relGraph]
  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --     (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0)
  -- (wsum keys fun b => (if (if f a1 = b then 1 else 0) > 0 then 1 else 0) * if S b c1 > 0 then 1 else 0) > 0
  -- obtain hEx606 :=
  --   ex606 keys fun b => (if (if f a1 = b then 1 else 0) > 0 then 1 else 0) * if S b c1 > 0 then 1 else 0
  conv =>
    lhs
    arg 1
    rw [ex606]
  by_cases h1 : ∃ x, x ∈ keys ∧ ((if (if f a1 = x then 1 else 0) > 0 then 1 else 0) * if S x c1 > 0 then 1 else 0) > 0
  obtain ⟨b0, hMem, hProd⟩ := h1
  have hProd_1 : S b0 c1 > 0 := by
    by_cases hProd_1_ : S b0 c1 > 0
    exact hProd_1_
    rw [if_neg hProd_1_] at hProd
    rw [Nat.mul_zero] at hProd
    contradiction
  have hProd_2 : f a1 = b0 := by
    by_cases hProd_2_ : f a1 = b0
    exact hProd_2_
    rw [if_neg hProd_2_] at hProd
    rw [if_neg] at hProd
    rw [Nat.zero_mul] at hProd
    contradiction
    intro hProd_2_1
    contradiction
  clear hProd
  rw [hProd_2]
  rw [if_pos hProd_1]
  rw [Nat.one_mul]
  rw [if_pos hMem]
  rw [if_pos]
  exists b0
  constructor
  exact hMem
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hProd_1
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  -- neg
  rw [if_neg]
  symm
  rw [Nat.mul_eq_zero]
  by_cases h2 : f a1 ∈ keys
  rw [if_pos h2]
  left
  rw [if_neg]
  intro h3
  apply h1
  exists (f a1)
  constructor
  exact h2
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h3
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  right
  rw [if_neg]
  intro h4
  apply h2
  exact h4
  intro h5
  obtain ⟨b1, hMem, hProd⟩ := h5
  have hProd_1 : S b1 c1 > 0 := by
    by_cases hProd_1_ : S b1 c1 > 0
    exact hProd_1_
    rw [if_neg hProd_1_] at hProd
    rw [Nat.mul_zero] at hProd
    contradiction
  have hProd_2 : f a1 = b1 := by
    by_cases hProd_2_ : f a1 = b1
    exact hProd_2_
    rw [if_neg hProd_2_] at hProd
    rw [if_neg] at hProd
    rw [Nat.zero_mul] at hProd
    contradiction
    intro hProd_2_1
    contradiction
  clear hProd
  apply h1
  exists b1
  constructor
  exact hMem
  rw [hProd_2]
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hProd_1
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl

-- 849：graph-graph の reach（関数合成 + keys マスク）
theorem ex849 (keys : List β) (f : α → β) (g : β → γ) :
    wReachComp keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- ヒント：ex835 と同じ（再掲）
  apply ex835

-- 850：keys が {f a} を全て含むなら、graph の reach はマスクが消える
theorem ex850 (keys : List β) (f : α → β) (S : WRel β γ) :
    (∀ a : α, f a ∈ keys) →
      wReachComp keys (wGraph f) S
        =
      (fun a c => wBool S (f a) c) := by

  -- ヒント：
  --   * ex836 を funext でまとめる
  --   * あるいは ex848 を使って wMask の条件を if_pos で消す

  -- theorem ex848 (keys : List β) (f : α → β) (S : WRel β γ) :
  --     wReachComp keys (wGraph f) S
  --       =
  --     wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys)
  obtain hEx848 :=
    ex848 keys f S
  rw [hEx848]
  clear hEx848

  intro h1
  funext a1 c1
  dsimp [wMask, wBool, maskW, wSupp]
  by_cases h2 : S (f a1) c1 > 0
  rw [if_pos h2]
  rw [Nat.one_mul]
  obtain h3 := h1 a1
  rw [if_pos]
  exact h3
  rw [if_neg h2]
  rw [Nat.zero_mul]

--------------------------------------------------------------------------------
-- 851〜855：wsumW の代数（transpose / append / 重複 / 単調性）
--------------------------------------------------------------------------------

-- 851：transpose と wsumW は可換
theorem ex851 (keys : List β) (F : β → WRel α γ) :
    wTrans (wsumW (α:=α) (β:=β) (γ:=γ) keys F)
      =
    wsumW (α:=γ) (β:=β) (γ:=α) keys (fun b => wTrans (F b)) := by
  -- ヒント：
  --   * funext c a; dsimp [wsumW, wTrans]
  --   * まずは wSupp（>0）が同じことを示すのが楽
  --   * wSupp(wBool _) は元と同じ（ex796）
  funext c1 a1
  dsimp [wsumW, wTrans, wBool, wSupp, maskW]

-- 852：append は OR（bool-sum）になる
theorem ex852 (keys₁ keys₂ : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (keys₁ ++ keys₂) F
      =
    wBool (wAdd (wsumW (α:=α) (β:=β) (γ:=γ) keys₁ F)
                (wsumW (α:=α) (β:=β) (γ:=γ) keys₂ F)) := by
  -- ヒント：
  --   * ex845 で両辺を maskW(∃...) に落とすのが楽
  --   * “∃ b∈(xs++ys), ...” は xs 側 / ys 側に分解できる
  --   * 0/1 の OR は wBool(wAdd ...) で表せる（ex755 / ex820 など）
  obtain hEx845 :=
    ex845 (keys₁ ++ keys₂) F
  rw [hEx845]
  clear hEx845
  funext a1 c1
  dsimp [wBool, wsumW, wSupp]
  conv =>
    rhs
    arg 1
    intro a2 c2
    dsimp [wSupp]
    dsimp [wAdd]
    rw [gt_iff_lt]
    rw [Nat.add_pos_iff_pos_or_pos]
    dsimp [maskW, wSupp]
    conv =>
      lhs
      rhs
      arg 1
      rw [ex606]
    conv =>
      lhs
      rw [
        show (0 < if ∃ x, x ∈ keys₁ ∧ F x a2 c2 > 0 then 1 else 0) ↔ (∃ x, x ∈ keys₁ ∧ F x a2 c2 > 0) from by
          by_cases h1 :
            ∃ x, x ∈ keys₁ ∧ F x a2 c2 > 0
          rw [if_pos h1]
          constructor
          intro h2
          exact h1
          intro h3
          apply Nat.zero_lt_one
          rw [if_neg h1]
          constructor
          intro h4
          contradiction
          intro h5
          contradiction
      ]
    conv =>
      rhs
      rhs
      arg 1
      rw [ex606]
    conv =>
      rhs
      rw [
        show (0 < if ∃ x, x ∈ keys₂ ∧ F x a2 c2 > 0 then 1 else 0) ↔ (∃ x, x ∈ keys₂ ∧ F x a2 c2 > 0) from by
          by_cases h1 :
            ∃ x, x ∈ keys₂ ∧ F x a2 c2 > 0
          rw [if_pos h1]
          constructor
          intro h2
          exact h1
          intro h3
          apply Nat.zero_lt_one
          rw [if_neg h1]
          constructor
          intro h4
          contradiction
          intro h5
          contradiction
      ]
  dsimp [maskW]
  by_cases h10 :
    ∃ b, b ∈ keys₁ ++ keys₂ ∧ F b a1 c1 > 0
  rw [if_pos h10]
  obtain ⟨b0, hMem, hF⟩ := h10
  rw [if_pos]
  rw [List.mem_append] at hMem
  obtain hMem1 | hMem2 := hMem
  left
  exists b0
  right
  exists b0
  rw [if_neg h10]
  rw [if_neg]
  intro h11
  obtain ⟨b1, hMem1, hF1⟩ | ⟨b2, hMem2, hF2⟩ := h11
  apply h10
  exists b1
  constructor
  apply  List.mem_append_left
  exact hMem1
  exact hF1
  apply h10
  exists b2
  constructor
  apply List.mem_append_right
  exact hMem2
  exact hF2

-- 853：同じ b を 2 回足しても OR なので変わらない
theorem ex853 (b : β) (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: b :: keys) F
      =
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: keys) F := by
  -- ヒント：
  --   * ex845 による “∃ b∈...” の形で見れば明らか
  --   * List.mem_cons / or_assoc などで整理

  -- theorem ex845 (keys : List β) (F : β → WRel α γ) :
  --     wsumW (α:=α) (β:=β) (γ:=γ) keys F
  --       =
  --     maskW (fun a c => ∃ b, b ∈ keys ∧ F b a c > 0) := by
  obtain hEx845_1 :=
    ex845 (b :: b :: keys) F
  obtain hEx845_2 :=
    ex845 (b :: keys) F
  rw [hEx845_1, hEx845_2]
  clear hEx845_1 hEx845_2

  funext a1 c1
  dsimp [maskW, wSupp]

  conv =>
    lhs
    arg 1
    arg 1
    intro b1
    lhs
    rw [
      show (b1 ∈ b :: b :: keys) ↔ (b1 ∈ b :: keys) from by
        rw [List.mem_cons]
        rw [List.mem_cons]
        conv =>
          lhs
          rw [←or_assoc]
          lhs
          rw [or_self]
    ]

  by_cases h1 : ∃ b1, b1 ∈ b :: keys ∧ F b1 a1 c1 > 0
  rw [if_pos h1]
  obtain ⟨b0, hMem, hF⟩ := h1
  rw [if_pos]
  exists b0
  rw [if_neg]
  rw [if_neg]
  intro h2
  obtain ⟨b2, hMem1, hF1⟩ := h2
  apply h1
  exists b2
  exact h1

-- 854：keys 上で全部 0（到達なし）なら OR-和も 0
theorem ex854 (keys : List β) (F : β → WRel α γ) :
    (∀ b, b ∈ keys → F b = wZero α γ) →
      wsumW (α:=α) (β:=β) (γ:=γ) keys F = wZero α γ := by
  -- ヒント：
  --   * ex845 で maskW(∃ b∈keys, ...) に落とし、∃ を否定して if_neg
  --   * あるいは ex607（wsum=0 ↔ 全項=0）を使ってもよい

  -- theorem ex845 (keys : List β) (F : β → WRel α γ) :
  --     wsumW (α:=α) (β:=β) (γ:=γ) keys F
  --       =
  --     maskW (fun a c => ∃ b, b ∈ keys ∧ F b a c > 0) := by
  obtain hEx845 :=
    ex845 keys F
  rw [hEx845]
  clear hEx845

  intro h1
  funext a1 c1
  dsimp [maskW, wSupp, wZero]
  rw [if_neg]
  intro h2
  obtain ⟨b0, hMem, hF⟩ := h2
  have h2 := h1 b0 hMem
  rw [h2] at hF
  dsimp [wZero, wBool, maskW, wSupp] at hF
  contradiction

-- 855：単調性：各 b で F b ≤ G b なら OR-和も ≤
theorem ex855 (keys : List β) (F G : β → WRel α γ) :
    (∀ b, WLe (F b) (G b)) →
      WLe (wsumW (α:=α) (β:=β) (γ:=γ) keys F)
          (wsumW (α:=α) (β:=β) (γ:=γ) keys G) := by
  -- ヒント：
  --   * ex615（WLe→support包含）と ex845（wsumW=maskW(∃...)）を使うのが楽
  --   * 最後は ex801（maskW M ≤ R ↔ M ⊆ wSupp R）などでもよい

  -- theorem ex845 (keys : List β) (F : β → WRel α γ) :
  -- wsumW (α:=α) (β:=β) (γ:=γ) keys F
  --   =
  -- maskW (fun a c => ∃ b, b ∈ keys ∧ F b a c > 0) := by

  conv =>
    rhs
    conv =>
      arg 1
      rw [ex845]
    conv =>
      arg 2
      rw [ex845]

  intro h1

  -- theorem ex615 (R S : WRel α β) :
  --     WLe R S → (wSupp R ⊆ wSupp S)

  -- theorem ex801 (M : Rel α β) (R : WRel α β) :
  --     WLe (maskW M) R ↔ (M ⊆ wSupp R) := by
  rw [ex801]

  intro a1 c1 h2
  obtain ⟨b0, hMem, hF⟩ := h2
  rw [gt_iff_lt] at hF
  dsimp [wSupp, maskW]
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b0
  constructor
  exact hMem
  have hF2 := h1 b0 a1 c1
  obtain hF3 := Nat.lt_of_lt_of_le hF hF2
  exact hF3

end TL
