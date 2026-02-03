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
--  -- have h_symm : wTrans (wId α) = wId α := by

theorem ex766_pre :
  wTrans (wId α) = wId α := by
  -- 単位行列は転置しても単位行列
  funext a1 a2
  dsimp [wTrans, wId, maskW, relId]
  by_cases h_eq : (a2 = a1)
  rw [if_pos h_eq]
  rw [if_pos h_eq.symm]
  rw [if_neg h_eq]
  obtain  h_rev : ¬a1 = a2 := by
    intro h
    apply h_eq
    rw [h]
  rw [if_neg h_rev]

-- 766：keys.Nodup なら、wId の colSum も 0/1（a ∈ keys なら 1、それ以外は 0）
theorem ex766 (keys : List α) (a : α) :
    keys.Nodup →
      wColSum keys (wId α) a = (if a ∈ keys then 1 else 0) := by
  -- 一意のキーリストである列の和を取った時、
  -- 和を取る列の列番号が keys に含まれていれば 1、含まれていなければ 0

  -- ヒント：
  --   * ex761（rowSum 版）＋ ex709（transposeで row/col 入替）を使うのが楽
  --   * あるいは keys で帰納して ex761 と同型に解いてもよい

  intro hNodup
  obtain hEx708 :=
    ex708 keys (wId α) a
  rw [←hEx708]
  obtain hEx761 :=
    ex761 keys a hNodup
  rw [ex766_pre]
  rw [hEx761]

-- 767：wGraph の colSum>0 ↔ ∃ a∈keys, f a = b
theorem ex767 (keys : List α) (f : α → β) (b : β) :
    wColSum keys (wGraph f) b > 0
      ↔
    ∃ a, a ∈ keys ∧ f a = b := by
  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  -- def relGraph (f : α → β) : Rel α β := fun a b => f a = b

  -- noncomputable def wGraph {α β : Type} (f : α → β) : WRel α β :=
  --   maskW (relGraph f)

  -- ヒント：ex712 を R := wGraph f に適用し、wGraph の定義を展開
  --dsimp [wColSum, wGraph]
  -- theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
  --     wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0 := by
  rw [ex712]
  constructor

  -- mp
  intro hExist
  obtain ⟨a1, ha_in, hR_pos⟩ := hExist
  exists a1
  dsimp [wGraph, maskW, relGraph] at hR_pos
  constructor
  exact ha_in
  by_cases h_eq : (f a1 = b)
  exact h_eq
  rw [if_neg h_eq] at hR_pos
  contradiction

  -- mpr
  intro hExist
  obtain ⟨a1, ha_in, h_eq⟩ := hExist
  exists a1
  dsimp [wGraph, maskW, relGraph]
  constructor
  exact ha_in
  rw [if_pos h_eq]
  exact Nat.zero_lt_one

-- 768：keys.Nodup かつ keys 上で f が単射なら、wGraph の colSum は 0/1
theorem ex768 (keys : List α) (f : α → β) (b : β) :
    keys.Nodup →
    (∀ a₁ a₂, a₁ ∈ keys → a₂ ∈ keys → f a₁ = f a₂ → a₁ = a₂) →
      wColSum keys (wGraph f) b
        =
      (if (∃ a, a ∈ keys ∧ f a = b) then 1 else 0) := by
  -- wColSum: y座標を決め、x軸方向に和を取る
  -- あるy座標bに対し、指定されたx座標で合計を取るとき、
  -- (単射のため、多くても一か所しか該当しないため、その合計の最大値は 1 である。)
  -- 右辺の値と一致する

  -- ヒント：
  --   * keys で帰納
  --   * 「∃a∈(x::xs), ...」の分解（head と tail）
  --   * 単射仮定で「同じ b に当たる a が 2 個は無い」を作る
  --   * 最後は Nat の計算（0/1）に帰着
  intro hNodup hInj
  dsimp [wColSum, wGraph, maskW, relGraph]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons a1 xs ih =>
    rw [List.nodup_cons] at hNodup
    obtain ⟨hK1_notin, hKs_nodup⟩ := hNodup
    dsimp [wsum]

    obtain ih2 := ih hKs_nodup
    clear ih

    by_cases h_eq : (f a1 = b)

    -- pos
    rw [if_pos h_eq]
    rw [←h_eq]
    rw [←h_eq] at ih2
    -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
    --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0)
    obtain hEx607 :=
      ex607 xs (fun a2 => if f a2 = f a1 then 1 else 0)

    have hAll_zero : ∀ (x : α), x ∈ xs → (if f x = f a1 then 1 else 0) = 0 := by
      intro x hx_in
      by_cases h_eq2 : (f x = f a1)

      -- pos
      -- x ∈ a1 :: xs
      obtain h1 := List.mem_cons_of_mem a1 hx_in
      obtain h_eq3 :=
        hInj x a1 h1 List.mem_cons_self h_eq2

      rw [←h_eq3] at hK1_notin
      contradiction

      -- neg
      rw [if_neg h_eq2]

    have hZero : 0 = wsum xs fun a => if f a = f a1 then 1 else 0 := by
      symm
      rw [ex607]
      exact hAll_zero

    rw [←hZero]
    rw [Nat.add_zero]

    have hExist :∃ a, a ∈ a1 :: xs ∧ f a = f a1 := by
      exists a1
      constructor
      apply List.mem_cons_self
      rfl

    rw [if_pos hExist]

    -- neg
    rw [if_neg h_eq]
    rw [Nat.zero_add]

    have h3 : (∃ a, a ∈ a1 :: xs ∧ f a = b) = (∃ a, a ∈ xs ∧ f a = b) := by
      -- h_eq : ¬f a1 = b
      apply propext
      constructor

      -- mp
      intro hExist
      obtain ⟨a3, h3_2, h3_3⟩ := hExist
      by_cases h_eq2 : (a3 = a1)

      -- pos
      rw [h_eq2] at h3_3
      contradiction

      -- neg
      exists a3
      obtain h3_4 :=
        List.mem_of_ne_of_mem h_eq2 h3_2
      constructor
      exact h3_4
      exact h3_3

      -- mpr
      intro hExist
      obtain ⟨a3, h3_2, h3_3⟩ := hExist
      exists a3
      constructor

      -- mpr.left
      apply List.mem_cons_of_mem
      exact h3_2

      -- mpr.right
      exact h3_3

    conv =>
      rhs
      arg 1
      rw [h3]

    rw [ih2]
    intro a4 a5 hContains1 hContins2 hEq
    apply hInj
    apply List.mem_cons_of_mem
    exact hContains1
    apply List.mem_cons_of_mem
    exact hContins2
    exact hEq

-- 769：keys.Nodup かつ keys が α 全体を含むなら、wId の rowSum は常に 1
theorem ex769 (keys : List α) (a : α) :
    keys.Nodup →
    (∀ x : α, x ∈ keys) →
      wRowSum keys (wId α) a = 1 := by
  -- wRowSum: x座標を決め、y軸方向に和を取る
  -- 単位行列について、いかなる列番号について、その縦方向のすべての和を取っても 1 になる

  -- ヒント：ex761 で (if a∈keys then 1 else 0) にして if_pos
  intro hNodup hAll
  obtain hEx761 :=
    ex761 keys a hNodup
  rw [hEx761]
  obtain hAll1 := hAll a
  rw [if_pos hAll1]

-- 770：keys.Nodup かつ keys が {f a} を全て含むなら、wGraph の rowSum は常に 1
theorem ex770 (keys : List β) (f : α → β) (a : α) :
    keys.Nodup →
    (∀ x : α, f x ∈ keys) →
      wRowSum keys (wGraph f) a = 1 := by
  -- 関数については、いかなるx座標についても、その縦方向のすべての和を取っても 1 になる

  -- ヒント：ex762 で if にして if_pos
  intro hNodup hAll
  obtain hEx762 :=
    ex762 keys f a hNodup
  rw [hEx762]
  obtain hAll1 := hAll a
  rw [if_pos hAll1]

--------------------------------------------------------------------------------
-- 771〜775：wId と row/col-sum / wCompList の相性
--------------------------------------------------------------------------------
-- 771：左から wId で縮約してから rowSum を取ると
--   “a ∈ keysα のときだけ通る” が rowSum レベルにも現れる
theorem ex771 (keysα : List α) (keysg : List γ) (R : WRel α γ) (a : α) :
    keysα.Nodup →
    wRowSum keysg (wCompList keysα (wId α) R) a
      =
    (if a ∈ keysα then wRowSum keysg R a else 0) := by
  -- 結局 keysαとkeysgでそれぞれ、行、列で絞り込んで和を取っているだけ

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- ヒント：
  --   * ex751 で rowSum を wsum(keysα) の形へ押し込む
  --   * keysα.Nodup のもとで、wId a b は「b=a のときだけ 1」なので、wsum が if で潰れる（keysα で帰納）
  --   * 必要なら ex761（rowSum keysα (wId α) a = if a∈keysα then 1 else 0）も補助に

  intro hNodup
  dsimp [wRowSum, wCompList, wId, maskW, relId]

  by_cases h_in : a ∈ keysα

  -- pos
  rw [if_pos h_in]

  -- theorem ex601 {X : Type} (xs : List X) (f g : X → Nat) :
  --     (∀ x, x ∈ xs → f x = g x) → wsum xs f = wsum xs g := by
  -- obtain hEx601 :=
  --   ex601 keysα
  obtain hEx601 :=
    ex601 keysg (fun b => wsum keysα fun b_1 => (if a = b_1 then 1 else 0) * R b_1 b) (fun b => R a b)
  apply hEx601
  clear hEx601

  intro g1 h_g1_in

  induction keysα with
  | nil =>
    dsimp [wsum]
    rw [List.mem_nil_iff] at h_in
    contradiction
  | cons b1 bs ih =>
    rw [List.nodup_cons] at hNodup
    obtain ⟨hK1_notin, hKs_nodup⟩ := hNodup
    dsimp [wsum]
    by_cases h_eq : (a = b1)
    -- pos
    rw [if_pos h_eq]
    rw [Nat.one_mul]
    rw [←h_eq]
    rw [←h_eq] at h_in
    rw [←h_eq] at hK1_notin

    have h_sum_zero : (wsum bs fun b_1 => (if a = b_1 then 1 else 0) * R b_1 g1) = 0 := by
      obtain hEx607 :=
        ex607 bs (fun b_1 => (if a = b_1 then 1 else 0) * R b_1 g1)
      rw [hEx607]
      intro x hx_in
      by_cases h_eq2 : (a = x)
      rw [←h_eq2] at hx_in
      contradiction
      rw [if_neg h_eq2]
      rw [Nat.zero_mul]

    rw [h_sum_zero]
    rw [Nat.add_zero]

    -- neg
    rw [if_neg h_eq]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    apply ih
    exact hKs_nodup
    apply List.mem_of_ne_of_mem
    exact h_eq
    exact h_in

  -- neg
  rw [if_neg h_in]

  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0)
  --    (wsum keysg fun b => wsum keysα fun b_1 => (if a = b_1 then 1 else 0) * R b_1 b) = 0
  obtain hEx607 :=
    ex607 keysg (fun b => wsum keysα fun b_1 => (if a = b_1 then 1 else 0) * R b_1 b)

  rw [hEx607]
  clear hEx607

  intro x hx_in
  obtain hEx607 :=
    ex607 keysα (fun b_1 => (if a = b_1 then 1 else 0) * R b_1 x)

  rw [hEx607]
  clear hEx607

  intro y hy_in

  by_cases h_eq : (a = y)
  rw [←h_eq] at hy_in
  contradiction

  rw [if_neg h_eq]
  rw [Nat.zero_mul]

-- 772：右から wId で縮約してから “同じ keys” で rowSum を取ると、rowSum は変わらない
theorem ex772 (keys : List β) (R : WRel α β) (a : α) :
    keys.Nodup →
    wRowSum keys (wCompList keys R (wId β)) a = wRowSum keys R a := by
  -- ヒント：
  --   * ex751 を (keysβ:=keys) (keysg:=keys) (R:=R) (S:=wId β) に適用（rowSum を押し込む）
  --   * ex761 で wRowSum keys (wId β) b = if b∈keys then 1 else 0（keys.Nodup が必要）
  --   * b∈keys なので if は常に 1、よって Σ_b R a b * 1 = Σ_b R a b
  intro hNodup

  -- theorem ex751 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (a : α) :
  --     wRowSum keysg (wCompList keysβ R S) a
  --       =
  --     wsum keysβ (fun b => R a b * wRowSum keysg S b) := by
  --    (wsum keys fun b => wsum keys fun b_1 => R a b_1 * if b_1 = b then 1 else 0) =
  --    wsum keys fun b => R a b
  obtain hEx751 :=
    ex751 keys keys R (wId β) a

  rw [hEx751]
  clear hEx751

  -- theorem ex761 (keys : List α) (a : α) :
  --     keys.Nodup →
  --       wRowSum keys (wId α) a = (if a ∈ keys then 1 else 0) := by
  -- (wsum keys fun b => R a b * wRowSum keys (wId β) b) = wRowSum keys R a
  obtain hEx761 :=
     ex761 keys

  conv =>
    lhs
    arg 2
    intro b
    rhs
    rw [ex761 keys b hNodup]

  clear hEx761

  -- theorem ex601 {X : Type} (xs : List X) (f g : X → Nat) :
  --     (∀ x, x ∈ xs → f x = g x) → wsum xs f = wsum xs g := by
  obtain hEx601 :=
    ex601 keys (fun b => R a b * (if b ∈ keys then 1 else 0)) (fun b => R a b)
  apply hEx601
  clear hEx601

  intro g1 h_g1_in
  rw [if_pos h_g1_in]
  rw [Nat.mul_one]

-- 773：左から wId で縮約してから “同じ keys” で colSum を取ると、colSum は変わらない
theorem ex773 (keys : List α) (R : WRel α β) (b : β) :
    keys.Nodup →
    wColSum keys (wCompList keys (wId α) R) b = wColSum keys R b := by
  -- ヒント：
  --   * ex752 を (keysα:=keys) (keysβ:=keys) (R:=wId α) (S:=R) に適用（colSum を押し込む）
  --   * ex766 で wColSum keys (wId α) a = if a∈keys then 1 else 0（keys.Nodup が必要）
  --   * a∈keys なので if は常に 1、よって Σ_a 1 * R a b = Σ_a R a b

  intro hNodup

  -- theorem ex752 (keysα : List α) (keysβ : List β)
  --     (R : WRel α β) (S : WRel β γ) (c : γ) :
  --     wColSum keysα (wCompList keysβ R S) c
  --       =
  --     wsum keysβ (fun b => wColSum keysα R b * S b c)

  -- wColSum keys (wCompList keys (wId α) R) b = wColSum keys R b

  obtain hEx752 :=
    ex752 keys keys (wId α) R b
  rw [hEx752]
  clear hEx752

  conv =>
    lhs
    arg 2
    intro a1
    rw [ex766 keys a1 hNodup]

  obtain hEx601 :=
    ex601 keys (fun a1 => (if a1 ∈ keys then 1 else 0) * R a1 b) (fun a1 => R a1 b)
  rw [hEx601]
  clear hEx601
  dsimp [wColSum]
  intro x hx_in
  rw [if_pos hx_in]
  rw [Nat.one_mul]

-- 774：もし keysβ 上のすべての b で S の rowSum（keysg 上）が 0 なら、
--      合成の rowSum も 0
theorem ex774 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    (∀ b, b ∈ keysβ → wRowSum keysg S b = 0) →
      wRowSum keysg (wCompList keysβ R S) a = 0 := by
  -- Sについて、keysβとkeysgの組み合わせの場所の値がすべて0ならば、
  -- RとSの合成についてもkeysβとkeysgの組み合わせで絞り込んで和をとるなら結果は0となる

  -- ヒント：
  --   * ex751 で `wRowSum keysg (wCompList keysβ R S) a` を書き換える
  --   * 右辺の wsum の各項が 0 になる（Nat.mul_zero）ことを示して ex711 で締める

  -- theorem ex751 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (a : α) :
  --     wRowSum keysg (wCompList keysβ R S) a
  --       =
  --     wsum keysβ (fun b => R a b * wRowSum keysg S b) := by
  obtain hEx751 :=
    ex751 keysβ keysg R S a
  rw [hEx751]
  clear hEx751
  intro hAll_zero
  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
  obtain hEx607 :=
    ex607 keysβ (fun b => R a b * wRowSum keysg S b)
  rw [hEx607]
  clear hEx607
  intro x hx_in
  obtain hAll_zero2 := hAll_zero x hx_in
  rw [hAll_zero2]
  rw [Nat.mul_zero]

-- 775：もし keysβ 上のすべての b で R の colSum（keysα 上）が 0 なら、
--      合成の colSum も 0
theorem ex775 (keysα : List α) (keysβ : List β)
    (R : WRel α β) (S : WRel β γ) (c : γ) :
    (∀ b, b ∈ keysβ → wColSum keysα R b = 0) →
      wColSum keysα (wCompList keysβ R S) c = 0 := by
  -- ヒント：
  --   * ex752 で `wColSum keysα (wCompList keysβ R S) c` を書き換える
  --   * 右辺の wsum の各項が 0 になる（Nat.zero_mul）ことを示して ex713 で締める

  -- theorem ex752 (keysα : List α) (keysβ : List β)
  --     (R : WRel α β) (S : WRel β γ) (c : γ) :
  --     wColSum keysα (wCompList keysβ R S) c
  --       =
  --     wsum keysβ (fun b => wColSum keysα R b * S b c) := by
  obtain hEx752 :=
    ex752 keysα keysβ R S c
  rw [hEx752]
  clear hEx752

  intro hAll_zero

  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
  obtain hEx607 :=
    ex607 keysβ (fun b => wColSum keysα R b * S b c)
  rw [hEx607]
  clear hEx607

  intro x hx_in
  obtain hAll_zero2 := hAll_zero x hx_in
  rw [hAll_zero2]
  rw [Nat.zero_mul]

--------------------------------------------------------------------------------
-- 776〜779：WSpec による keys-filtering と “2段 witness” の展開
--------------------------------------------------------------------------------

-- 776：spec を満たす R は、rowSum をとるとき keys を T でフィルタしても同じ
-- （T の外の重みが 0 なので落ちる）
theorem ex776 (keys : List β) (R : WRel α β) (T : Rel α β) (a1 : α) :
    WSpec R T →
      wRowSum keys R a1
        =
      wRowSum (keys.filter (fun b => decide (T a1 b))) R a1 := by
  -- ヒント：
  --   * keys で帰納法
  --   * head について `by_cases h : T a b` をして
  --     - h=true なら filter に残る
  --     - h=false なら WSpec から R a b = 0 なので、足しても変わらない
  dsimp [wRowSum, maskW, WSpec]
  intro hSpec
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b1 bs ih =>
    dsimp [List.filter]
    dsimp [wsum]
    by_cases hT : T a1 b1

    -- pos
    have h_decide : decide (T a1 b1) = true := by
      rw [decide_eq_true]
      exact hT
    rw [h_decide]
    dsimp
    clear h_decide
    obtain hEx502 :=
      ex502 b1 (List.filter (fun b => decide (T a1 b)) bs) (fun b => R a1 b)
    rw [hEx502]
    clear hEx502
    rw [Nat.add_left_cancel_iff]
    exact ih

    -- neg
    obtain hSpec2 := hSpec a1 b1 hT
    have h_decide : decide (T a1 b1) = false := by
      rw [decide_eq_false]
      exact hT
    rw [h_decide]
    clear h_decide
    dsimp
    rw [hSpec2]
    rw [Nat.zero_add]
    exact ih

-- 777：spec を満たす R は、colSum をとるとき keys を T でフィルタしても同じ
theorem ex777 (keys : List α) (R : WRel α β) (T : Rel α β) (b1 : β) :
    WSpec R T →
      wColSum keys R b1
        =
      wColSum (keys.filter (fun a => decide (T a b1))) R b1 := by
  -- ヒント：ex776 の colSum 版（keys で帰納するのが早い）

  dsimp [wColSum, maskW, WSpec]
  intro hSpec
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons a1 as ih =>
    dsimp [List.filter]
    dsimp [wsum]
    by_cases hT : T a1 b1

    -- pos
    have h_decide : decide (T a1 b1) = true := by
      rw [decide_eq_true]
      exact hT
    rw [h_decide]
    dsimp
    clear h_decide
    obtain hEx502 :=
      ex502 a1 (List.filter (fun a => decide (T a b1)) as) (fun a => R a b1)
    rw [hEx502]
    clear hEx502
    rw [Nat.add_left_cancel_iff]
    exact ih

    -- neg
    obtain hSpec2 := hSpec a1 b1 hT
    have h_decide : decide (T a1 b1) = false := by
      rw [decide_eq_false]
      exact hT
    rw [h_decide]
    clear h_decide
    dsimp
    rw [hSpec2]
    rw [Nat.zero_add]
    exact ih

-- 778：入力側/出力側がそれぞれ spec を持つなら、
--      合成 wCompList の rowSum も “合成 spec” でフィルタしてよい
theorem ex778 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : Rel α β) (U : Rel β γ) (a : α) :
    WSpec R T → WSpec S U →
      wRowSum keysg (wCompList keysβ R S) a
        =
      wRowSum (keysg.filter (fun c => decide (relCompList keysβ T U a c)))
        (wCompList keysβ R S) a := by
  -- ヒント：
  --   * ex746：WSpec R T, WSpec S U ⇒ WSpec (wCompList keysβ R S) (relCompList keysβ T U)
  --   * その WSpec を ex776 に食わせるだけ
  intro hSpecRT hSpecSU

  -- theorem ex746 (keys : List β) (R : WRel α β) (S : WRel β γ)
  --     (T : Rel α β) (U : Rel β γ) :
  --     WSpec R T → WSpec S U → WSpec (wCompList keys R S) (relCompList keys T U) := by
  obtain hEx746 :=
    ex746 keysβ R S T U hSpecRT hSpecSU

  -- theorem ex776 (keys : List β) (R : WRel α β) (T : Rel α β) (a1 : α) :
  --     WSpec R T →
  --       wRowSum keys R a1
  --         =
  --       wRowSum (keys.filter (fun b => decide (T a1 b))) R a1 := by
  obtain hEx776 :=
    ex776 keysg (wCompList keysβ R S) (relCompList keysβ T U) a hEx746

  exact hEx776

-- 779：rowSum>0 を “2段 witness（b と c）” まで展開
theorem ex779 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (a : α) :
    wRowSum keysg (wCompList keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ R a b > 0 ∧ S b c > 0 := by
  -- ヒント：
  --   * ex753 で `∃ b∈keysβ ∧ R a b>0 ∧ wRowSum keysg S b>0`
  --   * さらに ex710（rowSum>0 ↔ ∃c∈keysg, S b c>0）で分解
  --   * 仕上げは ∃ の並べ替え

  -- theorem ex753 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (a : α) :
  --     wRowSum keysg (wCompList keysβ R S) a > 0
  --       ↔
  --     ∃ b, b ∈ keysβ ∧ R a b > 0 ∧ wRowSum keysg S b > 0 := by
  obtain hEx753 :=
    ex753 keysβ keysg R S a

  rw [hEx753]
  clear hEx753

  -- theorem ex710 (keys : List β) (R : WRel α β) (a : α) :
  --     wRowSum keys R a > 0 ↔ ∃ b, b ∈ keys ∧ R a b > 0 := by
  constructor

  -- mp
  intro hExist1
  obtain ⟨b1, hb_in, hR_pos, hRowSum_pos⟩ := hExist1

  obtain hEx710 :=
    ex710 keysg S b1
  rw [hEx710] at hRowSum_pos
  clear hEx710

  obtain ⟨c1, hc_in, hS_pos⟩ := hRowSum_pos
  exists b1
  constructor
  exact hb_in
  exists c1

  -- mpr
  intro hExist2
  obtain ⟨b1, hb_in, c1, hc_in, hR_pos, hS_pos⟩ := hExist2
  exists b1
  constructor
  exact hb_in
  constructor
  exact hR_pos
  obtain hEx710 :=
    ex710 keysg S b1
  rw [hEx710]
  exists c1

--------------------------------------------------------------------------------
-- 780：wCompList の結合則（有限和の並べ替え / weighted 版）
--------------------------------------------------------------------------------

-- 780：wCompList の結合（keysβ と keysg の 2 段 witness の並べ替え）
theorem ex780 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wCompList keysg (wCompList keysβ R S) T
      =
    wCompList keysβ R (wCompList keysg S T) := by
  -- ヒント：
  --   * funext a d; dsimp [wCompList]
  --   * どちらも “二重和（Σg Σb ...）” なので、
  --     Nat.add_assoc / Nat.add_comm / Nat.mul_add / Nat.add_mul / Nat.mul_assoc で整理する
  --   * すすめ方：keysg で帰納して、途中で必要なら keysβ での補助補題
  --       `wsum keysβ f * t = wsum keysβ (fun b => f b * t)` をその場で作る
  funext a1 s1
  dsimp [wCompList, maskW]

  obtain wsum_comm2 :=
    wsum_comm keysg keysβ (fun b b_1 => R a1 b_1 * S b_1 b * T b s1)

  conv =>
    lhs
    arg 2
    intro b
    rw [ex538]

  rw [wsum_comm2]

  conv =>
    rhs
    arg 2
    intro b
    rw [Nat.mul_comm]
    rw [ex538]
    arg 2
    intro b_1
    rw [Nat.mul_comm]
    rw [←Nat.mul_assoc]

end TL
