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

  -- def WSpec {α β : Type} (R : WRel α β) (T : Rel α β) : Prop :=
  --   ∀ a b, ¬ T a b → R a b = 0

  --   ∀ a b, ¬ T a b → (maskW M) a b = 0
  --   ∀ a b, ¬ T a b → ¬ M a b
  --   ∀ a b, M a b  → T a b

  -- ヒント：
  --   * ex691（WSpec ↔ wSupp ⊆ T）
  --   * ex613（wSupp (maskW M) = M）

  -- theorem ex691 (R : WRel α β) (T : Rel α β) :
  --     WSpec R T ↔ (wSupp R ⊆ T) := by
  obtain hEx691 :=
    ex691 (maskW M) T

  rw [hEx691]
  clear hEx691

  -- theorem ex613 (M : Rel α β) :
  --     wSupp (maskW M) = M := by
  obtain hEx613 :=
    ex613 M
  rw [hEx613]

-- 782：0/1 行列同士の WLe は、元の関係の包含と同値
-- （0/1 なので「≤」は「1 なら右も 1」を意味する）
theorem ex782 (M N : Rel α β) :
    WLe (maskW M) (maskW N) ↔ (M ⊆ N) := by
  -- def WLe {α β : Type} (R S : WRel α β) : Prop :=
  --   ∀ a b, R a b ≤ S a b

  --   ∀ a b, (maskW M) a b ≤ (maskW N) a b
  --   ∀ a b, M a b → N a b

  -- ヒント：
  --   * dsimp [WLe, maskW]
  --   * by_cases (M a b), by_cases (N a b)
  --   * Nat.succ_le_succ_iff / Nat.not_succ_le_zero などでも可

  dsimp [WLe, maskW]
  constructor

  -- mp
  intro hWLe a1 b1 hMa1b1

  obtain hWLe1 :=
    hWLe a1 b1

  rw [if_pos hMa1b1] at hWLe1
  by_cases hNa1b1 : N a1 b1
  -- pos
  exact hNa1b1
  rw [if_neg hNa1b1] at hWLe1
  contradiction

  -- mpr
  intro hMN a2 b2
  rw [RelLe] at hMN
  by_cases hMa2b2 : M a2 b2

  -- pos
  rw [if_pos hMa2b2]
  obtain hMN2 := hMN a2 b2 hMa2b2
  rw [if_pos hMN2]
  apply Nat.le_refl

  -- neg
  rw [if_neg hMa2b2]
  by_cases hNa2b2 : N a2 b2

  -- pos
  rw [if_pos hNa2b2]
  apply Nat.zero_le

  -- neg
  rw [if_neg hNa2b2]
  apply Nat.le_refl


-- 783：0/1 行列の Hadamard 積は論理積（∧）に対応する（重みレベルで完全一致）
theorem ex783 (M N : Rel α β) :
    wMul (maskW M) (maskW N) = maskW (relMul M N) := by
  -- 論理演算と数値演算をおきかえているだけ
  -- def wMul {α β : Type} (R S : WRel α β) : WRel α β :=
  --   fun a b => R a b * S a b
  --
  -- def relMul (R S : Rel α β) : Rel α β :=
  --   fun a b => R a b ∧ S a b

  -- ヒント：by classical; funext a b; by_cases hM : M a b <;> by_cases hN : N a b <;>
  --          simp [wMul, maskW, relMul, hM, hN]

  funext a1 b1
  dsimp [wMul, maskW, relMul]
  by_cases hMa1b1 : M a1 b1
  -- pos
  rw [if_pos hMa1b1]
  rw [Nat.one_mul]
  by_cases hNa1b1 : N a1 b1
  -- pos
  rw [if_pos hNa1b1]
  rw [if_pos ⟨hMa1b1, hNa1b1⟩]
  -- neg
  rw [if_neg hNa1b1]
  rw [if_neg]
  intro hFalse1
  obtain ⟨hM1, hN1⟩ := hFalse1
  apply hNa1b1
  apply hN1
  -- neg
  rw [if_neg hMa1b1]
  rw [Nat.zero_mul]
  rw [if_neg]
  intro hFalse2
  obtain ⟨hM2, hN2⟩ := hFalse2
  apply hMa1b1
  apply hM2

-- 784：0/1 行列を関係 N で mask するのは、関係の ∧ を取って 0/1 化するのと同じ
theorem ex784 (M N : Rel α β) :
    wMask (maskW M) N = maskW (relMul M N) := by
  -- 論理演算を数値演算に置き換えているだけ

  -- ヒント：
  --   * ex725（wMask R M = wMul R (maskW M)）
  --   * ex783 を使う

  obtain hEx725 :=
    ex725 (maskW M) N
  rw [hEx725]
  clear hEx725

  obtain hEx783 :=
    ex783 M N
  rw [hEx783]

-- 785：transpose は maskW と可換（関係側も transpose する）
theorem ex785 (M : Rel α β) :
    wTrans (maskW M) = maskW (relTrans M) := by
  -- 数値化前に転置するのと、数値化後に転置するのは同じ

  -- ヒント：by classical; funext b a; simp [wTrans, maskW, relTrans]
  funext b1 a1
  dsimp [wTrans, maskW, relTrans]

--------------------------------------------------------------------------------
-- 786〜790：wCountComp（「witness の個数」）と relCompList（存在）
--------------------------------------------------------------------------------

-- 786：wCountComp の展開：積の 0/1 をまとめて ∧ の 0/1 にできる
--   (if M then 1 else 0) * (if N then 1 else 0) = if (M ∧ N) then 1 else 0
theorem ex786 (keys : List β) (R : Rel α β) (S : Rel β γ) (a : α) (c : γ) :
    wCountComp keys R S a c
      =
    wsum keys (fun b => if (R a b ∧ S b c) then 1 else 0) := by
  -- ヒント：
  --   * dsimp [wCountComp, wCompList, maskW]
  --   * keys で帰納
  --   * 各 b で by_cases (R a b) と by_cases (S b c)
  --   * Nat.mul_one / Nat.mul_zero / Nat.zero_mul
  dsimp [wCountComp, wCompList, maskW]
  induction keys with
  | nil =>
    rw [wsum]
    rw [wsum]
  | cons b1 bs ih =>
    rw [wsum]
    rw [wsum]
    by_cases hRab1 : R a b1
    -- pos
    rw [if_pos hRab1]
    rw [Nat.one_mul]
    by_cases hSbc1 : S b1 c
    -- pos
    rw [if_pos hSbc1]
    rw [if_pos ⟨hRab1, hSbc1⟩]
    rw [ih]
    -- neg
    rw [if_neg hSbc1]
    rw [Nat.zero_add]
    rw [if_neg]
    rw [Nat.zero_add]
    exact ih
    -- neg
    intro hRab1_neg
    obtain ⟨hRab2, hSbc2⟩ := hRab1_neg
    apply hSbc1
    exact hSbc2

    -- neg
    rw [if_neg hRab1]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    rw [if_neg]
    rw [Nat.zero_add]
    exact ih

    intro hRab1_Sb1c
    obtain ⟨hRab2, hSbc2⟩ := hRab1_Sb1c
    apply hRab1
    exact hRab2

-- 787：support（>0）は「witness が存在する」だけを見るので relCompList に一致
-- （重みは “数” だが、>0 は “存在” に潰れる）
theorem ex787 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    wSupp (wCountComp keys R S) = relCompList keys R S := by
  -- 0より大きければ、条件に該当しているものは少なくとも一つはある
  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- ヒント：
  --   * ex621（wSupp (wCompList keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)）
  --   * QK := maskW R, KV := maskW S
  --   * ex613（wSupp (maskW M) = M）

  dsimp [wCountComp]
  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)
  --     wSupp (wCountComp keys R S) = relCompList keys R S

  -- def attnWRel {α β γ : Type} (keys : List β) (QK : WRel α β) (KV : WRel β γ) : WRel α γ :=
  --   wCompList keys QK KV

  -- theorem ex613 (M : Rel α β) :
  --     wSupp (maskW M) = M
  obtain hEx613_R :=
    ex613 R
  obtain hEx613_S :=
    ex613 S
  obtain hEx621 :=
    ex621 keys (maskW R) (maskW S)
  rw [hEx613_R, hEx613_S] at hEx621
  rw [←hEx621]
  clear hEx613_R hEx613_S hEx621
  rw [attnWRel]

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
  -- aとcの組み合わせに対しR a bとS b cを満たすbは最大一つしかない条件

  -- ヒント：
  --   * funext a c
  --   * ex786 で wsum (if (R a b ∧ S b c) then 1 else 0) の形へ
  --   * keys.Nodup と “witness 一意性” から、true になる b は高々 1 個
  --   * ∃ があるなら wsum は 1、ないなら 0
  --   * RHS は maskW（= if ∃ witness then 1 else 0）
  intro hNodup
  intro hUnique

  funext a1 c1
  obtain hEx786 :=
    ex786 keys R S a1 c1
  rw [hEx786]
  clear hEx786
  dsimp [maskW, relCompList]

  by_cases h_ex : ∃ b, b ∈ keys ∧ R a1 b ∧ S b c1

  -- pos
  have h_one : (wsum keys fun b => if R a1 b ∧ S b c1 then 1 else 0) = 1 := by
    obtain ⟨b_ex, hIn, hR, hS⟩ := h_ex
    have h_eq_sum : (wsum keys fun b => if R a1 b ∧ S b c1 then 1 else 0) =
                    wRowSum keys (wId β) b_ex := by
      dsimp [wRowSum, wId, maskW, relId]
      apply ex601
      intro b hb
      by_cases h_eq : b = b_ex
      · rw [h_eq]
        rw [if_pos (And.intro hR hS)]
        rw [if_pos rfl]
      · have h_rhs : (if b_ex = b then 1 else 0) = 0 := by
          apply if_neg
          intro h
          exact h_eq h.symm
        rw [h_rhs]
        apply if_neg
        intro h_and
        have h_cont : b = b_ex := hUnique a1 c1 b b_ex hb hIn h_and.1 h_and.2 hR hS
        exact h_eq h_cont
    rw [h_eq_sum]
    rw [ex761 keys b_ex hNodup]
    rw [if_pos hIn]

  rw [h_one]

  rw [if_pos h_ex]

  -- neg
  rw [if_neg h_ex]
  rw [ex607]
  intro b1 hIn
  apply if_neg
  intro h_and
  obtain ⟨hR, hS⟩ := h_and
  apply h_ex
  exists b1

-- 789：graph（左が関数）なら witness は自動的に一意 → wCountComp は 0/1 で “行選択”
-- （keys.Nodup で重複カウントが無い前提）
theorem ex789 (keys : List β) (f : α → β) (S : Rel β γ) :
    keys.Nodup →
      wCountComp keys (relGraph f) S
        =
      maskW (fun a c => f a ∈ keys ∧ S (f a) c) := by

  -- def relGraph (f : α → β) : Rel α β := fun a b => f a = b
  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- ヒント：
  --   * ex788 を R:=relGraph f に適用（witness の一意性は自明）
  --   * relCompList keys (relGraph f) S a c は「∃b∈keys, f a = b ∧ S b c」
  --     なので b を f a に潰して (f a ∈ keys ∧ S (f a) c) に整理

  -- theorem ex788 (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     keys.Nodup →
  --     (∀ a c b₁ b₂,
  --         b₁ ∈ keys → b₂ ∈ keys →
  --         R a b₁ → S b₁ c →
  --         R a b₂ → S b₂ c →
  --         b₁ = b₂) →
  --       wCountComp keys R S = maskW (relCompList keys R S) := by

  intro hNodup
  funext a1 c1
  obtain hEx788 :=
    ex788 keys (relGraph f) S hNodup
  rw [hEx788]
  clear hEx788

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  dsimp [maskW]
  dsimp [relCompList, relGraph]
  by_cases h_in : (∃ b, b ∈ keys ∧ f a1 = b ∧ S b c1)

  -- pos
  rw [if_pos h_in]
  obtain ⟨b_ex, hIn, hEq, hS⟩ := h_in
  rw [hEq]
  rw [if_pos ⟨hIn, hS⟩]

  -- neg
  rw [if_neg h_in]
  have h_no : ¬ (f a1 ∈ keys ∧ S (f a1) c1) := by
    intro h1
    obtain ⟨hIn2, hS2⟩ := h1
    apply h_in
    exists (f a1)
  rw [if_neg h_no]

  --
  intro a2 c2 b1 b2 hContains1 hContains2 hRelGraph1 hS1 hRelGraph2 hS2
  rw [relGraph] at hRelGraph1 hRelGraph2
  rw [←hRelGraph1]
  rw [←hRelGraph2]

-- 790：graph-graph なら “関数合成 + keys マスク” の 0/1 版になる
theorem ex790 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
      wCountComp keys (relGraph f) (relGraph g)
        =
      maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- ヒント：
  --   * ex789 に S := relGraph g を入れる
  --   * relGraph g (f a) c は g (f a) = c

  intro hNodup
  -- theorem ex789 (keys : List β) (f : α → β) (S : Rel β γ) :
  --     keys.Nodup →
  --       wCountComp keys (relGraph f) S
  --         =
  --       maskW (fun a c => f a ∈ keys ∧ S (f a) c)
  obtain hEx789 :=
    ex789 keys f (relGraph g) hNodup
  rw [hEx789]
  clear hEx789

  dsimp [relGraph]

--------------------------------------------------------------------------------
-- 791〜795：wCountComp を row/col-sum で観察（“2段 witness” と行選択）
--------------------------------------------------------------------------------

-- 791：rowSum>0（到達）が “b と c の 2段 witness” に分解できる（Rel 版）
theorem ex791 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (a : α) :
    wRowSum keysg (wCountComp keysβ R S) a > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ c, c ∈ keysg ∧ R a b ∧ S b c := by
  -- ヒント：
  --   * ex710（rowSum>0 ↔ ∃c∈keysg, (..) a c >0）
  --   * (..) := wCountComp keysβ R S
  --   * ex787 で support を relCompList に落として、∃ の並べ替え

  --dsimp [wCountComp]

  -- theorem ex710 (keys : List β) (R : WRel α β) (a : α) :
  --     wRowSum keys R a > 0 ↔ ∃ b, b ∈ keys ∧ R a b > 0
  obtain hEx710 :=
    ex710 keysg (wCountComp keysβ R S) a
  rw [hEx710]
  clear hEx710

  -- theorem ex787 (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     wSupp (wCountComp keys R S) = relCompList keys R S

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- def relCompList {α β γ : Type} (keys : List β) (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  --   fun a c => ∃ b, b ∈ keys ∧ R a b ∧ S b c

  have hEx787 : ∀ a c, wSupp (wCountComp keysβ R S) a c = (relCompList keysβ R S) a c := by
    intro a2 c2
    rw [ex787 keysβ R S]

  conv =>
    lhs
    arg 1
    intro g1
    rhs
    apply hEx787 a g1

  clear hEx787

  dsimp [relCompList]
  constructor
  -- mp
  intro h_exists
  obtain ⟨c1, hIn_c1, hRelComp⟩ := h_exists
  obtain ⟨b1, hIn_b1, hR, hS⟩ := hRelComp
  exists b1
  constructor
  exact hIn_b1
  exists c1

  intro h_exists2
  obtain ⟨b2, hIn_b2, ⟨c2, hIn_c2, hR2, hS2⟩⟩ := h_exists2
  exists c2
  constructor
  exact hIn_c2
  exists b2

-- 792：colSum>0（到達）が “a と b の 2段 witness” に分解できる（Rel 版）
theorem ex792 (keysα : List α) (keysβ : List β)
    (R : Rel α β) (S : Rel β γ) (c : γ) :
    wColSum keysα (wCountComp keysβ R S) c > 0
      ↔
    ∃ b, b ∈ keysβ ∧ ∃ a, a ∈ keysα ∧ R a b ∧ S b c := by
  -- ヒント：
  --   * ex712（colSum>0 ↔ ∃a∈keysα, (..) a c >0）
  --   * ex787 で relCompList にして整理

  -- theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
  --     wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0
  obtain hEx712 :=
    ex712 keysα (wCountComp keysβ R S) c

  rw [hEx712]
  clear hEx712

  -- theorem ex787 (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     wSupp (wCountComp keys R S) = relCompList keys R S
  have hEx787 : ∀ a c, wSupp (wCountComp keysβ R S) a c = (relCompList keysβ R S) a c := by
    intro a2 c2
    rw [ex787 keysβ R S]

  conv =>
    lhs
    arg 1
    intro a1
    rhs
    apply hEx787 a1 c

  clear hEx787

  dsimp [relCompList]
  constructor

  -- mp
  intro h_exists
  obtain ⟨a1, hIn_a1, hRelComp⟩ := h_exists
  obtain ⟨b1, hIn_b1, hR, hS⟩ := hRelComp
  exists b1
  constructor
  exact hIn_b1
  exists a1

  -- mpr
  intro h_exists2
  obtain ⟨b2, hIn_b2, ⟨a2, hIn_a2, hR2, hS2⟩⟩ := h_exists2
  exists a2
  constructor
  exact hIn_a2
  exists b2

-- 793：rowSum を押し込む（Rel 版）：到達先 c を全て足すと “(b,c) の組の個数” を数える
--   Σ_c #{b | R a b ∧ S b c} = Σ_b ( [R a b] * Σ_c [S b c] )
theorem ex793 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (a : α) :
    wRowSum keysg (wCountComp keysβ R S) a
      =
    wsum keysβ (fun b => (if R a b then 1 else 0) * wRowSum keysg (maskW S) b) := by
  -- ヒント：
  --   * ex751 を QK := maskW R, KV := maskW S に適用
  --   * wCountComp の定義へ戻す

  rw [wCountComp]

  -- theorem ex751 (keysβ : List β) (keysg : List γ)
  --     (R : WRel α β) (S : WRel β γ) (a : α) :
  --     wRowSum keysg (wCompList keysβ R S) a
  --       =
  --     wsum keysβ (fun b => R a b * wRowSum keysg S b)
  obtain hEx751 :=
    ex751 keysβ keysg (maskW R) (maskW S) a
  rw [hEx751]
  clear hEx751

  induction keysβ with
  | nil =>
    rw [wsum]
    rw [wsum]
  | cons b1 bs ih =>
    rw [wsum]
    rw [wsum]
    rw [maskW]
    by_cases hRab1 : R a b1

    -- pos
    rw [if_pos hRab1]
    rw [Nat.one_mul]
    rw [Nat.add_left_cancel_iff]
    rw [ih]

    -- neg
    rw [if_neg hRab1]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    rw [Nat.zero_add]
    rw [ih]

-- 794：colSum を押し込む（Rel 版）
theorem ex794 (keysα : List α) (keysβ : List β)
    (R : Rel α β) (S : Rel β γ) (c : γ) :
    wColSum keysα (wCountComp keysβ R S) c
      =
    wsum keysβ (fun b => wColSum keysα (maskW R) b * (if S b c then 1 else 0)) := by
  -- ヒント：ex752 を QK := maskW R, KV := maskW S に適用して整理

  -- theorem ex752 (keysα : List α) (keysβ : List β)
  --     (R : WRel α β) (S : WRel β γ) (c : γ) :
  --     wColSum keysα (wCompList keysβ R S) c
  --       =
  --     wsum keysβ (fun b => wColSum keysα R b * S b c) := by
  obtain hEx752 :=
    ex752 keysα keysβ (maskW R) (fun b c => if S b c then 1 else 0) c
  conv =>
    rhs
    rw [←hEx752]
  clear hEx752

  dsimp [wColSum, wCompList, wCountComp, maskW]


-- 795：graph を左に置くと “行選択” になる：rowSum も if で表せる（重み版）
theorem ex795 (keys : List β) (keysg : List γ)
    (f : α → β) (W : WRel β γ) (a : α) :
    keys.Nodup →
      wRowSum keysg (wCompList keys (wGraph f) W) a
        =
      (if f a ∈ keys then wRowSum keysg W (f a) else 0) := by
  -- ヒント：
  --   * ex727（wCompList keys (wGraph f) W = wMask (fun a c => W (f a) c) (f a∈keys)）
  --   * それを wRowSum して、by_cases (f a ∈ keys)
  --   * true 側は mask が全部 1 なので wRowSum がそのまま
  --   * false 側は全項 0 → rowSum=0（ex711）

  -- theorem ex727 (keys : List β) (f : α → β) (S : WRel β γ) :
  --     keys.Nodup →
  --       wCompList keys (wGraph f) S
  --         =
  --       wMask (fun a c => S (f a) c) (fun a _ => f a ∈ keys) := by
  obtain hEx727 :=
    ex727 keys f W

  intro hNodup
  rw [hEx727 hNodup]
  clear hEx727

  dsimp [wRowSum, wMask, maskW]
  by_cases h_in : f a ∈ keys
  -- pos
  rw [if_pos h_in]
  conv =>
    lhs
    arg 2
    intro h
    rw [Nat.mul_one]

  rw [if_pos h_in]

  -- neg
  rw [if_neg h_in]
  conv =>
    lhs
    arg 2
    intro h
    rw [Nat.mul_zero]
  conv =>
    rhs
    rw [if_neg h_in]

  induction keysg with
  | nil =>
    rw [wsum]
  | cons c1 cs ih =>
    rw [wsum]
    rw [Nat.zero_add]
    rw [ih]

end TL
