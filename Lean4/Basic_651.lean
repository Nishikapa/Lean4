--------------------------------------------------------------------------------
-- Basic_651.lean
-- 演習問題 651〜700（keys付きRel合成の代数 / transpose / Hadamard / graph / multi-head / spec）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 601〜650 は Basic_601 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_601

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wTrans / wMul / wScale / wId / wGraph / WSpec）
--------------------------------------------------------------------------------

-- WRel の transpose（引数をひっくり返す）
def wTrans {α β : Type} (R : WRel α β) : WRel β α :=
  fun b a => R a b

-- WRel の要素積（Hadamard 積）
def wMul {α β : Type} (R S : WRel α β) : WRel α β :=
  fun a b => R a b * S a b

-- スカラー倍（Nat）
def wScale {α β : Type} (t : Nat) (R : WRel α β) : WRel α β :=
  fun a b => t * R a b

-- WRel の（0/1）恒等（maskW を使うので noncomputable）
noncomputable def wId (X : Type) : WRel X X :=
  maskW (relId X)

-- 関数 f の graph を 0/1 の WRel にしたもの（maskW を使うので noncomputable）
noncomputable def wGraph {α β : Type} (f : α → β) : WRel α β :=
  maskW (relGraph f)

-- 「仕様 T の外は重み 0」という意味の weighted-spec
def WSpec {α β : Type} (R : WRel α β) (T : Rel α β) : Prop :=
  ∀ a b, ¬ T a b → R a b = 0

--------------------------------------------------------------------------------
-- 651〜660：relCompList / relInKeys の “代数”
--------------------------------------------------------------------------------

-- 651：空 keys の relCompList は空関係
theorem ex651 (R : Rel α β) (S : Rel β γ) :
    relCompList ([] : List β) R S = (relBot α γ) := by

  funext a1 g1
  dsimp [relCompList, relBot]
  apply propext
  constructor
  intro h
  obtain ⟨b, hb, hR, hS⟩ := h
  cases hb
  intro h
  contradiction

-- 652：cons 展開（head で当たるか tail に流す）
theorem ex652 (b : β) (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList (b :: keys) R S
      =
    relAdd (fun a c => R a b ∧ S b c) (relCompList keys R S) := by

  funext a1 g1
  dsimp [relCompList, relAdd]
  apply propext
  constructor

  -- mp
  intro h
  obtain ⟨b1, hb1, hR, hS⟩ := h
  by_cases hEq : b = b1

  -- pos
  left
  rw [hEq]
  constructor

  -- pos.left
  exact hR
  -- pos.right
  exact hS

  -- neg
  right

  have hEq2 : ¬ b1 = b := by
    intro hEq2_1
    rw [hEq2_1] at hEq
    contradiction

  obtain hb2 :=
    List.mem_of_ne_of_mem (hEq2) hb1

  exists b1

  -- mpr
  intro h
  obtain ⟨hR1, hS1⟩ | ⟨b1, hContains, hR2, hS2⟩ := h

  -- mpr.inl
  exists b
  constructor

  -- mpr.inl.left
  apply List.mem_cons_self

  -- mpr.inl.right
  constructor
  -- mpr.inl.right.left
  exact hR1
  -- mpr.inl.right.right
  exact hS1
  -- mpr.inr
  exists b1
  constructor
  -- mpr.inr.left
  apply List.mem_cons_of_mem
  exact hContains
  -- mpr.inr.right
  constructor
  -- mpr.inr.right.left
  exact hR2
  -- mpr.inr.right.right
  exact hS2

-- 653：singleton keys の relCompList
theorem ex653 (b : β) (R : Rel α β) (S : Rel β γ) :
    relCompList [b] R S = (fun a c => R a b ∧ S b c) := by

  -- theorem ex652 (b : β) (keys : List β) (R : Rel α β) (S : Rel β γ) :
  --     relCompList (b :: keys) R S
  --       =
  --     relAdd (fun a c => R a b ∧ S b c) (relCompList keys R S)
  obtain hEx652 :=
    ex652 b [] R S
  rw [hEx652]

  funext a1 g1
  dsimp [relAdd, relCompList]
  apply propext
  constructor
  intro h1
  obtain ⟨hR1, hS1⟩ | ⟨b1,hContains,hR2,hS2⟩ := h1
  constructor
  exact hR1
  exact hS1
  contradiction
  intro h2
  obtain ⟨hR3, hS3⟩ := h2
  left
  constructor
  exact hR3
  exact hS3

-- 654：append 分解（keys を 2 ブロックに分けると OR）
theorem ex654 (keys1 keys2 : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList (keys1 ++ keys2) R S
      =
    relAdd (relCompList keys1 R S) (relCompList keys2 R S) := by

  funext a1 g1
  apply propext
  constructor
  intro hRelCompList
  obtain ⟨b1, hContains1, hR1, hS1⟩ := hRelCompList
  by_cases hInKeys1 : b1 ∈ keys1
  left
  exists b1
  have hInKeys2 : b1 ∈ keys2 := by
    rw [List.mem_append] at hContains1
    obtain hContainsLeft | hContainsRight := hContains1
    contradiction
    exact hContainsRight
  right
  exists b1
  dsimp [relCompList, relAdd]
  intro h2
  obtain ⟨b2, hContains2,hR2,hS2⟩ | ⟨b3, hContains3,hR3,hS3⟩ := h2
  exists b2
  constructor
  apply List.mem_append_left
  exact hContains2
  constructor
  exact hR2
  exact hS2
  exists b3
  constructor
  apply List.mem_append_right
  exact hContains3
  constructor
  exact hR3
  exact hS3

-- 655：keys の単調性（候補が増えるほど relCompList は増える）
theorem ex655 (keys keys' : List β) (R : Rel α β) (S : Rel β γ) :
    (∀ b, b ∈ keys → b ∈ keys') →
      relCompList keys R S ⊆ relCompList keys' R S := by

  intro h1 a1 g1 hRelCompList1
  obtain ⟨b1, hContains1, hR1, hS1⟩ := hRelCompList1

  obtain h2 :=
    h1 b1 hContains1

  exists b1

-- 656：R/S の単調性（R⊆R', S⊆S' なら relCompList も ⊆）
theorem ex656 (keys : List β) (R R' : Rel α β) (S S' : Rel β γ) :
    (R ⊆ R') → (S ⊆ S') →
      relCompList keys R S ⊆ relCompList keys R' S' := by

  intro hRSub hSSub a1 g1 hRelCompList1
  obtain ⟨b1, hContains1, hR1, hS1⟩ := hRelCompList1
  exists b1
  constructor
  exact hContains1
  constructor
  apply hRSub
  exact hR1
  apply hSSub
  exact hS1

-- 657：左の和（∨）に分配：relCompList keys (R+R') S = ...
theorem ex657 (keys : List β) (R R' : Rel α β) (S : Rel β γ) :
    relCompList keys (relAdd R R') S
      =
    relAdd (relCompList keys R S) (relCompList keys R' S) := by

  funext a1 g1
  apply propext
  constructor

  intro hRelCompList1
  obtain ⟨b1, hContains1, hR1 | hR2, hS1⟩ := hRelCompList1
  left
  exists b1
  right
  exists b1

  intro hRelAdd1
  obtain ⟨b1, hContains1, hR1, hS1⟩ | ⟨b2, hContains2, hR2, hS2⟩ := hRelAdd1
  exists b1
  constructor
  exact hContains1
  constructor
  left
  exact hR1
  exact hS1
  exists b2
  constructor
  exact hContains2
  constructor
  right
  exact hR2
  exact hS2

-- 658：右の和（∨）に分配：relCompList keys R (S+S') = ...
theorem ex658 (keys : List β) (R : Rel α β) (S S' : Rel β γ) :
    relCompList keys R (relAdd S S')
      =
    relAdd (relCompList keys R S) (relCompList keys R S') := by

  funext a1 g1
  apply propext
  constructor
  intro hRelCompList1
  obtain ⟨b1, hContains1, hR1, hS1 | hS2⟩ := hRelCompList1
  left
  exists b1
  right
  exists b1
  intro hRelAdd1
  obtain ⟨b1, hContains1, hR1, hS1⟩ | ⟨b2, hContains2, hR2, hS2⟩ := hRelAdd1
  exists b1
  constructor
  exact hContains1
  constructor
  exact hR1
  left
  exact hS1
  exists b2
  constructor
  exact hContains2
  constructor
  exact hR2
  right
  exact hS2

-- 659：relCompList の結合（2段 witness の並べ替え）
theorem ex659 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    relCompList keysg (relCompList keysβ R S) T
      =
    relCompList keysβ R (relCompList keysg S T) := by

  funext a1 s1
  apply propext
  constructor
  intro hRelCompList1
  obtain ⟨g1, hContainsg1, hRelCompList2, hT1⟩ := hRelCompList1
  obtain ⟨b1, hContainsb1, hR1, hS1⟩ := hRelCompList2
  exists b1
  constructor
  exact hContainsb1
  constructor
  exact hR1
  exists g1
  intro hContainsg2
  obtain ⟨b1, hContains1, hR, g1, hContains2, hS, hT⟩ := hContainsg2
  exists g1
  constructor
  exact hContains2
  constructor
  exists b1
  exact hT

-- 660：relInKeys の append は OR になる
theorem ex660 (keys1 keys2 : List β) :
    relInKeys (α:=α) (keys1 ++ keys2)
      =
    relAdd (relInKeys (α:=α) keys1) (relInKeys (α:=α) keys2) := by

  funext a1 b1
  apply propext
  constructor
  intro hInKeys
  by_cases hInKeys1 : b1 ∈ keys1
  left
  exact hInKeys1
  right
  have hInKeys2 : b1 ∈ keys2 := by
    dsimp [relInKeys] at hInKeys
    rw [List.mem_append] at hInKeys
    obtain hContainsLeft | hContainsRight := hInKeys
    contradiction
    exact hContainsRight
  exact hInKeys2
  dsimp [relAdd, relInKeys]
  intro hRelAdd
  obtain hInKeys1 | hInKeys2 := hRelAdd
  apply List.mem_append_left
  exact hInKeys1
  apply List.mem_append_right
  exact hInKeys2

--------------------------------------------------------------------------------
-- 661〜670：wTrans / wMul（Hadamard）/ wCompList との相性
--------------------------------------------------------------------------------

-- 661：wTrans は 2 回で元に戻る
theorem ex661 (R : WRel α β) :
    wTrans (wTrans R) = R := by
  funext a1 b1
  dsimp [wTrans]

-- 662：wTrans は wAdd と可換
theorem ex662 (R S : WRel α β) :
    wTrans (wAdd R S) = wAdd (wTrans R) (wTrans S) := by
  funext b1 a1
  dsimp [wTrans, wAdd]

-- 663：wTrans は wZero と可換
theorem ex663 :
    wTrans (wZero α β) = wZero β α := by
  funext b1 a1
  dsimp [wTrans, wZero]

-- 664：wTrans は wMask と可換（mask 側は transpose する）
theorem ex664 (R : WRel α β) (M : Rel α β) :
    wTrans (wMask R M) = wMask (wTrans R) (relTrans M) := by
  -- ヒント：by classical; funext b a; simp [wTrans, wMask, maskW, relTrans]
  funext b1 a1
  dsimp [wTrans, wMask, maskW, relTrans]

-- 665：transpose は縮約の順序を逆にする（weighted 版）
theorem ex665 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wTrans (wCompList keys R S) = wCompList keys (wTrans S) (wTrans R) := by
  -- ヒント：Nat.mul_comm が本体
  funext c1 a1
  dsimp [wTrans, wCompList]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    have hEq : R a1 b * S b c1 = S b c1 * R a1 b := by
      apply Nat.mul_comm
    rw [hEq]
    rw [ih]

-- 666：support は transpose と可換
theorem ex666 (R : WRel α β) :
    wSupp (wTrans R) = relTrans (wSupp R) := by

  funext b1 a1
  dsimp [wSupp, wTrans, relTrans]

theorem ex667_pre (a: Nat) (b: Nat) : (0 < a * b)  ↔ 0 < a ∧ 0 < b := by
  constructor
  intro h
  obtain h1 := Nat.pos_of_mul_pos_left h
  obtain h2 := Nat.pos_of_mul_pos_right h
  constructor
  exact h2
  exact h1
  intro h
  obtain ⟨h1, h2⟩ := h
  apply Nat.mul_pos
  exact h1
  exact h2

theorem ex667_pre2 (a: Nat) (b: Nat) : (a * b > 0)  ↔ a > 0 ∧ b > 0 := by
  apply ex667_pre

-- 667：support(Hadamard) は ∧ になる
theorem ex667 (R S : WRel α β) :
    wSupp (wMul R S) = relMul (wSupp R) (wSupp S) := by
  -- ヒント：Nat の積の正（ex608）を使う
  funext a1 b1
  dsimp [wSupp, wMul, relMul]
  obtain h :=
    ex667_pre2 (R a1 b1) (S a1 b1)
  rw [h]

-- 668：wMul の可換
theorem ex668 (R S : WRel α β) :
    wMul R S = wMul S R := by

  funext a1 b1
  dsimp [wMul]
  apply Nat.mul_comm

-- 669：wMul の結合
theorem ex669 (R S T : WRel α β) :
    wMul (wMul R S) T = wMul R (wMul S T) := by

  funext a1 b1
  dsimp [wMul]
  apply Nat.mul_assoc

-- 670：wMul は wAdd に分配（点ごと）
theorem ex670 (R S T : WRel α β) :
    wMul (wAdd R S) T = wAdd (wMul R T) (wMul S T) := by
  -- ヒント：Nat.add_mul
  funext a1 b1
  dsimp [wMul, wAdd]
  apply Nat.add_mul

--------------------------------------------------------------------------------
-- 671〜680：wId / wGraph（0/1 行列）と support / keys
--------------------------------------------------------------------------------

-- 671：support(wId) = relId
theorem ex671 :
    wSupp (wId α) = relId α := by
  -- ヒント：wId = maskW (relId α)、ex613 を使う

  funext a1 a2
  dsimp [wSupp, wId, maskW, relId]
  apply propext
  constructor
  intro h
  by_cases hEq : a1 = a2
  rw [hEq]
  rw [if_neg hEq] at h
  contradiction
  intro h
  rw [if_pos h]
  apply Nat.one_pos

-- 676：support(wGraph f) = relGraph f
theorem ex676 (f : α → β) :
    wSupp (wGraph f) = relGraph f := by
  -- ヒント：wGraph = maskW (relGraph f)、ex613
  funext a1 b1
  dsimp [wSupp, wGraph, maskW, relGraph]
  apply propext
  constructor
  intro h
  by_cases hEq : f a1 = b1
  exact hEq
  rw [if_neg hEq] at h
  contradiction
  intro h
  rw [if_pos h]
  apply Nat.one_pos

-- 677：graph を左に置いた縮約の support は “f a が keys にいる” で潰れる
theorem ex677 (keys : List β) (f : α → β) (S : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys (wGraph f) S) a c
        ↔ (f a ∈ keys ∧ wSupp S (f a) c) := by
  -- ヒント：ex621（support(attn)=relCompList）→ witness b を b=f a に潰す

  intro a1 c1

  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)
  -- ⊢ ∀ (a : α) (c : γ),
  --     wSupp (wCompList keys (wGraph f) S) a c ↔ f a ∈ keys ∧ wSupp S (f a) c
  obtain hEx621 :=
    ex621 keys (wGraph f) S
  rw [attnWRel] at hEx621
  rw [hEx621]
  constructor

  -- mp
  dsimp [relCompList, wGraph, maskW, relGraph]
  intro hRelCompList
  obtain ⟨b1, hContains1, hR1, hS1⟩ := hRelCompList
  dsimp [wSupp, maskW, relGraph] at hR1
  dsimp [wSupp] at hS1
  by_cases hEq : b1 = f a1

  -- pos
  constructor
  rw [←hEq]
  exact hContains1
  dsimp [wSupp, maskW, relGraph]
  rw [←hEq]
  exact hS1

  -- neg
  have hEq2 : ¬f a1 = b1 := by
    intro hEq2_1
    apply hEq
    rw [hEq2_1]

  rw [if_neg hEq2] at hR1
  contradiction

  -- mpr
  intro hExists
  obtain ⟨hInKeys, hS1⟩ := hExists
  dsimp [wSupp] at hS1
  dsimp [relCompList, wGraph, maskW, relGraph]
  exists (f a1)
  constructor

  -- mpr.left
  exact hInKeys

  -- mpr.right
  constructor

  -- mpr.right.left
  dsimp [wSupp, maskW, relGraph]
  rw [if_pos rfl]
  exact Nat.zero_lt_one

  -- mpr.right.right
  dsimp [wSupp]
  exact hS1

-- 678：graph を右に置いた縮約の support は “c = g b” で潰れる
theorem ex678 (keys : List β) (R : WRel α β) (g : β → γ) :
    ∀ a c,
      wSupp (wCompList keys R (wGraph g)) a c
        ↔ (∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by

  -- def relGraph (f : α → β) : Rel α β :=
  --   fun a b => f a = b

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  -- noncomputable def wGraph {α β : Type} (f : α → β) : WRel α β :=
  --   maskW (relGraph f)
  --   fun a b => if f a = b then 1 else 0

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- def attnWRel {α β γ : Type} (keys : List β) (QK : WRel α β) (KV : WRel β γ) : WRel α γ :=
  --   wCompList keys QK KV

  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by
  obtain hEx621 :=
    ex621 keys R (wGraph g)
  rw [attnWRel] at hEx621

  rw [hEx621]

  intro a1 c1
  constructor
  -- mp
  dsimp [relCompList, wGraph, maskW, relGraph]
  intro hwSupp
  obtain ⟨b1, hContains1, hR1, hS1⟩ := hwSupp
  exists b1
  constructor
  exact hContains1
  constructor
  exact hR1
  dsimp [wSupp, maskW, relGraph] at hS1
  by_cases hEq : g b1 = c1
  exact hEq
  rw [if_neg hEq] at hS1
  contradiction

  -- mpr
  intro hExists
  obtain ⟨b1, hContains1, hR1, hEq1⟩ := hExists
  exists b1
  constructor
  exact hContains1
  constructor
  exact hR1
  dsimp [wSupp, wGraph, maskW, relGraph]
  rw [if_pos hEq1]
  apply Nat.one_pos

-- 679：graph-graph の縮約（support 版）
theorem ex679 (keys : List β) (f : α → β) (g : β → γ) :
    ∀ a c,
      wSupp (wCompList keys (wGraph f) (wGraph g)) a c
        ↔ (f a ∈ keys ∧ g (f a) = c) := by
  -- ヒント：ex677/ex678 を組み合わせる

  intro a1 c1

  -- theorem ex677 (keys : List β) (f : α → β) (S : WRel β γ) :
  --     ∀ a c,
  --       wSupp (wCompList keys (wGraph f) S) a c
  --         ↔ (f a ∈ keys ∧ wSupp S (f a) c)
  obtain hEx677 :=
    ex677 keys f (wGraph g) a1 c1

  rw [hEx677]

  constructor

  intro hExists
  obtain ⟨hInKeys, hWSupp⟩ := hExists
  constructor
  exact hInKeys
  dsimp [wSupp, wGraph, maskW, relGraph] at hWSupp
  by_cases hEq : g (f a1) = c1
  exact hEq
  rw [if_neg hEq] at hWSupp
  contradiction

  intro hExists2
  obtain ⟨hInKeys2, hEq2⟩ := hExists2
  constructor
  exact hInKeys2
  dsimp [wSupp, wGraph, maskW, relGraph]
  rw [if_pos hEq2]
  apply Nat.one_pos

-- 680：keys が十分大きいと graph の合成がそのまま（support で）
theorem ex680 (keys : List β) (f : α → β) (g : β → γ) :
    (∀ b, b ∈ keys) →
      wSupp (wCompList keys (wGraph f) (wGraph g)) = relGraph (fun a => g (f a)) := by

  -- ヒント：ex679 を全体で使う
  intro hAll
  funext a1 c1
  -- theorem ex679 (keys : List β) (f : α → β) (g : β → γ) :
  --     ∀ a c,
  --       wSupp (wCompList keys (wGraph f) (wGraph g)) a c
  --         ↔ (f a ∈ keys ∧ g (f a) = c) := by
  obtain hEx679 :=
    ex679 keys f g a1 c1
  rw [hEx679]
  apply propext
  constructor
  intro hExists
  obtain ⟨hInKeys, hEq⟩ := hExists
  exact hEq
  intro hEq2
  constructor
  apply hAll
  exact hEq2

--------------------------------------------------------------------------------
-- 681〜690：multi-head（wAdd）とスカラー倍（wScale）
--------------------------------------------------------------------------------

-- 681：QK を足した attention の support は OR（multi-head の基本）
theorem ex681 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys (wAdd QK1 QK2) KV)
      =
    relAdd (wSupp (wCompList keys QK1 KV)) (wSupp (wCompList keys QK2 KV)) := by
  -- ヒント：ex511（線形性）→ ex612（support(R+S)=∨）

  -- theorem ex511 (keys : List β) (R S : WRel α β) (T : WRel β γ) :
  --     wCompList keys (wAdd R S) T
  --       = wAdd (wCompList keys R T) (wCompList keys S T)
  obtain hEx511 :=
    ex511 keys QK1 QK2 KV

  rw [hEx511]

  -- theorem ex612 (R S : WRel α β) :
  --     wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S)
  obtain hEx612 :=
    ex612 (wCompList keys QK1 KV) (wCompList keys QK2 KV)

  rw [hEx612]

-- 682：KV を足した attention の support も OR
theorem ex682 (keys : List β) (QK : WRel α β) (KV1 KV2 : WRel β γ) :
    wSupp (wCompList keys QK (wAdd KV1 KV2))
      =
    relAdd (wSupp (wCompList keys QK KV1)) (wSupp (wCompList keys QK KV2)) := by

  -- theorem ex512 (keys : List β) (R : WRel α β) (S T : WRel β γ) :
  --     wCompList keys R (wAdd S T)
  --       = wAdd (wCompList keys R S) (wCompList keys R T) := by
  obtain hEx512 :=
    ex512 keys QK KV1 KV2

  rw [hEx512]

  -- theorem ex612 (R S : WRel α β) :
  --     wSupp (wAdd R S) = relAdd (wSupp R)
  obtain hEx612 :=
    ex612 (wCompList keys QK KV1) (wCompList keys QK KV2)

  rw [hEx612]

-- 683：各 head の到達は “sum-head” の到達に含まれる（片側）
theorem ex683 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK1 KV) ⊆ wSupp (wCompList keys (wAdd QK1 QK2) KV) := by
  -- ヒント：wCompList の WLe 単調性＋ ex615（WLe→supp包含）でも可

  -- theorem ex615 (R S : WRel α β) :
  --     WLe R S → (wSupp R ⊆ wSupp S) := by
  apply ex615 (wCompList keys QK1 KV) (wCompList keys (wAdd QK1 QK2) KV)

  dsimp [WLe]
  intro a1 c1
  dsimp [wCompList]
  dsimp [wAdd]

  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]

    have h1 :
      (QK1 a1 b * KV b c1 + wsum keys fun b => QK1 a1 b * KV b c1) ≤
      (QK1 a1 b * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) := by
      apply Nat.add_le_add_iff_left.mpr
      exact ih

    have h2 :
      (QK1 a1 b * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) ≤
      ((QK1 a1 b + QK2 a1 b) * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) := by

      have h2_1 : (QK1 a1 b * KV b c1) ≤ ((QK1 a1 b + QK2 a1 b) * KV b c1) := by
        apply Nat.mul_le_mul_right
        apply Nat.le_add_right

      apply Nat.add_le_add_right
      exact h2_1

    apply Nat.le_trans h1 h2

theorem ex683_2 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK2 KV) ⊆ wSupp (wCompList keys (wAdd QK1 QK2) KV) := by
  -- ヒント：wCompList の WLe 単調性＋ ex615（WLe→supp包含）でも可

  -- theorem ex615 (R S : WRel α β) :
  --     WLe R S → (wSupp R ⊆ wSupp S) := by
  apply ex615 (wCompList keys QK2 KV) (wCompList keys (wAdd QK1 QK2) KV)

  dsimp [WLe]
  intro a1 c1
  dsimp [wCompList]
  dsimp [wAdd]

  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]

    have h1 :
      (QK2 a1 b * KV b c1 + wsum keys fun b => QK2 a1 b * KV b c1) ≤
      (QK2 a1 b * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) := by
      apply Nat.add_le_add_iff_left.mpr
      exact ih

    have h2 :
      (QK2 a1 b * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) ≤
      ((QK1 a1 b + QK2 a1 b) * KV b c1 + wsum keys fun b => (QK1 a1 b + QK2 a1 b) * KV b c1) := by

      have h2_1 : (QK2 a1 b * KV b c1) ≤ ((QK1 a1 b + QK2 a1 b) * KV b c1) := by
        apply Nat.mul_le_mul_right
        apply Nat.le_add_left

      apply Nat.add_le_add_right
      exact h2_1

    apply Nat.le_trans h1 h2


-- 684：両 head が spec を満たせば sum-head も満たす
theorem ex684 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (wCompList keys QK1 KV) ⊆ T) →
    (wSupp (wCompList keys QK2 KV) ⊆ T) →
    (wSupp (wCompList keys (wAdd QK1 QK2) KV) ⊆ T) := by
  -- ヒント：ex681 で OR にして cases

  -- QK1とKVをkeysで畳み込んだ値が0より大きければ、それはTに含まれる
  -- また、QK2とKVをkeysで畳み込んだ値が0より大きければ、それもTに含まれる
  -- という仮定が満たされるのであれば、
  -- QK1とQK2を足し合わせたものとKVをkeysで畳み込んだ値が0より大きい場合もTに含まれる

  -- theorem ex681 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
  --     wSupp (wCompList keys (wAdd QK1 QK2) KV)
  --       =
  --     relAdd (wSupp (wCompList keys QK1 KV)) (wSupp (wCompList keys QK2 KV)) := by

  obtain hEx681 :=
    ex681 keys QK1 QK2 KV
  rw [hEx681]

  intro hSpec1 hSpec2
  intro a1 c1
  intro hRelAdd
  obtain hIn1 | hIn2 := hRelAdd
  apply hSpec1
  exact hIn1
  apply hSpec2
  exact hIn2

-- 685：sum-head が spec を満たすなら、各 head も満たす
theorem ex685 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (wCompList keys (wAdd QK1 QK2) KV) ⊆ T) →
      (wSupp (wCompList keys QK1 KV) ⊆ T) ∧ (wSupp (wCompList keys QK2 KV) ⊆ T) := by

  -- ヒント：ex683（包含）で落とす
  intro hSpec
  constructor
  intro a1 c1
  intro hSupp1
  apply hSpec
  apply ex683 keys QK1 QK2 KV
  exact hSupp1
  intro a2 c2
  intro hSupp2
  apply hSpec
  apply ex683_2 keys QK1 QK2 KV
  exact hSupp2

-- 686：wMask は wAdd に分配する（点ごと分配）
theorem ex686 (R S : WRel α β) (M : Rel α β) :
    wMask (wAdd R S) M = wAdd (wMask R M) (wMask S M) := by
  -- ヒント：Nat.add_mul
  funext a1 b1
  dsimp [wMask, wAdd, maskW]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  rw [if_neg hM]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]

-- 687：mask してから multi-head しても、multi-head してから mask しても同じ（重みレベル）
theorem ex687 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (M : Rel α β) :
    wCompList keys (wMask (wAdd QK1 QK2) M) KV
      =
    wAdd (wCompList keys (wMask QK1 M) KV) (wCompList keys (wMask QK2 M) KV) := by
  -- ヒント：ex686 → ex511
  funext a1 c1
  --dsimp [wCompList]
  rw [ex686 QK1 QK2 M]

  -- theorem ex511 (keys : List β) (R S : WRel α β) (T : WRel β γ) :
  --     wCompList keys (wAdd R S) T
  --       = wAdd (wCompList keys  R            T ) (wCompList keys  S         T) := by
  --         wAdd (wCompList keys (wMask QK1 M) KV) (wCompList keys (wMask QK2 M) KV)
  rw [←ex511 keys (wMask QK1 M) (wMask QK2 M) KV]

-- 688：wScale 0 はゼロ
theorem ex688 (R : WRel α β) :
    wScale 0 R = wZero α β := by

  funext a1 b1
  dsimp [wScale, wZero]
  rw [Nat.zero_mul]

-- 689：t>0 なら、スカラー倍しても support は変わらない
theorem ex689 (t : Nat) (R : WRel α β) :
    (t > 0) → wSupp (wScale t R) = wSupp R := by
  -- ヒント：Nat.mul_pos と「¬(m>0)→m=0」など
  intro hT
  funext a1 b1
  dsimp [wSupp, wScale]
  apply propext
  constructor

  -- mp
  intro h2

  have h3 : 0 < t * R a1 b1 := h2
  obtain hPos := Nat.mul_pos_iff_of_pos_left hT
  rw [hPos] at h3
  exact h3

  -- mpr
  intro h4
  apply Nat.mul_pos
  exact hT
  exact h4

-- 690：左側をスカラー倍すると、縮約結果もスカラー倍される（線形性）
theorem ex690 (keys : List β) (t : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wScale t R) S = wScale t (wCompList keys R S) := by
  -- ヒント：ex539/ex538（Σ と * の交換）＋ Nat.mul_assoc

  funext a1 c1
  dsimp [wCompList, wScale]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.mul_add]
    rw [Nat.mul_assoc]

--------------------------------------------------------------------------------
-- 691〜700：WSpec（「仕様の外は0」）と安全設計の “重みレベル” 表現
--------------------------------------------------------------------------------

-- 691：WSpec は「support ⊆ T」と同値
theorem ex691 (R : WRel α β) (T : Rel α β) :
    WSpec R T ↔ (wSupp R ⊆ T) := by
  -- ヒント：
  --   (→) : wSupp R a b は R a b >0。T でなければ R a b=0 になって矛盾。
  --   (←) : ¬T なら ¬(R>0) なので Nat.eq_zero_of_not_pos で 0。
  constructor
  -- (→)
  intro hWSpec
  intro a1 b1
  intro hSupp
  dsimp [wSupp] at hSupp
  dsimp [WSpec] at hWSpec
  obtain hWSpec2 := hWSpec a1 b1
  by_cases hT : T a1 b1
  exact hT
  obtain h3 := hWSpec2 hT
  have hSupp2 : 0 < R a1 b1 := hSupp
  rw [Nat.pos_iff_ne_zero] at hSupp2
  contradiction

  -- (←)
  intro hSubset
  intro a1 b1
  intro hT
  obtain hSubset2 := hSubset a1 b1
  have hNotSupp : ¬(wSupp R a1 b1) := by
    intro hSupp
    apply hT
    apply hSubset2
    exact hSupp
  obtain hNotSupp2 :=
    Nat.eq_zero_of_not_pos hNotSupp
  exact hNotSupp2

-- 692：wZero は任意の spec を満たす
theorem ex692 (T : Rel α β) :
    WSpec (wZero α β) T := by

  dsimp [WSpec, wZero]
  intro a1 b1
  intro hT
  rfl

-- 693：同じ spec なら足しても spec を満たす
theorem ex693 (R S : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec S T → WSpec (wAdd R S) T := by
  intro hSpecR hSpecS
  dsimp [WSpec, wAdd] at *
  intro a1 b1
  intro hT
  have hSpecR2 := hSpecR a1 b1 hT
  have hSpecS2 := hSpecS a1 b1 hT
  rw [hSpecR2]
  rw [hSpecS2]

-- 694：要素積（Hadamard）は spec を ∧ で細くする
theorem ex694 (R S : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec S U → WSpec (wMul R S) (relMul T U) := by

  intro hSpecR hSpecS
  dsimp [WSpec, wMul, relMul] at *
  intro a1 b1
  intro hTU
  have hSpecR2 := hSpecR a1 b1
  have hSpecS2 := hSpecS a1 b1
  by_cases hT : T a1 b1
  rw [and_iff_right hT] at hTU
  obtain h3 := hSpecS2 hTU
  rw [h3]
  rw [Nat.mul_zero]
  obtain h3 := hSpecR2 hT
  rw [h3]
  rw [Nat.zero_mul]

-- 695：mask すると spec は保たれる（むしろ強くなる）
theorem ex695 (R : WRel α β) (T : Rel α β) (M : Rel α β) :
    WSpec R T → WSpec (wMask R M) T := by
  -- ヒント：wMask ≤ R を使ってもよい
  intro hSpec
  dsimp [WSpec, wMask, maskW] at *
  intro a1 b1
  intro hT
  obtain hSpec2 := hSpec a1 b1 hT
  rw [hSpec2]
  rw [Nat.zero_mul]

-- 696：support(QK) ⊆ (supp(KV)▷T) なら、attn の重みは T の外で 0
theorem ex696 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ rRes (wSupp KV) T) →
      WSpec (attnWRel keys QK KV) T := by
  -- ヒント：ex622（support ⊆ T）＋ ex691（WSpec↔support⊆）
  intro hSubset
  rw [WSpec]
  intro a1 c1
  intro hT
  rw [attnWRel]
  rw [wCompList]

  have h1 : ∀ (b : β), (QK a1 b = 0) ∨ (KV b c1 = 0) := by
    intro b1
    obtain hSubset2 := hSubset a1 b1
    dsimp [wSupp, rRes] at hSubset2
    by_cases hQK : QK a1 b1 = 0
    left
    exact hQK
    right
    by_cases hKV : KV b1 c1 = 0
    exact hKV
    obtain hQK2 := Nat.pos_iff_ne_zero.mpr hQK
    obtain hKV2 := Nat.pos_iff_ne_zero.mpr hKV
    obtain hSubset3 := hSubset2 hQK2 c1 hKV2
    contradiction

  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b1 keys ih =>
    dsimp [wsum]
    obtain hCase1 | hCase2 := h1 b1
    rw [hCase1]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    rw [ih]
    rw [hCase2]
    rw [Nat.mul_zero]
    rw [Nat.zero_add]
    rw [ih]

-- 697：安全マスク（residual）を入れると、必ず WSpec を満たす（重みレベル）
theorem ex697 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    WSpec (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) T := by
  -- ヒント：ex650（support ⊆ T）＋ ex691
  intro a1 c1
  intro hT
  obtain hEx650 :=
    ex650 keys QK KV T a1 c1
  obtain hEx650_2 :=
    mt hEx650 hT
  obtain hEx650_3 :=
    Nat.eq_zero_of_not_pos hEx650_2
  exact hEx650_3

-- 698：spec は右に単調（T ⊆ T' なら WSpec R T → WSpec R T'）
theorem ex698 (R : WRel α β) (T T' : Rel α β) :
    (T ⊆ T') → WSpec R T → WSpec R T' := by

  intro hSubset hWSpec
  dsimp [WSpec] at *
  intro a1 b1
  intro hT'
  apply hWSpec
  obtain hSubset2 := hSubset a1 b1
  obtain hSubset3 := mt hSubset2 hT'
  exact hSubset3

-- 699：spec を 2 つ同時に満たすなら、∧ も満たす（tightening）
theorem ex699 (R : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec R U → WSpec R (relMul T U) := by
  intro hSpecT hSpecU
  dsimp [WSpec, relMul] at *
  intro a1 b1
  intro hTU
  obtain hSpecT2 := hSpecT a1 b1
  obtain hSpecU2 := hSpecU a1 b1

  by_cases hT : T a1 b1
  rw [and_iff_right hT] at hTU
  obtain h3 := hSpecU2 hTU
  exact h3
  obtain h3 := hSpecT2 hT
  exact h3

-- 700：入力側/出力側の spec があると、縮約後の spec は relComp で表せる
theorem ex700 (keys : List β) (R : WRel α β) (S : WRel β γ)
    (T : Rel α β) (U : Rel β γ) :
    WSpec R T → WSpec S U → WSpec (wCompList keys R S) (relComp T U) := by
  -- ヒント：support(wCompList) ⊆ relCompList ⊆ relComp を経由して ex691 へ

  intro hSpecR hSpecS
  rw [WSpec] at *
  intro a1 c1
  intro hRelComp
  dsimp [relComp] at hRelComp
  dsimp [wCompList]
  rw [not_exists] at hRelComp
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b1 keys ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_zero]
    obtain hRelComp2 := hRelComp b1
    by_cases hT : T a1 b1
    rw [and_iff_right hT] at hRelComp2
    obtain hSpecS2 := hSpecS b1 c1 hRelComp2
    rw [hSpecS2]
    rw [Nat.mul_zero]
    obtain hSpecR2 := hSpecR a1 b1 hT
    rw [hSpecR2]
    rw [Nat.zero_mul]

end TL
