--------------------------------------------------------------------------------
-- Basic_551.lean
-- 演習問題 551〜600（重み付き関係＝行列/テンソルとしての Attention：縮約・マスク・support・residual）
-- ※ import Mathlib なし
-- ※ Basic_501 を import して再利用
--------------------------------------------------------------------------------

import Lean4.Basic_501

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- ここでの見取り図（読み物）：
--   WRel α β   : α×β 成分をもつ「重み付き関係」（行列/テンソルと思ってよい）
--   wCompList  : 中間添字 β での縮約（Σ_b QK(a,b)*KV(b,c)）
--               ※ keys : List β で有限個だけ足す（実装上の有限化）
--   wMask      : 0/1 マスクとの要素積（Hadamard 積）
--   attnNat    : score(a,b) と val(b) を縮約して a ごとのスカラーを作る（注意機構の集約）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 補助：Rel の ⊤ / ⊥（Prop の上の関係）
--------------------------------------------------------------------------------
def relTop (α β : Type) : Rel α β := fun _ _ => True
def relBot (α β : Type) : Rel α β := fun _ _ => False

--------------------------------------------------------------------------------
-- 補助：ベクトル（β → Nat）を WRel β Unit に埋め込む
--------------------------------------------------------------------------------
def vecAsWRel (v : β → Nat) : WRel β Unit :=
  fun b _ => v b

--------------------------------------------------------------------------------
-- 補助：support（正の重みがある場所を Prop 関係として見る）
--------------------------------------------------------------------------------
def wSupp (R : WRel α β) : Rel α β :=
  fun a b => R a b > 0

--------------------------------------------------------------------------------
-- 551〜560：wCompList（縮約）の基本法則（ゼロ/空/再帰/単調性）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 551：左ゼロ（QK=0 なら合成も 0）
--------------------------------------------------------------------------------
theorem ex551 (keys : List β) (KV : WRel β γ) :
    wCompList keys (wZero α β) KV = wZero α γ := by
  -- ヒント：funext a c; keys で帰納（[] / b::keys）

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- def wZero (α β : Type) : WRel α β := fun _ _ => 0

  -- 片側が０しか返さないのであれば、 合成しても０にしかならない。

  funext a1 g1
  dsimp [wCompList]
  dsimp [wZero]
  conv =>
    lhs
    dsimp [wsum]
    arg 2
    intro b1
    rw [Nat.zero_mul]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

--------------------------------------------------------------------------------
-- 552：右ゼロ（KV=0 なら合成も 0）
--------------------------------------------------------------------------------
theorem ex552 (keys : List β) (QK : WRel α β) :
    wCompList keys QK (wZero β γ) = wZero α γ := by
  -- ヒント：ex551 と同様に keys で帰納

  -- ex551と同様。ただし、今度は 右側が０。

  funext a1 g1
  dsimp [wCompList]
  dsimp [wZero]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

--------------------------------------------------------------------------------
-- 553：空 keys（足す項が無い）
--------------------------------------------------------------------------------
theorem ex553 (QK : WRel α β) (KV : WRel β γ) :
    wCompList ([] : List β) QK KV = wZero α γ := by
  -- ヒント：wCompList の定義を dsimp

  -- 空のリストを畳み込んでも、その合計は０にしかならない。

  funext a1 g1
  dsimp [wCompList]
  dsimp [wsum]
  dsimp [wZero]

--------------------------------------------------------------------------------
-- 554：cons 展開（“先頭の項 + 残り”）
--------------------------------------------------------------------------------
theorem ex554 (b : β) (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c, wCompList (b :: keys) QK KV a c
          = QK a b * KV b c + wCompList keys QK KV a c := by
  -- ヒント：dsimp [wCompList] で定義展開

  -- keysにbを追加して畳み込むことは
  -- 元のkeysでの畳み込みに対し、QK a b * KV b cを加算することと同じ。

  intro a1 g1
  dsimp [wCompList]
  dsimp [wsum]

--------------------------------------------------------------------------------
-- 555：singleton keys（1項だけの縮約）
--------------------------------------------------------------------------------
theorem ex555 (b : β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c, wCompList [b] QK KV a c = QK a b * KV b c := by
  -- ヒント：ex554 と ex553

  -- keysの要素がbだけだった場合、
  -- その畳み込みはQK a b * KV b cと一致する

  intro a1 g1
  dsimp [wCompList]
  dsimp [wsum]

--------------------------------------------------------------------------------
-- 556：append 分解（keys を2つに分けると “和” になる）
--------------------------------------------------------------------------------
theorem ex556 (keys1 keys2 : List β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c,
      wCompList (keys1 ++ keys2) QK KV a c
        = wCompList keys1 QK KV a c + wCompList keys2 QK KV a c := by
  -- ヒント：keys1 で帰納（[] / b::keys1）

  -- ふたつのkeysを連結して畳み込むことは、
  -- それぞれを畳み込んだ結果の和に等しい。

  intro a1 g1
  dsimp [wCompList]
  induction keys1 with
  | nil =>
    dsimp [wsum]
    rw [Nat.zero_add]
  | cons b keys1 ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_assoc]

--------------------------------------------------------------------------------
-- 557：縮約の結合（2段縮約の結合性）
-- keysβ で β を縮約し、その後 keysg で γ を縮約するのは、
-- 先に γ を縮約してから β を縮約するのと同じ（型が合う形で）
--------------------------------------------------------------------------------
theorem ex557 (keysβ : List β) (keysg : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wCompList keysg (wCompList keysβ R S) T
      = wCompList keysβ R (wCompList keysg S T) := by
  -- ヒント：funext a d; どちらも「二重和」になるので
  --         keysβ / keysg のどちらかで帰納して整理

  -- 畳み込みの結合律

  rw [ex541]

--------------------------------------------------------------------------------
-- 558：左単調性（QK を増やすと結果も増える）
--------------------------------------------------------------------------------
theorem ex558 (keys : List β) (QK QK' : WRel α β) (KV : WRel β γ) :
    WLe QK QK' → WLe (wCompList keys QK KV) (wCompList keys QK' KV) := by
  -- ヒント：keys で帰納、各項で ≤ を使う

  -- def WLe {α β : Type} (R S : WRel α β) : Prop :=
  --   ∀ a b, R a b ≤ S a b

  -- WRelの結果がすべてにおいて大きいのであれば、
  -- その畳み込み結果もすべてにおいて大きい。
  -- 左側

  intro hWle a1 g1
  dsimp [wCompList]
  dsimp [WRel] at QK QK' KV
  dsimp [WLe] at hWle
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_right (KV b g1) (hWle a1 b)
    exact ih

--------------------------------------------------------------------------------
-- 559：右単調性（KV を増やすと結果も増える）
--------------------------------------------------------------------------------
theorem ex559 (keys : List β) (QK : WRel α β) (KV KV' : WRel β γ) :
    WLe KV KV' → WLe (wCompList keys QK KV) (wCompList keys QK KV') := by
  -- ヒント：keys で帰納

  -- WRelの結果がすべてにおいて大きいのであれば、
  -- その畳み込み結果もすべてにおいて大きい。
  -- 右側

  intro hWle a1 g1
  dsimp [wCompList]
  dsimp [WRel] at QK KV KV'
  dsimp [WLe] at hWle
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_left (QK a1 b) (hWle b g1)
    exact ih

--------------------------------------------------------------------------------
-- 560：両側単調性（まとめ）
--------------------------------------------------------------------------------
theorem ex560 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
    WLe QK QK' → WLe KV KV' →
    WLe (wCompList keys QK KV) (wCompList keys QK' KV') := by
  -- ヒント：ex558 と ex559 を合成

  -- 右側も左側も大きいならば、
  -- 畳み込み結果もすべてにおいて大きい。
  intro hWle1 hWle2 a1 g1
  obtain hWLe1 := ex559 keys QK KV KV' hWle2 a1 g1
  obtain hWLe2 := ex558 keys QK QK' KV' hWle1 a1 g1
  obtain hWLe3 := Nat.le_trans hWLe1 hWLe2
  exact hWLe3

--------------------------------------------------------------------------------
-- 561〜570：attnNat を “縮約として” 扱う（再帰形 / 線形性 / 単調性）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 561：attnNat は「Unit への縮約」として書ける
--------------------------------------------------------------------------------
theorem ex561 (keys : List β) (score : α → β → Nat) (val : β → Nat) :
    ∀ a : α, attnNat keys score val a = wCompList keys score (vecAsWRel val) a () := by
  -- ヒント：keys で帰納。attnNat と wCompList の再帰が一致するはず。

  -- def attnNat (keys : List β) (score : α → β → Nat) (val : β → Nat) : α → Nat :=
  --   fun a => wsum keys (fun b => score a b * val b)

  -- def vecAsWRel (v : β → Nat) : WRel β Unit :=
  --   fun b _ => v b

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  intro a1
  dsimp [attnNat]
  dsimp [wCompList]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [ih]
    dsimp [vecAsWRel]

--------------------------------------------------------------------------------
-- 562：attnNat（空 keys）
--------------------------------------------------------------------------------
theorem ex562 (score : α → β → Nat) (val : β → Nat) :
    ∀ a : α, attnNat ([] : List β) score val a = 0 := by
  -- ヒント：dsimp [attnNat]

  -- 空リストの畳み込みの結果は０になる。

  intro a1
  dsimp [attnNat]
  dsimp [wsum]

--------------------------------------------------------------------------------
-- 563：attnNat の cons 展開
--------------------------------------------------------------------------------
theorem ex563 (b : β) (keys : List β) (score : α → β → Nat) (val : β → Nat) :
    ∀ a : α, attnNat (b :: keys) score val a
            = score a b * val b + attnNat keys score val a := by
  -- ヒント：dsimp [attnNat]

  -- keysにbを追加して畳み込むというのは、
  -- 元のkeysでの畳み込みに対し、score a b * val bを加算することと同じ。

  intro a1
  dsimp [attnNat]
  dsimp [wsum]

--------------------------------------------------------------------------------
-- 564：score が 0 なら attention も 0
--------------------------------------------------------------------------------
theorem ex564 (keys : List β) (val : β → Nat) :
    ∀ a : α, attnNat keys (fun _ _ => 0) val a = 0 := by
  -- ヒント：keys で帰納（ex563 を使う）

  -- scoreが常に０を返すならば、
  -- 畳み込みの結果も０にしかならない。

  intro a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    exact ih

--------------------------------------------------------------------------------
-- 565：val が 0 なら attention も 0
--------------------------------------------------------------------------------
theorem ex565 (keys : List β) (score : α → β → Nat) :
    ∀ a : α, attnNat keys score (fun _ => 0) a = 0 := by
  -- ヒント：keys で帰納（ex563）

  -- valが常に０を返すならば、
  -- 畳み込みの結果も０にしかならない。

  intro a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

--------------------------------------------------------------------------------
-- 566：val について線形（val1+val2）
--------------------------------------------------------------------------------
theorem ex566 (keys : List β) (score : α → β → Nat) (val1 val2 : β → Nat) :
    ∀ a : α,
      attnNat keys score (fun b => val1 b + val2 b) a
        = attnNat keys score val1 a + attnNat keys score val2 a := by
  -- ヒント：keys で帰納、Nat の分配則

  -- attenNatは準同型的に振る舞う
  -- 言い換えると、 valの和を取ることは
  -- attenNatの結果の和を取ることと同じ。

  intro a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_assoc]
    rw [←Nat.add_assoc (wsum keys fun b => score a1 b * val1 b) (score a1 b * val2 b) (wsum keys fun b => score a1 b * val2 b)]
    rw [Nat.add_comm (wsum keys fun b => score a1 b * val1 b) (score a1 b * val2 b)]
    rw [←Nat.add_assoc]
    rw [←Nat.add_assoc]
    rw [←Nat.add_assoc]
    rw [Nat.add_right_cancel_iff]
    rw [Nat.add_right_cancel_iff]
    rw [Nat.mul_add]

--------------------------------------------------------------------------------
-- 567：score について線形（score1+score2）
--------------------------------------------------------------------------------
theorem ex567 (keys : List β) (score1 score2 : α → β → Nat) (val : β → Nat) :
    ∀ a : α,
      attnNat keys (fun a b => score1 a b + score2 a b) val a
        = attnNat keys score1 val a + attnNat keys score2 val a := by
  -- ヒント：keys で帰納

  -- attenNatは準同型的に振る舞う
  -- 言い換えると、 scoreの和を取ることは
  -- attenNatの結果の和を取ることと同じ。

  intro a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
  | cons b keys ih =>
    dsimp [wsum]
    rw [←Nat.add_assoc (score1 a1 b * val b + wsum keys fun b => score1 a1 b * val b) (score2 a1 b * val b) (wsum keys fun b => score2 a1 b * val b)]
    rw [Nat.add_assoc (score1 a1 b * val b) (wsum keys fun b => score1 a1 b * val b) (score2 a1 b * val b)]
    rw [Nat.add_comm (wsum keys fun b => score1 a1 b * val b) (score2 a1 b * val b)]
    rw [←Nat.add_assoc]
    rw [Nat.add_assoc]
    rw [ih]
    rw [Nat.add_right_cancel_iff]
    rw [←Nat.add_mul]

--------------------------------------------------------------------------------
-- 568：score に単調（pointwise ≤）
--------------------------------------------------------------------------------
theorem ex568 (keys : List β) (score score' : α → β → Nat) (val : β → Nat) :
    (∀ a b, score a b ≤ score' a b) →
    (∀ a : α, attnNat keys score val a ≤ attnNat keys score' val a) := by
  -- ヒント：keys で帰納、Nat の単調性

  -- attenNatは単調に振る舞う
  -- 言い換えると、 scoreがすべての場所で大きいならば
  -- attenNatの結果もすべての場所で大きい。

  intro hLe a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_right (val b) (hLe a1 b)
    exact ih

--------------------------------------------------------------------------------
-- 569：val に単調（pointwise ≤）
--------------------------------------------------------------------------------
theorem ex569 (keys : List β) (score : α → β → Nat) (val val' : β → Nat) :
    (∀ b, val b ≤ val' b) →
    (∀ a : α, attnNat keys score val a ≤ attnNat keys score val' a) := by
  -- ヒント：keys で帰納

  -- attenNatは単調に振る舞う
  -- 言い換えると、 valがすべての場所で大きいならば
  -- attenNatの結果もすべての場所で大きい。

  intro hLe a1
  dsimp [attnNat]
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b keys ih =>
    dsimp [wsum]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_left (score a1 b) (hLe b)
    exact ih

--------------------------------------------------------------------------------
-- 570：keys の append（足し算に分解）
--------------------------------------------------------------------------------
theorem ex570 (keys1 keys2 : List β) (score : α → β → Nat) (val : β → Nat) :
    ∀ a : α,
      attnNat (keys1 ++ keys2) score val a
        = attnNat keys1 score val a + attnNat keys2 score val a := by
  -- ヒント：keys1 で帰納（ex563）

  -- ふたつのkeysを連結して畳み込むことは、
  -- それぞれを畳み込んだ結果の和に等しい。

  intro a1
  dsimp [attnNat]

  induction keys1 with
  | nil =>
    dsimp [wsum]
    rw [Nat.zero_add]
  | cons b keys1 ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_assoc]

--------------------------------------------------------------------------------
-- 571〜580：マスク（0/1 要素積）の法則（⊤/⊥/冪等/単調性/縮約との相性）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 571：⊤ マスクは 1（全部通す）
--------------------------------------------------------------------------------
theorem ex571 :
    ∀ a b, maskW (relTop α β) a b = 1 := by
  -- ヒント：by classical; simp [maskW, relTop]

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  -- def relTop (α β : Type) : Rel α β := fun _ _ => True

  intro a1 b1
  dsimp [maskW]
  dsimp [relTop]
  rw [if_pos True.intro]

--------------------------------------------------------------------------------
-- 572：⊥ マスクは 0（全部落とす）
--------------------------------------------------------------------------------
theorem ex572 :
    ∀ a b, maskW (relBot α β) a b = 0 := by
  -- ヒント：by classical; simp [maskW, relBot]

  -- def relBot (α β : Type) : Rel α β := fun _ _ => False

  intro a1 b1
  dsimp [maskW]
  dsimp [relBot]
  rw [if_neg False.elim]

--------------------------------------------------------------------------------
-- 573：wMask R ⊤ = R
--------------------------------------------------------------------------------
theorem ex573 (R : WRel α β) :
    wMask R (relTop α β) = R := by
  -- ヒント：funext; by classical; simp [wMask, maskW, relTop]

  -- noncomputable def wMask {α β : Type} (R : WRel α β) (M : Rel α β) : WRel α β :=
  --   fun a b => R a b * maskW M a b

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  dsimp [relTop]
  rw [if_pos True.intro]
  rw [Nat.mul_one]

--------------------------------------------------------------------------------
-- 574：wMask R ⊥ = 0
--------------------------------------------------------------------------------
theorem ex574 (R : WRel α β) :
    wMask R (relBot α β) = wZero α β := by
  -- ヒント：funext; by classical; simp [wMask, maskW, relBot, wZero]

  -- 常にFalseを返すのであれば、
  -- マスクをかけた結果は常に０にしかならない。

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  dsimp [relBot]
  rw [wZero]
  rw [if_neg False.elim]
  rw [Nat.mul_zero]

--------------------------------------------------------------------------------
-- 575：マスクは冪等（同じマスクを2回かけても同じ）
--------------------------------------------------------------------------------
theorem ex575 (R : WRel α β) (M : Rel α β) :
    wMask (wMask R M) M = wMask R M := by
  -- ヒント：funext; by classical; simp [wMask, maskW]

  -- マスクの冪等律

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  rw [Nat.mul_one]
  rw [if_neg hM]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]

--------------------------------------------------------------------------------
-- 576：マスクの合成（2枚かけるのは ∧ を1枚かけるのと同じ）
--------------------------------------------------------------------------------
theorem ex576 (R : WRel α β) (M N : Rel α β) :
    wMask (wMask R M) N = wMask R (relMul M N) := by
  -- ヒント：funext; by classical; simp [wMask, maskW, relMul]

  -- MとNの二回マスクをかけるということは
  -- MとNの論理積でマスクをかけることと同じ。

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  dsimp [relMul]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  by_cases hN : N a1 b1
  rw [if_pos hN]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  have h1 : M a1 b1 ∧ N a1 b1 := ⟨hM, hN⟩
  rw [if_pos h1]
  rw [Nat.mul_one]
  rw [if_neg hN]
  have h2 : ¬(M a1 b1 ∧ N a1 b1) := by
    intro h
    exact hN h.right
  rw [if_neg h2]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [if_neg hM]
  rw [Nat.mul_zero]
  by_cases hN : N a1 b1
  rw [if_pos hN]
  have h3 : ¬(M a1 b1 ∧ N a1 b1) := by
    intro h
    exact hM h.left
  rw [if_neg h3]
  rw [Nat.mul_zero]
  rw [if_neg hN]
  have h4 : ¬(M a1 b1 ∧ N a1 b1) := by
    intro h
    exact hM h.left
  rw [if_neg h4]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]

--------------------------------------------------------------------------------
-- 577：マスクすると値は増えない（≤）
--------------------------------------------------------------------------------
theorem ex577 (R : WRel α β) (M : Rel α β) :
    WLe (wMask R M) R := by
  -- ヒント：by classical; intro a b; simp [wMask, maskW]; cases (M a b)

  -- マスクをかけることで値が増えることはない。

  intro a1 b1
  dsimp [wMask]
  dsimp [maskW]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  rw [Nat.mul_one]
  apply Nat.le_refl
  rw [if_neg hM]
  rw [Nat.mul_zero]
  apply Nat.zero_le

--------------------------------------------------------------------------------
-- 578：マスクは “弱める” と単調（M ⊆ N なら mask(M) ≤ mask(N)）
--------------------------------------------------------------------------------
theorem ex578 (R : WRel α β) (M N : Rel α β) :
    (M ⊆ N) → WLe (wMask R M) (wMask R N) := by
  -- ヒント：by classical; intro hMN a b; by_cases hM : M a b

  -- マスクをかける範囲が狭いなら
  -- マスクをかけた結果はすべてにおいて以下になる。

  intro hMN a1 b1
  rw [RelLe] at hMN
  dsimp [wMask]
  dsimp [maskW]
  by_cases hM : M a1 b1
  rw [if_pos hM]
  obtain hN := hMN a1 b1 hM
  rw [if_pos hN]
  rw [Nat.mul_one]
  apply Nat.le_refl
  rw [if_neg hM]
  rw [Nat.mul_zero]
  apply Nat.zero_le

--------------------------------------------------------------------------------
-- 579：左側をマスクすると縮約は減る（≤）
--------------------------------------------------------------------------------
theorem ex579 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (M : Rel α β) :
    WLe (wCompList keys (wMask QK M) KV) (wCompList keys QK KV) := by
  -- ヒント：ex577 と ex558 を使う（単調性で押す）

  -- マスクをかければ、畳み込みの結果はすべてにおいて以下になる。
  -- 左側

  intro a1 g1
  dsimp [wCompList]
  dsimp [WRel] at QK KV
  dsimp [Rel] at M
  dsimp [wMask]
  dsimp [maskW]
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b1 keys ih =>
    dsimp [wsum]
    by_cases hM : M a1 b1
    rw [if_pos hM]
    rw [Nat.mul_one]
    apply Nat.add_le_add_left
    exact ih
    rw [if_neg hM]
    rw [Nat.mul_zero]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    apply Nat.le_trans ih
    apply Nat.le_add_left

--------------------------------------------------------------------------------
-- 580：右側をマスクすると縮約は減る（≤）
--------------------------------------------------------------------------------
theorem ex580 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (N : Rel β γ) :
    WLe (wCompList keys QK (wMask KV N)) (wCompList keys QK KV) := by
  -- ヒント：ex577 と ex559

  -- マスクをかければ、畳み込みの結果はすべてにおいて以下になる。
  -- 右側

  intro a1 g1
  dsimp [wCompList]
  dsimp [WRel] at QK KV
  dsimp [Rel] at N
  dsimp [wMask]
  dsimp [maskW]
  induction keys with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons b1 keys ih =>
    dsimp [wsum]
    by_cases hN : N b1 g1
    rw [if_pos hN]
    rw [Nat.mul_one]
    apply Nat.add_le_add_left
    exact ih
    rw [if_neg hN]
    rw [Nat.mul_zero]
    rw [Nat.mul_zero]
    rw [Nat.zero_add]
    apply Nat.le_trans ih
    apply Nat.le_add_left

--------------------------------------------------------------------------------
-- 581〜590：support（>0）で “論理関係” に落として見る（attention をテンソル論理へ接続）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 581：support(0) = ⊥
--------------------------------------------------------------------------------
theorem ex581 :
    wSupp (wZero α β) = relBot α β := by
  -- ヒント：funext; apply propext; dsimp [wSupp, wZero, relBot]

  funext a1 b1
  dsimp [wSupp]
  dsimp [wZero]
  dsimp [relBot]
  apply propext
  refine ⟨?fLeft, ?fRight⟩
  intro hPos
  cases hPos
  intro f
  contradiction

--------------------------------------------------------------------------------
-- 582：support(maskW M) = M
--------------------------------------------------------------------------------
theorem ex582 (M : Rel α β) :
    wSupp (maskW M) = M := by
  -- ヒント：funext; apply propext; by classical; by_cases h : M a b

  funext a1 b1
  dsimp [wSupp]
  dsimp [maskW]
  by_cases hM : M a1 b1

  rw [if_pos hM]
  apply propext
  refine ⟨?fLeft1, ?fRight1⟩
  -- fLeft1
  intro hPos
  exact hM
  -- fRight1
  intro hM2
  apply Nat.zero_lt_one

  rw [if_neg hM]
  apply propext
  refine ⟨?fLeft2, ?fRight2⟩
  -- fLeft2
  intro hPos
  cases hPos
  -- fRight2
  intro hM2
  contradiction

--------------------------------------------------------------------------------
-- 583：support(wMask R M) = support(R) ∧ M
--------------------------------------------------------------------------------
theorem ex583 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) = relMul (wSupp R) M := by
  -- ヒント：funext; apply propext; by classical; by_cases h : M a b

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- def relMul (R S : Rel α β) : Rel α β :=
  --   fun a b => R a b ∧ S a b

  funext a1 b1
  dsimp [wSupp]
  dsimp [wMask]
  dsimp [relMul]
  dsimp [maskW]
  by_cases hM : M a1 b1
  -- pos
  rw [if_pos hM]
  rw [Nat.mul_one]
  apply propext
  refine ⟨?fLeft1, ?fRight1⟩
  -- fLeft1
  intro hPos
  dsimp [wSupp]
  constructor
  exact hPos
  exact hM
  -- fRight1
  intro hAnd
  obtain ⟨hWSupp,hM2⟩ := hAnd
  dsimp [wSupp] at hWSupp
  exact hWSupp
  -- neg
  rw [if_neg hM]
  rw [Nat.mul_zero]
  apply propext
  refine ⟨?fLeft2, ?fRight2⟩
  -- fLeft2
  intro hPos
  cases hPos
  -- fRight2
  intro hAnd
  obtain ⟨hWSupp,hM2⟩ := hAnd
  contradiction

--------------------------------------------------------------------------------
-- 584：WLe なら support の包含が成り立つ
--------------------------------------------------------------------------------
theorem ex584 (R S : WRel α β) :
    WLe R S → (wSupp R ⊆ wSupp S) := by
  -- ヒント：intro h a b hpos; have := h a b; exact lt_of_lt_of_le hpos this

  intro hWLe a1 b1 hwSupp
  dsimp [wSupp] at hwSupp
  dsimp [wSupp]
  dsimp [WLe] at hWLe
  obtain hS := hWLe a1 b1
  apply Nat.lt_of_lt_of_le hwSupp hS

--------------------------------------------------------------------------------
-- 585：support(wCompList ...) は relComp(support QK)(support KV) に含まれる
--------------------------------------------------------------------------------
theorem ex585 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK KV) ⊆ relComp (wSupp QK) (wSupp KV) := by
  -- ヒント：keys で帰納。
  --   ・[] は矛盾（0>0）
  --   ・b::keys は
  --       (QK a b * KV b c + rest) > 0 から
  --       (QK a b * KV b c) > 0 もしくは rest > 0 を取り出す

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- def relComp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  --   fun a c => ∃ b, R a b ∧ S b c

  -- keysで対象を制限しているため、
  -- 左辺の方が狭くなる

  intro a1 g1 hwSupp
  dsimp [wSupp] at hwSupp
  dsimp [wCompList] at hwSupp
  dsimp [relComp]
  dsimp [wSupp]
  induction keys with
  | nil =>
    dsimp [wsum] at hwSupp
    cases hwSupp
  | cons b1 keys ih =>
    dsimp [wsum] at hwSupp
    by_cases h1 : (QK a1 b1 * KV b1 g1) > 0
    have h2 : ((QK a1 b1) > 0) ∧ ((KV b1 g1) > 0) := by
      by_cases hQK : (QK a1 b1) > 0
      by_cases hKV : (KV b1 g1) > 0

      -- pos
      constructor

      -- pos.left
      exact hQK

      -- pos.right
      exact hKV

      -- neg
      cases h3 : KV b1 g1 with
      | zero =>
        rw [h3] at h1
        rw [Nat.mul_zero] at h1
        contradiction
      | succ n =>
        constructor
        exact hQK
        exact Nat.succ_pos n

      cases h4 : QK a1 b1 with
      | zero =>
        rw [h4] at h1
        rw [Nat.zero_mul] at h1
        contradiction
      | succ n =>
        constructor
        exact Nat.succ_pos n
        rw [h4] at h1
        cases h5 : KV b1 g1 with
        | zero =>
          rw [h5] at h1
          contradiction
        | succ m =>
          exact Nat.succ_pos m

    exists b1

    -- neg
    apply ih

    have h5: QK a1 b1 * KV b1 g1 = 0 := by
      cases h5_1 : QK a1 b1 with
      | zero =>
        rw [Nat.zero_mul]
      | succ n =>
        cases h5_2 : KV b1 g1 with
        | zero =>
          rw [Nat.mul_zero]
        | succ m =>
          apply False.elim
          apply h1
          rw [h5_1]
          rw [h5_2]
          rw [Nat.succ_mul_succ]
          apply Nat.zero_lt_succ

    rw [h5] at hwSupp
    rw [Nat.zero_add] at hwSupp
    exact hwSupp

--------------------------------------------------------------------------------
-- 586：support から “keys の中に witness がいる” を取り出す（→ 方向）
--------------------------------------------------------------------------------
theorem ex586 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys QK KV) a c →
        ∃ b, b ∈ keys ∧ wSupp QK a b ∧ wSupp KV b c := by
  -- ヒント：keys で帰納。b::keys の場合、head 項で決まるか tail に流すか。

  -- wCompListの結果が0より大きいならば、
  -- keysの中に少なくとも一つのwSupp QK a b と wSupp KV b c の両方を満たすbが存在するはず

  intro a1 c1 hwSupp
  dsimp [wSupp] at hwSupp
  dsimp [wCompList] at hwSupp
  dsimp [wSupp]
  induction keys with
  | nil =>
    dsimp [wsum] at hwSupp
    cases hwSupp
  | cons b1 keys ih =>
    dsimp [wsum] at hwSupp
    by_cases h1 : (wsum keys fun b => QK a1 b * KV b c1) > 0
    obtain h2 := ih h1
    obtain ⟨b2, hIn, hQK, hKV⟩ := h2
    exists b2
    constructor
    apply List.mem_cons_of_mem
    exact hIn
    constructor
    exact hQK
    exact hKV
    obtain h2 :=  Nat.eq_zero_of_not_pos h1
    rw [h2] at hwSupp
    obtain h3 := Nat.pos_of_mul_pos_right hwSupp
    obtain h4 := Nat.pos_of_mul_pos_left hwSupp
    rw [Nat.add_zero] at hwSupp
    exists b1
    constructor
    apply List.mem_cons_self
    constructor
    exact h3
    exact h4

--------------------------------------------------------------------------------
-- 587：witness が keys にいれば support が立つ（← 方向）
--------------------------------------------------------------------------------
theorem ex587 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c,
      (∃ b, b ∈ keys ∧ wSupp QK a b ∧ wSupp KV b c) →
        wSupp (wCompList keys QK KV) a c := by
  -- ヒント：keys で帰納。mem_cons を使って cases。

  -- def wSupp (R : WRel α β) : Rel α β :=
  --   fun a b => R a b > 0

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- keysの中にwSupp QK a b と wSupp KV b c の両方を満たすbが存在するならば、
  -- wCompListの結果は0より大きいはず

  intro a1 c1 hExist

  obtain ⟨b1, hIn, hQK, hKV⟩ := hExist

  dsimp [wSupp] at hQK hKV

  dsimp [wSupp]
  dsimp [wCompList]

  induction keys with

  | nil =>
    dsimp [wsum]
    cases hIn

  | cons b2 keys ih =>
    dsimp [wsum]
    by_cases hEq : b1 = b2

    -- b1 = b2
    rw [←hEq]
    have h1 : QK a1 b1 * KV b1 c1 > 0 := by
      apply Nat.mul_pos
      exact hQK
      exact hKV

    rw [Nat.add_comm (QK a1 b1 * KV b1 c1) (wsum keys fun b => QK a1 b * KV b c1)]
    apply  Nat.add_pos_right
    exact h1

    -- b1 ≠ b2
    have h2 : b1 ∈ keys := by
      cases (List.mem_cons.mp hIn) with
      | inl hEq2 =>
        contradiction
      | inr hIn2 =>
        exact hIn2

    have h3 : wsum keys (fun b => QK a1 b * KV b c1) > 0 := by
      apply ih
      exact h2

    rw [Nat.add_comm (QK a1 b2 * KV b2 c1) (wsum keys fun b => QK a1 b * KV b c1)]
    apply Nat.add_pos_left
    exact h3

--------------------------------------------------------------------------------
-- 588：まとめ：support(wCompList) の “存在” 表現
--------------------------------------------------------------------------------
theorem ex588 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys QK KV) a c
        ↔ ∃ b, b ∈ keys ∧ wSupp QK a b ∧ wSupp KV b c := by
  -- ヒント：ex586 と ex587

  -- keysの中に QK a b が0より大きい と KV b c が0より大きい
  -- の両方を満たすbが存在することと、
  -- wCompListの結果が0より大きいことは同値である。

  intro a1 c1

  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro hSupp
  -- theorem ex586 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     ∀ a c,
  --       wSupp (wCompList keys QK KV) a c →
  --         ∃ b, b ∈ keys ∧ wSupp QK a b ∧ wSupp KV b c := by
  obtain h2 := ex586 keys QK KV a1 c1 hSupp
  exact h2

  -- fRight
  intro hExist
  -- theorem ex587 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     ∀ a c,
  --       (∃ b, b ∈ keys ∧ wSupp QK a
  --         b ∧ wSupp KV b c) →
  --         wSupp (wCompList keys QK KV) a c := by
  obtain h2 := ex587 keys QK KV a1 c1 hExist
  exact h2

--------------------------------------------------------------------------------
-- 589：wCompList の support は boolean attention（attnRel）に含まれる
--------------------------------------------------------------------------------
theorem ex589 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK KV) ⊆ attnRel (wSupp QK) (wSupp KV) := by
  -- ヒント：attnRel = relComp。ex585 を使うだけ。

  -- def attnRel (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  --   relComp QK KV

  -- wCompList keys QK KV の support で (a,c) に到達できるなら、ある b ∈ keys を経由して
  -- wSupp QK a b と wSupp KV b c が成り立つ（ex588 の存在分解）。
  -- すると keys 条件を捨てても「ある b を経由して QK→KV で到達できる」ことは残る。
  -- よって wSupp (wCompList keys QK KV) は、support を通常の関係として合成した
  -- attnRel (wSupp QK) (wSupp KV) に含まれる。

  -- theorem ex585 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (wCompList keys QK KV) ⊆ relComp (wSupp QK) (wSupp KV) := by
  rw [attnRel]
  apply ex585

--------------------------------------------------------------------------------
-- 590：wMask すると support も ∧ で減る（support レベルの再掲）
--------------------------------------------------------------------------------
theorem ex590 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) ⊆ wSupp R := by
  -- wMask R M は、R に対して条件 M をかけて一部の重みを 0 にする（到達を削る）操作。
  -- wSupp は「重みが 0 でない＝到達が残っている」ペアだけを取り出す。
  -- したがって mask 後に support に残る (a,b) は、もともと R でも重みが 0 でなかったはず。
  -- よって wSupp (wMask R M) ⊆ wSupp R。

  -- ヒント：ex583 で右射影

  -- theorem ex583 (R : WRel α β) (M : Rel α β) :
  --     wSupp (wMask R M) = relMul (wSupp R) M := by
  rw [ex583]

  dsimp [RelLe]
  intro a1 b1 hRelMul
  dsimp [relMul] at hRelMul
  obtain ⟨hWSupp, hM⟩ := hRelMul
  exact hWSupp

--------------------------------------------------------------------------------
-- 591〜600：residual（rRes）で “安全な head” を設計する（support を介して）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 補助：KV と仕様 T から “安全な QK の条件” を作る
-- safeRel KV T a b  :=  ∀ c, (KV b c > 0) → T a c
--------------------------------------------------------------------------------
def safeRel (KV : WRel β γ) (T : Rel α γ) : Rel α β :=
  rRes (wSupp KV) T

--------------------------------------------------------------------------------
-- 591：residual の正しさ（boolean）：attnRel (KV▷T) KV ⊆ T
--------------------------------------------------------------------------------
theorem ex591 (KV : WRel β γ) (T : Rel α γ) :
    attnRel (safeRel (α:=α) KV T) (wSupp KV) ⊆ T := by
  -- ヒント：ex433 を (QK:=safeRel KV T), (KV:=wSupp KV) に適用して、
  --         右側は「X ⊆ X」で reflexive。

  -- safeRel KV T は「この b を経由して wSupp KV で到達できる先 c は、必ず T a c で許される」
  -- という安全条件を満たす (a,b) だけを集めた関係（安全な QK のフィルタ）。
  -- その safeRel で選んだ b に対して wSupp KV を合成すると、到達先は定義どおり常に T に入る。
  -- つまり「安全化してから attention（合成）すれば、仕様 T を破らない」。

  -- def rRes (S : Rel α γ) (T : Rel β γ) : Rel β α :=
  --   fun b a => ∀ c, S a c → T b c

  -- def safeRel (KV : WRel β γ) (T : Rel α γ) : Rel α β :=
  --   rRes (wSupp KV) T

  -- def attnRel (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  --   relComp QK KV

  -- theorem ex433 (QK : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
  --     (attnRel QK KV ⊆ T) ↔ (QK ⊆ rRes KV T) := by

  rw [ex433]
  dsimp [RelLe]
  intro a1 b1 hSafeRel c1 hSuppKV
  dsimp [safeRel] at hSafeRel
  dsimp [rRes] at hSafeRel
  apply hSafeRel
  exact hSuppKV

--------------------------------------------------------------------------------
-- 592：residual の最大性（boolean）：attnRel QK KV ⊆ T → QK ⊆ (KV▷T)
--------------------------------------------------------------------------------
theorem ex592 (QKrel : Rel α β) (KV : WRel β γ) (T : Rel α γ) :
    (attnRel QKrel (wSupp KV) ⊆ T) → (QKrel ⊆ safeRel (α:=α) KV T) := by
  -- ヒント：ex433 の (→) 方向

  rw [ex433]
  intro hRelLe1
  intro a1 b1 hQKrel c1 hSuppKV
  obtain hRelLe2 := hRelLe1 a1 b1
  apply hRelLe2
  exact hQKrel
  exact hSuppKV

--------------------------------------------------------------------------------
-- 593：wCompList の support は boolean attention に含まれる（再掲：接続の要）
--------------------------------------------------------------------------------
theorem ex593 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK KV) ⊆ attnRel (wSupp QK) (wSupp KV) := by
  -- ヒント：ex589

  -- theorem ex589 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (wCompList keys QK KV) ⊆ attnRel (wSupp QK) (wSupp KV) := by
  apply ex589

--------------------------------------------------------------------------------
-- 594：安全条件（support(QK) ⊆ KV▷T）なら、support(wCompList) ⊆ T
--------------------------------------------------------------------------------
theorem ex594 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ safeRel (α:=α) KV T) → (wSupp (wCompList keys QK KV) ⊆ T) := by
  -- ヒント：ex593 で boolean attention に押し上げ、ex591 で T に落とす（推移）

  -- theorem ex589 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (wCompList keys QK KV) ⊆ attnRel (wSupp QK) (wSupp KV) := by

  intro hSafeRel a1 g1 hSupp
  obtain hAttnRel := ex589 keys QK KV a1 g1 hSupp
  obtain ⟨b1, hWSuppQK, hWSuppKV⟩ := hAttnRel
  obtain hT := hSafeRel a1 b1 hWSuppQK g1 hWSuppKV
  exact hT

--------------------------------------------------------------------------------
-- 595：マスクした QK は “必ず” safeRel を満たす（support で見れば自明）
--------------------------------------------------------------------------------
theorem ex595 (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (wMask QK (safeRel (α:=α) KV T)) ⊆ safeRel (α:=α) KV T := by
  -- ヒント：ex583（support(wMask)=support∧mask）で右射影

  -- theorem ex583 (R : WRel α β) (M : Rel α β) :
  --     wSupp (wMask R M) = relMul (wSupp R) M := by

  rw [ex583]
  intro a1 b1 hwSupp1 g1 hwSupp2
  obtain ⟨hQK, hSafeRel⟩ := hwSupp1
  apply hSafeRel
  exact hwSupp2

--------------------------------------------------------------------------------
-- 596：設計：QK を safeRel でマスクすれば、縮約の support は必ず T に入る
--------------------------------------------------------------------------------
theorem ex596 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (wCompList keys (wMask QK (safeRel (α:=α) KV T)) KV) ⊆ T := by
  -- ヒント：ex594 に、ex595 を入れる
  intro a1 g1 hwSupp
  --dsimp [wSupp, wCompList, wMask, maskW, safeRel, rRes] at hwSupp

  -- obtain hSafeRel :=
  --   ex595 QK KV T

  -- obtain hT :=
  --   ex594 keys (wMask QK (safeRel (α:=α) KV T)) KV T hSafeRel a1 g1 hwSupp

  -- exact hT

  sorry



--------------------------------------------------------------------------------
-- 597：すでに安全ならマスクしても変わらない（wSupp を仮定にする版）
--------------------------------------------------------------------------------
theorem ex597 (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ safeRel (α:=α) KV T) →
      wMask QK (safeRel (α:=α) KV T) = QK := by
  -- ヒント：support(QK) で mask が True になることを使って funext で示す
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 598：safeRel は仕様 T に単調（T ⊆ T' なら safeRel KV T ⊆ safeRel KV T'）
--------------------------------------------------------------------------------
theorem ex598 (KV : WRel β γ) (T T' : Rel α γ) :
    (T ⊆ T') → (safeRel (α:=α) KV T ⊆ safeRel (α:=α) KV T') := by
  -- ヒント：safeRel は rRes (wSupp KV) T。ex483（rRes の右単調）を使う。
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 599：safeRel は KV（support）に反単調（KV が増えるほど safeRel は厳しくなる）
--------------------------------------------------------------------------------
theorem ex599 (KV KV' : WRel β γ) (T : Rel α γ) :
    (wSupp KV ⊆ wSupp KV') →
      (safeRel (α:=α) KV' T ⊆ safeRel (α:=α) KV T) := by
  -- ヒント：ex484（rRes の左反単調）
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 600：keys 付きの安全条件（必要十分に近い形）
-- 「keys に現れる b についてだけ」QK が安全なら、wCompList の support は T に入る
--------------------------------------------------------------------------------
theorem ex600 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (∀ a b, b ∈ keys → wSupp QK a b → safeRel (α:=α) KV T a b) →
      (wSupp (wCompList keys QK KV) ⊆ T) := by
  -- ヒント：ex588（存在表現）で witness b を取り、仮定で T を出す
  -- TODO
  sorry

end TL
