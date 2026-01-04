--------------------------------------------------------------------------------
-- 演習問題 301〜320（Tensor Logic / Attention 準備：Relational fragment）
-- ※ import Mathlib なしでOK
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

namespace TL

--------------------------------------------------------------------------------
-- 1) 「テンソル＝関数」: funext の練習
--------------------------------------------------------------------------------

def Tensor1 (ι κ : Type) := ι → κ
def Tensor2 (ι κ out : Type) := ι → κ → out

-- 301：Tensor1 の外延性（funext）
-- ヒント：intro h; funext i; exact h i
example {ι κ : Type} (t u : Tensor1 ι κ) :
    (∀ i, t i = u i) → t = u := by
  -- TODO
  sorry

-- 302：Tensor2 の外延性（funext 2回）
-- ヒント：intro h; funext i; funext j; exact h i j
example {ι κ out : Type} (f g : Tensor2 ι κ out) :
    (∀ i j, f i j = g i j) → f = g := by
  -- TODO
  sorry

-- 303：reindex（添字の付け替え）＝関数合成
def reindex {ι₁ ι₂ κ : Type} (σ : ι₂ → ι₁) (t : Tensor1 ι₁ κ) : Tensor1 ι₂ κ :=
  fun j => t (σ j)

-- reindex の合成則
-- ヒント：funext j; rfl
example {ι₁ ι₂ ι₃ κ : Type} (σ : ι₂ → ι₁) (ρ : ι₃ → ι₂) (t : Tensor1 ι₁ κ) :
    reindex ρ (reindex σ t) = reindex (fun k => σ (ρ k)) t := by
  -- TODO
  sorry

-- 304：Tensor2 の「左添字」だけ reindex
def reindexL {ι₁ ι₂ κ out : Type} (σ : ι₂ → ι₁) (t : Tensor2 ι₁ κ out) : Tensor2 ι₂ κ out :=
  fun i j => t (σ i) j

-- ヒント：funext i; funext j; rfl
example {ι₁ ι₂ ι₃ κ out : Type}
    (σ : ι₂ → ι₁) (ρ : ι₃ → ι₂) (t : Tensor2 ι₁ κ out) :
    reindexL ρ (reindexL σ t) = reindexL (fun k => σ (ρ k)) t := by
  -- TODO
  sorry

-- 305：「点ごとの等しさ ↔ 関数として等しい」
def TensorEq {ι κ : Type} (t u : Tensor1 ι κ) : Prop := ∀ i, t i = u i

-- ヒント：
--   (→) intro h; funext i; exact h i
--   (←) intro h i; rw [h]
example {ι κ : Type} (t u : Tensor1 ι κ) :
    TensorEq t u ↔ t = u := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 2) 「テンソル論理の核」: Prop値テンソル（関係）と収縮（∃, ∧）
--------------------------------------------------------------------------------

def Rel (α β : Type) := α → β → Prop

-- 関係の合成（＝ 収縮 / 最小の Einstein summation）
def relComp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, R a b ∧ S b c

def relAdd (R S : Rel α β) : Rel α β := fun a b => R a b ∨ S a b
def relMul (R S : Rel α β) : Rel α β := fun a b => R a b ∧ S a b

-- 306：relComp の結合律（点ごとの ↔）
-- (R;S);T ↔ R;(S;T)
example (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    ∀ a d, relComp (relComp R S) T a d ↔ relComp R (relComp S T) a d := by
  -- TODO
  sorry

-- 恒等関係（単位行列）
def relId (α : Type) : Rel α α := fun a b => a = b

-- 307：左単位元  id;R ↔ R
example (R : Rel α β) :
    ∀ a c, relComp (relId α) R a c ↔ R a c := by
  -- TODO
  sorry

-- 308：右単位元  R;id ↔ R
example (R : Rel α β) :
    ∀ a c, relComp R (relId β) a c ↔ R a c := by
  -- TODO
  sorry

-- 309：transpose（転置）を2回やると元に戻る
def relTrans (R : Rel α β) : Rel β α := fun b a => R a b

-- ヒント：funext b; funext a; rfl
example (R : Rel α β) : relTrans (relTrans R) = R := by
  -- TODO
  sorry

-- 310：tensor product（Kronecker積っぽい）
def relTensor (R : Rel α β) (S : Rel γ δ) : Rel (α × γ) (β × δ) :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2

-- 転置は tensor に分配する（定義通り）
example (R : Rel α β) (S : Rel γ δ) :
    relTrans (relTensor R S) = relTensor (relTrans R) (relTrans S) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 3) 推論の道具：単調性（⊆）と分配
--------------------------------------------------------------------------------

def RelLe (R S : Rel α β) : Prop := ∀ a b, R a b → S a b

-- 311：左分配  (R+S);T ↔ (R;T)+(S;T)
example (R S : Rel α β) (T : Rel β γ) :
    ∀ a c,
      relComp (relAdd R S) T a c ↔ relAdd (relComp R T) (relComp S T) a c := by
  -- TODO
  sorry

-- 312：右分配  R;(S+T) ↔ (R;S)+(R;T)
example (R : Rel α β) (S T : Rel β γ) :
    ∀ a c,
      relComp R (relAdd S T) a c ↔ relAdd (relComp R S) (relComp R T) a c := by
  -- TODO
  sorry

-- 313：RelLe は反射的
example (R : Rel α β) : RelLe R R := by
  -- TODO
  sorry

-- 314：RelLe は推移的
example (R S T : Rel α β) :
    RelLe R S → RelLe S T → RelLe R T := by
  -- TODO
  sorry

-- 315：relComp の単調性（両側）
example (R R' : Rel α β) (S S' : Rel β γ) :
    RelLe R R' → RelLe S S' → RelLe (relComp R S) (relComp R' S') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 4) Attention を「関係の合成」としてまず表す（論理版 attention）
--------------------------------------------------------------------------------

def attn (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  relComp QK KV

-- 316：attn の結合（＝ relComp の結合）
example (QK : Rel α β) (KK : Rel β γ) (KV : Rel γ δ) :
    ∀ q v, attn (attn QK KK) KV q v ↔ attn QK (attn KK KV) q v := by
  -- TODO
  sorry

-- 317：attn は左側で単調
example (QK QK' : Rel α β) (KV : Rel β γ) :
    RelLe QK QK' → RelLe (attn QK KV) (attn QK' KV) := by
  -- TODO
  sorry

-- 318：attn は右側で単調
example (QK : Rel α β) (KV KV' : Rel β γ) :
    RelLe KV KV' → RelLe (attn QK KV) (attn QK KV') := by
  -- TODO
  sorry

-- 319：マスク（∧）は元の関係の部分
example (QK M : Rel α β) :
    RelLe (relMul QK M) QK := by
  -- TODO
  sorry

-- 320：マスク付き attention はマスク無し attention の部分
example (QK M : Rel α β) (KV : Rel β γ) :
    RelLe (attn (relMul QK M) KV) (attn QK KV) := by
  -- TODO
  sorry

end TL
