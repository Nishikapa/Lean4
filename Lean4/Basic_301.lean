import Lean4.Basic_101
import Lean4.Basic_151
import Lean4.Basic_201

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
  intro a
  funext b
  apply a

-- 302：Tensor2 の外延性（funext 2回）
-- ヒント：intro h; funext i; funext j; exact h i j
example {ι κ out : Type} (f g : Tensor2 ι κ out) :
    (∀ i j, f i j = g i j) → f = g := by
  intro a
  funext b c
  apply a

-- 303：reindex（添字の付け替え）＝関数合成
def reindex {ι₁ ι₂ κ : Type} (σ : ι₂ → ι₁) (t : Tensor1 ι₁ κ) : Tensor1 ι₂ κ :=
  fun j => t (σ j)

-- reindex の合成則
-- ヒント：funext j; rfl
example {ι₁ ι₂ ι₃ κ : Type} (σ : ι₂ → ι₁) (ρ : ι₃ → ι₂) (t : Tensor1 ι₁ κ) :
    reindex ρ (reindex σ t) = reindex (fun k => σ (ρ k)) t := by
  funext a
  dsimp [reindex]

-- 304：Tensor2 の「左添字」だけ reindex
def reindexL {ι₁ ι₂ κ out : Type} (σ : ι₂ → ι₁) (t : Tensor2 ι₁ κ out) : Tensor2 ι₂ κ out :=
  fun i j => t (σ i) j

-- ヒント：funext i; funext j; rfl
example {ι₁ ι₂ ι₃ κ out : Type}
    (σ : ι₂ → ι₁) (ρ : ι₃ → ι₂) (t : Tensor2 ι₁ κ out) :
    reindexL ρ (reindexL σ t) = reindexL (fun k => σ (ρ k)) t := by
  funext a b
  dsimp [reindexL]

-- 305：「点ごとの等しさ ↔ 関数として等しい」
def TensorEq {ι κ : Type} (t u : Tensor1 ι κ) : Prop := ∀ i, t i = u i

-- ヒント：
--   (→) intro h; funext i; exact h i
--   (←) intro h i; rw [h]
example {ι κ : Type} (t u : Tensor1 ι κ) :
    TensorEq t u ↔ t = u := by

  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro a
  dsimp [TensorEq] at a
  dsimp [Tensor1] at t u
  funext b
  apply a

  -- hRight
  intro a
  dsimp [TensorEq]
  dsimp [Tensor1] at t u
  intro b
  rw [a]

--------------------------------------------------------------------------------
-- 2) 「テンソル論理の核」: Prop値テンソル（関係）と収縮（∃, ∧）
--------------------------------------------------------------------------------

-- ■ 二項関係 (Binary Relation)
-- 型 α の要素と 型 β の要素の間に「関係がある (Prop)」ことを表します。
-- 集合論的には「α × β の部分集合」、グラフ理論的には「α から β への有向辺の集合」と同じです。
def Rel (α β : Type) := α → β → Prop

-- ■ 関係の合成 (Composition)
-- 「a から b へ行き (R)、そこから c へ行く (S) 経路がある」こと。
-- 行列の乗算（ブール行列の積）と同じ構造です。
-- 記号では「R ; S」や「S ∘ R」と書かれます。
def relComp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, R a b ∧ S b c

-- ■ 関係の和 (Union / Join)
-- 「R または S のどちらかの経路がある」こと。
-- 集合としての「和集合 (R ∪ S)」に対応します。
def relAdd (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∨ S a b

-- ■ 関係の積 (Intersection / Meet)
-- 「R かつ S の両方の性質を持つ経路である」こと。
-- 集合としての「共通部分 (R ∩ S)」に対応します。
-- ※「積 (Mul)」という名前ですが、関係代数では共通部分（mask）として機能します。
def relMul (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∧ S a b

-- ■ 包含関係 (Inclusion / Less than or Equal)
-- 「R にある経路はすべて S にも含まれている」こと。
-- 集合の「部分集合 (R ⊆ S)」の関係であり、論理的には「ならば (→)」を含意します。
def RelLe (R S : Rel α β) : Prop :=
  ∀ a b, R a b → S a b

-- ■ 右残余 (Right Residual)
-- 関係代数における「割り算」のような操作です。ガロア接続（随伴）の片割れになります。
-- 意味：「S で a から行けるすべての先 c について、T でも b から c に行ける」ような (b, a) の関係。
-- 直感的には「S の行き先を T がカバーしているか」という包含チェックに近い操作です。
def rRes (S : Rel α γ) (T : Rel β γ) : Rel β α :=
  fun b a => ∀ c, S a c → T b c

-- ■ 転置 / 逆関係 (Transpose / Converse)
-- 矢印の向きを逆にした関係。
-- 「a から b への辺がある」を「b から a への辺がある」と読み替えます。
-- 行列の「転置行列」に対応します。記号では「Rᵀ」や「R⁻¹」と書かれます。
def relTrans (R : Rel α β) : Rel β α :=
  fun b a => R a b

-- ■ 恒等関係 (Identity)
-- 「自分自身へのループ」のみを持つ関係。
-- 行列における「単位行列（対角成分のみ1）」に対応します。
-- 何も移動しない（No-op）操作を表します。
def relId (α : Type) : Rel α α :=
  fun a b => a = b

-- 306：relComp の結合律（点ごとの ↔）
-- (R;S);T ↔ R;(S;T)
example (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    ∀ a d, relComp (relComp R S) T a d ↔ relComp R (relComp S T) a d := by
  intro a b
  dsimp [relComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, ⟨c2, c3, c4⟩, c5⟩ := c
  exists c2
  constructor
  exact c3
  exists c1

  -- hRight
  intro d
  obtain ⟨d1, d2, d3, d4, d5⟩ := d
  exists d3
  constructor
  exists d1
  exact d5

-- 307：左単位元  id;R ↔ R
example (R : Rel α β) :
    ∀ a c, relComp (relId α) R a c ↔ R a c := by
  intro a b
  dsimp [relComp, relId]
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro c
  obtain ⟨c1, c2, c3⟩ := c
  rw [c2]
  exact c3

  -- hRight
  intro d
  refine ⟨?b_1, ?x, ?y⟩

  -- b_1
  exact a

  -- x
  rfl

  -- y
  exact d

-- 308：右単位元  R;id ↔ R
example (R : Rel α β) :
    ∀ a c, relComp R (relId β) a c ↔ R a c := by

  intro a b
  dsimp [relComp, relId]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro ⟨c1, c2, c3⟩
  rw [←c3]
  exact c2

  -- hRight
  intro d
  refine ⟨?b_1, ?x, ?y⟩
  exact b

  -- x
  exact d

  -- y
  rfl

-- 309：transpose（転置）を2回やると元に戻る
-- ヒント：funext b; funext a; rfl
example (R : Rel α β) : relTrans (relTrans R) = R := by
  funext a b
  dsimp [relTrans]

-- 310：tensor product（Kronecker積っぽい）
def relTensor (R : Rel α β) (S : Rel γ δ) : Rel (α × γ) (β × δ) :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2

-- 転置は tensor に分配する（定義通り）
example (R : Rel α β) (S : Rel γ δ) :
    relTrans (relTensor R S) = relTensor (relTrans R) (relTrans S) := by
  funext a b
  dsimp [relTrans, relTensor]

--------------------------------------------------------------------------------
-- 3) 推論の道具：単調性（⊆）と分配
--------------------------------------------------------------------------------

-- 311：左分配  (R+S);T ↔ (R;T)+(S;T)
example (R S : Rel α β) (T : Rel β γ) :
    ∀ a c,
      relComp (relAdd R S) T a c ↔ relAdd (relComp R T) (relComp S T) a c := by
  intro a b
  dsimp [relComp, relAdd]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  rintro ⟨c1, c2 | c3, c4⟩

  -- hLeft.inl
  left
  exists c1

  -- hLeft.inr
  right
  exists c1

  -- hRight
  rintro (⟨d1, d2, d3⟩ | ⟨d4, d5, d6⟩)

  -- hRight.inl
  exists d1
  constructor

  -- hRight.inl.left
  left
  exact d2

  -- hRight.inl.right
  exact d3

  -- hRight.inr
  exists d4
  constructor

  -- hRight.inr.left
  right
  exact d5

  -- hRight.inr.right
  exact d6

-- 312：右分配  R;(S+T) ↔ (R;S)+(R;T)
example (R : Rel α β) (S T : Rel β γ) :
    ∀ a c,
      relComp R (relAdd S T) a c ↔ relAdd (relComp R S) (relComp R T) a c := by

  intro a b
  dsimp [relComp, relAdd]
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  rintro ⟨c1, c2, c3 | c4⟩
  -- hLeft.inl
  left
  exists c1
  -- hLeft.inr
  right
  exists c1
  -- hRight
  rintro (⟨d1, d2, d3⟩ | ⟨d4, d5, d6⟩)
  -- hRight.inl
  exists d1
  constructor
  -- hRight.inl.left
  exact d2
  -- hRight.inl.right
  left
  exact d3
  -- hRight.inr
  exists d4
  constructor
  -- hRight.inr.left
  exact d5
  -- hRight.inr.right
  right
  exact d6

-- 313：RelLe は反射的
example (R : Rel α β) : RelLe R R := by
  intro a b h
  exact h

-- 314：RelLe は推移的
example (R S T : Rel α β) :
    RelLe R S → RelLe S T → RelLe R T := by
  intro a b c d e
  dsimp [RelLe] at a b
  apply b
  apply a
  exact e

-- 315：relComp の単調性（両側）
example (R R' : Rel α β) (S S' : Rel β γ) :
    RelLe R R' → RelLe S S' → RelLe (relComp R S) (relComp R' S') := by
  intro a b c d e
  dsimp [RelLe, relComp] at a b e
  obtain ⟨e1, e2, e3⟩ := e
  dsimp [relComp]
  dsimp [Rel] at R R' S S'
  refine⟨?f, ?x, ?y⟩

  -- f
  exact e1

  -- x
  apply a
  exact e2

  -- y
  apply b
  exact e3

--------------------------------------------------------------------------------
-- 4) Attention を「関係の合成」としてまず表す（論理版 attention）
--------------------------------------------------------------------------------

def attn (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  relComp QK KV

-- 316：attn の結合（＝ relComp の結合）
example (QK : Rel α β) (KK : Rel β γ) (KV : Rel γ δ) :
    ∀ q v, attn (attn QK KK) KV q v ↔ attn QK (attn KK KV) q v := by
  intro a b
  dsimp [attn, relComp]
  dsimp [Rel] at QK KK KV
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, ⟨c2, c3, c4⟩, c5⟩ := c
  exists c2
  constructor

  -- hLeft.left
  exact c3

  -- hLeft.right
  exists c1

  -- hRight
  intro d
  obtain ⟨d1, d2, d3, d4, d5⟩ := d
  exists d3
  constructor

  -- hRight.left
  exists d1
  exact d5

-- 317：attn は左側で単調
example (QK QK' : Rel α β) (KV : Rel β γ) :
    RelLe QK QK' → RelLe (attn QK KV) (attn QK' KV) := by
  intro a b c d
  dsimp [RelLe, attn, relComp] at a d
  dsimp [attn, relComp]
  dsimp [Rel] at QK QK' KV
  obtain ⟨d1, d2, d3⟩ := d
  refine ⟨?f, ?x, ?y⟩

  -- f
  exact d1

  -- x
  apply a
  exact d2

  -- y
  exact d3

-- 318：attn は右側で単調
example (QK : Rel α β) (KV KV' : Rel β γ) :
    RelLe KV KV' → RelLe (attn QK KV) (attn QK KV') := by
  intro a b c d
  dsimp [RelLe, attn, relComp] at a d
  dsimp [attn, relComp]
  dsimp [Rel] at QK KV KV'
  obtain ⟨d1, d2, d3⟩ := d
  refine ⟨?f, ?x, ?y⟩

  -- f
  exact d1

  -- x
  exact d2

  -- y
  apply a
  exact d3

-- 319：マスク（∧）は元の関係の部分
example (QK M : Rel α β) :
    RelLe (relMul QK M) QK := by
  intro a b c
  dsimp [RelLe, relMul] at c
  dsimp [Rel] at QK M
  obtain ⟨c1, c2⟩ := c
  exact c1

-- 320：マスク付き attention はマスク無し attention の部分
example (QK M : Rel α β) (KV : Rel β γ) :
    RelLe (attn (relMul QK M) KV) (attn QK KV) := by
  intro a b c
  dsimp [RelLe, attn, relComp] at c
  dsimp [attn, relComp]
  dsimp [Rel] at QK M KV
  obtain ⟨c1, c2, c4⟩ := c
  dsimp [relMul] at c2
  obtain ⟨c5, c6⟩ := c2
  refine ⟨?f, ?x, ?y⟩
  -- f
  exact c1
  -- x
  exact c5
  -- y
  exact c4

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
--------------------------------------------------------------------------------
-- 演習問題 321〜340（Tensor Logic 続き：関係の代数 / テンソル積 / グラフ関係）
-- ※ import Mathlib なし
-- ※ 301〜320 の namespace TL の定義がある前提（追記用）
--------------------------------------------------------------------------------
variable {α β γ δ ε ζ : Type}
--------------------------------------------------------------------------------
-- 追加定義（便利ツール）
--------------------------------------------------------------------------------

def relZero (α β : Type) : Rel α β := fun _ _ => False

def relDom (R : Rel α β) : α → Prop := fun a => ∃ b, R a b
def relCod (R : Rel α β) : β → Prop := fun b => ∃ a, R a b

def relGuardL (A : α → Prop) (R : Rel α β) : Rel α β := fun a b => A a ∧ R a b
def relGuardR (B : β → Prop) (R : Rel α β) : Rel α β := fun a b => R a b ∧ B b

def funComp (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
def relOfFun (f : α → β) : Rel α β := fun a b => f a = b

--------------------------------------------------------------------------------
-- relAdd / relMul の「格子」性
--------------------------------------------------------------------------------

-- 321：relAdd は可換（点ごと ↔）
-- ヒント：constructor; intro h; cases h with | inl => ... | inr => ...
example (R S : Rel α β) :
    ∀ a b, relAdd R S a b ↔ relAdd S R a b := by
  intro a b
  dsimp [relAdd]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain (h : R a b) | (h : S a b) := c

  -- hLeft.inl
  right
  exact h

  -- hLeft.inr
  left
  exact h

  -- hRight
  intro d
  obtain (h : S a b) | (h : R a b) := d

  -- hRight.inl
  right
  exact h

  -- hRight.inr
  left
  exact h

-- 322：relAdd は結合的（点ごと ↔）
-- ヒント：cases で Or を2回さばく
example (R S T : Rel α β) :
    ∀ a b, relAdd (relAdd R S) T a b ↔ relAdd R (relAdd S T) a b := by

  intro a b
  dsimp [relAdd]
  dsimp [Rel] at R S T
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ((h: R a b) | (h : S a b)) | (h : T a b) := c

  -- hLeft.inl.inl
  left
  exact h

  -- hLeft.inl.inr
  right
  left
  exact h

  -- hLeft.inr
  right
  right
  exact h

  -- hRight
  intro d
  obtain (h : R a b) | ((h : S a b) | (h : T a b)) := d

  -- hRight.inl
  left
  left
  exact h

  -- hRight.inr.inl
  left
  right
  exact h

  -- hRight.inr.inr
  right
  exact h

-- 323：relAdd は冪等（R+R ↔ R）
example (R : Rel α β) :
    ∀ a b, relAdd R R a b ↔ R a b := by
  intro a b
  dsimp [relAdd]
  dsimp [Rel] at R
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain (h : R a b) | (h : R a b) := c

  -- hLeft.inl
  exact h

  -- hLeft.inr
  exact h

  -- hRight
  intro d
  left
  exact d

-- 324：relMul は可換（点ごと ↔）
-- ヒント：⟨h1,h2⟩ を ⟨h2,h1⟩ に入れ替える
example (R S : Rel α β) :
    ∀ a b, relMul R S a b ↔ relMul S R a b := by
  intro a b
  dsimp [relMul]
  dsimp [Rel] at R S
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨h1, h2⟩ := c
  exact ⟨h2, h1⟩

  -- hRight
  intro d
  obtain ⟨h1, h2⟩ := d
  exact ⟨h2, h1⟩

-- 325：relMul は結合的（点ごと ↔）
example (R S T : Rel α β) :
    ∀ a b, relMul (relMul R S) T a b ↔ relMul R (relMul S T) a b := by
  intro a b
  dsimp [relMul]
  dsimp [Rel] at R S T
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨⟨c1, c2⟩, c3⟩ := c
  exact ⟨c1, ⟨c2, c3⟩⟩

  -- hRight
  intro d
  obtain ⟨c1, ⟨c2, c3⟩⟩ := d
  exact ⟨⟨c1, c2⟩, c3⟩

-- 326：relMul は冪等（R∧R ↔ R）
example (R : Rel α β) :
    ∀ a b, relMul R R a b ↔ R a b := by
  intro a b
  dsimp [relMul]
  dsimp [Rel] at R
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨h1, h2⟩ := c
  exact h1

  -- hRight
  intro d
  exact ⟨d, d⟩

-- 327：吸収律  R ∧ (R ∨ S) ↔ R
-- ヒント：cases で (R a b ∨ S a b) を分岐
example (R S : Rel α β) :
    ∀ a b, relMul R (relAdd R S) a b ↔ R a b := by
  intro a b
  dsimp [relMul, relAdd]
  dsimp [Rel] at R S
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, c2 | c3⟩ := c

  -- hLeft.inl
  exact c1

  -- hLeft.inr
  exact c1

  -- hRight
  intro d
  constructor

  -- hRight.left
  exact d

  -- hRight.right
  left
  exact d

--------------------------------------------------------------------------------
-- 0（False関係）と合成
--------------------------------------------------------------------------------

-- 328：0 + R ↔ R
example (R : Rel α β) :
    ∀ a b, relAdd (relZero α β) R a b ↔ R a b := by
  intro a b
  dsimp [relAdd, relZero]
  dsimp [Rel] at R
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro c
  obtain (h : False) | (h : R a b) := c

  -- hLeft.inl
  contradiction

  -- hLeft.inr
  exact h

  -- hRight
  intro d
  right
  exact d

-- 329：0 ; R は常に False
-- 型に注意：0 : Rel α β, R : Rel β γ
example (R : Rel β γ) :
    ∀ a c, relComp (relZero α β) R a c ↔ False := by
  intro a b
  dsimp [relComp, relZero]
  dsimp [Rel] at R
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, c2, c3⟩ := c
  contradiction

  -- hRight
  intro d
  contradiction

-- 330：R ; 0 は常に False
example (R : Rel α β) :
    ∀ a c, relComp R (relZero β γ) a c ↔ False := by

  intro a b
  dsimp [relComp, relZero]
  dsimp [Rel] at R
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, c2, c3⟩ := c
  contradiction

  -- hRight
  intro d
  contradiction

--------------------------------------------------------------------------------
-- transpose（converse）と合成/加法
--------------------------------------------------------------------------------

-- 331：(R;S)ᵀ ↔ Sᵀ;Rᵀ（順番が逆になる）
-- ヒント：∃ の witness をそのまま使って、And の順番を入れ替える
example (R : Rel α β) (S : Rel β γ) :
    ∀ c a, relTrans (relComp R S) c a ↔ relComp (relTrans S) (relTrans R) c a := by
  intro a b
  dsimp [relTrans, relComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, c2, c3⟩ := c
  exists c1

  -- hRight.left
  intro d
  obtain ⟨d1, d2, d3⟩ := d
  exists d1

-- 332：(R+S)ᵀ ↔ Rᵀ + Sᵀ（点ごと ↔）
example (R S : Rel α β) :
    ∀ b a, relTrans (relAdd R S) b a ↔ relAdd (relTrans R) (relTrans S) b a := by

  intro a b
  dsimp [relTrans, relAdd]
  dsimp [Rel] at R S
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro c
  obtain (h : R b a) | (h : S b a) := c

  -- hLeft.inl
  left
  exact h

  -- hLeft.inr
  right
  exact h

  -- hRight
  intro d
  obtain (h : R b a) | (h : S b a) := d

  -- hRight.inl
  left
  exact h

  -- hRight.inr
  right
  exact h

--------------------------------------------------------------------------------
-- domain/codomain（関係の「定義域」「値域」）
--------------------------------------------------------------------------------

-- 333：dom(R;S) ⊆ dom(R)
-- ヒント：obtain ⟨b, hb⟩ := ...
example (R : Rel α β) (S : Rel β γ) :
    ∀ a, relDom (relComp R S) a → relDom R a := by

  intro a
  dsimp [relDom, relComp]
  dsimp [Rel] at R S

  intro c
  obtain ⟨c1, c2, c3, c4⟩ := c
  exists c2

-- 334：cod(R;S) ⊆ cod(S)
-- ヒント：∃a, ∃b, ... から ∃b, ... を作る
example (R : Rel α β) (S : Rel β γ) :
    ∀ c, relCod (relComp R S) c → relCod S c := by
  intro a
  dsimp [relCod, relComp]
  dsimp [Rel] at R S
  intro c
  obtain ⟨c1, c2, c3, c4⟩ := c
  exists c2

--------------------------------------------------------------------------------
-- ガード（∧で条件を付ける）を ∃ の外に出す
--------------------------------------------------------------------------------

-- 335：左ガードは合成の外へ出せる
-- relComp ((A∧R)) S ↔ A ∧ relComp R S
example (A : α → Prop) (R : Rel α β) (S : Rel β γ) :
    ∀ a c, relComp (relGuardL A R) S a c ↔ A a ∧ relComp R S a c := by
  intro a b
  dsimp [relComp, relGuardL]
  dsimp [Rel] at R S
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, ⟨c2, c3⟩, c4⟩ := c
  constructor

  -- hLeft.left
  exact c2

  -- hLeft.right
  exists c1

  -- hRight
  intro d
  obtain ⟨d1, ⟨d2, d3, d4⟩⟩ := d
  exists d2

-- 336：右ガードも合成の外へ出せる
-- relComp R (S∧B) ↔ (relComp R S) ∧ B
example (B : γ → Prop) (R : Rel α β) (S : Rel β γ) :
    ∀ a c, relComp R (relGuardR B S) a c ↔ relComp R S a c ∧ B c := by

  intro a b
  dsimp [relComp, relGuardR]
  dsimp [Rel] at R S
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro c
  obtain ⟨c1, c2, ⟨c3, c4⟩⟩ := c
  constructor
  -- hLeft.left
  exists c1
  -- hLeft.right
  exact c4
  -- hRight
  intro d
  obtain ⟨⟨d1, d2, d3⟩, d4⟩ := d
  exists d1

--------------------------------------------------------------------------------
-- 関数を「関係（グラフ）」として扱う
--------------------------------------------------------------------------------

-- 337：グラフの合成は関数合成に一致
-- relOfFun f ; relOfFun g ↔ relOfFun (g∘f)
example (f : α → β) (g : β → γ) :
    ∀ a c, relComp (relOfFun f) (relOfFun g) a c ↔ relOfFun (funComp g f) a c := by
  intro a b
  dsimp [relComp, relOfFun, funComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1, c2, c3⟩ := c
  rw [c2]
  exact c3

  -- hRight
  intro d
  exists (f a)


-- 338：恒等関数のグラフ ↔ relId
example :
    ∀ a b : α, relOfFun (fun x : α => x) a b ↔ relId α a b := by
  intro a b
  dsimp [relOfFun, relId]
  rfl

--------------------------------------------------------------------------------
-- tensor（⊗）と合成：interchange law（モノイダル圏っぽい核心）
--------------------------------------------------------------------------------

-- 339：テンソルと合成の入れ替え（interchange）
-- (R1⊗S1);(R2⊗S2) ↔ (R1;R2)⊗(S1;S2)
-- ヒント：
--   左：witness は (b,e) : (β×ε)
--   右：witness は b と e に分解できる
example (R1 : Rel α β) (R2 : Rel β γ) (S1 : Rel δ ε) (S2 : Rel ε ζ) :
    ∀ p q,
      relComp (relTensor R1 S1) (relTensor R2 S2) p q
        ↔ relTensor (relComp R1 R2) (relComp S1 S2) p q := by
  intro p q
  dsimp [relComp, relTensor]
  dsimp [Rel] at R1 R2 S1 S2
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  obtain ⟨⟨b1,b2⟩,⟨c1,c2⟩,d,e⟩ := a
  constructor

  -- hLeft.left
  exists b1

  -- hLeft.right
  exists b2

  -- hRight
  intro f
  obtain ⟨⟨f1,f2,f3⟩, f4, ⟨f5, f6⟩⟩ := f
  exists (f1, f4)

-- 340：tensor は relAdd に分配（左側）
-- (R+S)⊗T ↔ (R⊗T) + (S⊗T)
-- ヒント：((A∨B)∧C) ↔ ((A∧C)∨(B∧C)) を cases で作る
example (R S : Rel α β) (T : Rel γ δ) :
    ∀ p q,
      relTensor (relAdd R S) T p q ↔
        relAdd (relTensor R T) (relTensor S T) p q := by
  intro a b
  dsimp [relTensor, relAdd]
  dsimp [Rel] at R S T
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨(c1 : R a.1 b.1) | (c1 : S a.1 b.1), c2⟩ := c

  -- hLeft.inl
  left
  constructor

  -- hLeft.inl.h.left
  exact c1

  -- hLeft.inl.h.right
  exact c2

  -- hLeft.inr
  right
  constructor

  -- hLeft.inr.h.left
  exact c1

  -- hLeft.inr.h.right
  exact c2

  -- hRight
  intro d

  obtain ⟨d1, d2⟩ | ⟨d1, d2⟩ := d

  -- hRight.inl
  constructor

  -- hRight.inl.left
  left
  exact d1

  -- hRight.inl.right
  exact d2

  -- hRight.inr
  constructor

  -- hRight.inr.left
  right
  exact d1

  -- hRight.inr.right
  exact d2

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆

--------------------------------------------------------------------------------
-- 演習問題 341〜350（次レベル：包含(⊆)中心 / 残余(residuation)入門 / 閉包の入口）
-- ※ import Mathlib なし
--------------------------------------------------------------------------------

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 準備：包含（RelLe）を infix にする（読みやすさ用）
--------------------------------------------------------------------------------
infix:50 " ⊆ " => RelLe

--------------------------------------------------------------------------------
-- 341：⊆ の反対称（点ごとの同値 → 関係の等しさ）
-- R ⊆ S と S ⊆ R なら R = S
--
-- ヒント：
--   funext a; funext b;
--   apply propext; constructor; intro h; ...
example (R S : Rel α β) : (R ⊆ S) → (S ⊆ R) → R = S := by
  intro a b
  funext c d
  dsimp [RelLe] at a b
  dsimp [Rel] at R S
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h
  apply a
  exact h

  -- hRight
  intro h
  apply b
  exact h

--------------------------------------------------------------------------------
-- 342：relAdd は最小上界（join）その1：R ⊆ R+S
-- ヒント：intro a b h; left; exact h
example (R S : Rel α β) : R ⊆ relAdd R S := by
  dsimp [RelLe, relAdd]
  dsimp [Rel] at R S
  intro a b c
  left
  exact c

-- 343：relAdd は最小上界（join）その2：S ⊆ R+S
example (R S : Rel α β) : S ⊆ relAdd R S := by
  dsimp [RelLe, relAdd]
  dsimp [Rel] at R S
  intro a b c
  right
  exact c

-- 344：relAdd は最小上界（join）その3：R ⊆ T と S ⊆ T なら (R+S) ⊆ T
-- ヒント：intro a b h; cases h with | inl => ... | inr => ...
example (R S T : Rel α β) : (R ⊆ T) → (S ⊆ T) → relAdd R S ⊆ T := by
  dsimp [RelLe, relAdd]
  dsimp [Rel] at R S T
  intro a b c d e
  obtain (h : R c d) | (h : S c d) := e

  -- inl
  apply a
  exact h

  -- inr
  apply b
  exact h

--------------------------------------------------------------------------------
-- 345：relMul は最大下界（meet）その1：(R∧S) ⊆ R
-- 319 の一般版（型を合わせて）
example (R S : Rel α β) : relMul R S ⊆ R := by
  dsimp [RelLe, relMul]
  dsimp [Rel] at R S
  intro a b c
  obtain ⟨c1, c2⟩ := c
  exact c1

-- 346：relMul は最大下界（meet）その2：T ⊆ R と T ⊆ S なら T ⊆ (R∧S)
-- ヒント：intro a b ht; exact ⟨hTR _ _ ht, hTS _ _ ht⟩
example (R S T : Rel α β) : (T ⊆ R) → (T ⊆ S) → T ⊆ relMul R S := by
  dsimp [RelLe, relMul]
  dsimp [Rel] at R S T
  intro a b c d e
  constructor

  -- left
  apply a
  exact e

  -- right
  apply b
  exact e

--------------------------------------------------------------------------------
-- 347：relComp の単調性（片側版）
-- R ⊆ R' なら (R;S) ⊆ (R';S)
-- ヒント：315 の片側（右側は同じ）
example (R R' : Rel α β) (S : Rel β γ) :
    (R ⊆ R') → relComp R S ⊆ relComp R' S := by
  dsimp [RelLe, relComp]
  dsimp [Rel] at R R' S
  intro a b c d
  obtain ⟨d1, d2, d3⟩ := d
  refine ⟨?e, ?f, ?g⟩

  -- e
  exact d1

  -- f
  apply a
  exact d2

  -- g
  exact d3

-- 348：relComp の単調性（もう片側）
-- S ⊆ S' なら (R;S) ⊆ (R;S')
example (R : Rel α β) (S S' : Rel β γ) :
    (S ⊆ S') → relComp R S ⊆ relComp R S' := by
  dsimp [RelLe, relComp]
  dsimp [Rel] at R S S'
  intro a b c d
  obtain ⟨d1, d2, d3⟩ := d
  refine ⟨?e, ?f, ?g⟩

  -- e
  exact d1

  -- f
  exact d2

  -- g
  apply a
  exact d3

--------------------------------------------------------------------------------
-- 349：transpose は包含を反転しない（単調）
-- R ⊆ S なら Rᵀ ⊆ Sᵀ
--
-- ヒント：intro b a h; exact hRS a b h
example (R S : Rel α β) :
    (R ⊆ S) → relTrans R ⊆ relTrans S := by
  dsimp [RelLe, relTrans]
  dsimp [Rel] at R S
  intro a b c d
  apply a
  exact d

--------------------------------------------------------------------------------
-- 350：残余（右残余）の導入：S ⊳ T
-- 「b から始めて S を通った先はすべて T に入る」という関係
--
-- 定義：S ▷ T : Rel β α   （注意：型がひっくり返る）
--   (S ▷ T) b a  := ∀ c, S a c → T b c
--
-- 目標：residuation（片方向でOK）：
--   (R;S) ⊆ T  →  R ⊆ (S ▷ T)
--
-- これはテンソル論理の「含意」の超入門です。
example (R : Rel β α) (S : Rel α γ) (T : Rel β γ) :
    (relComp R S ⊆ T) → (R ⊆ rRes S T) := by
  dsimp [RelLe, relComp, rRes]
  dsimp [Rel] at R S T
  intro a b c d e f
  apply a
  refine ⟨?g, ?h, ?i⟩

  -- g
  exact c

  -- h
  exact d

  -- i
  exact f

end TL

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
