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

-- 恒等関係（単位行列）
def relId (α : Type) : Rel α α := fun a b => a = b

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
def relTrans (R : Rel α β) : Rel β α := fun b a => R a b

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

def RelLe (R S : Rel α β) : Prop := ∀ a b, R a b → S a b

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
  -- TODO
  sorry

-- 322：relAdd は結合的（点ごと ↔）
-- ヒント：cases で Or を2回さばく
example (R S T : Rel α β) :
    ∀ a b, relAdd (relAdd R S) T a b ↔ relAdd R (relAdd S T) a b := by
  -- TODO
  sorry

-- 323：relAdd は冪等（R+R ↔ R）
example (R : Rel α β) :
    ∀ a b, relAdd R R a b ↔ R a b := by
  -- TODO
  sorry

-- 324：relMul は可換（点ごと ↔）
-- ヒント：⟨h1,h2⟩ を ⟨h2,h1⟩ に入れ替える
example (R S : Rel α β) :
    ∀ a b, relMul R S a b ↔ relMul S R a b := by
  -- TODO
  sorry

-- 325：relMul は結合的（点ごと ↔）
example (R S T : Rel α β) :
    ∀ a b, relMul (relMul R S) T a b ↔ relMul R (relMul S T) a b := by
  -- TODO
  sorry

-- 326：relMul は冪等（R∧R ↔ R）
example (R : Rel α β) :
    ∀ a b, relMul R R a b ↔ R a b := by
  -- TODO
  sorry

-- 327：吸収律  R ∧ (R ∨ S) ↔ R
-- ヒント：cases で (R a b ∨ S a b) を分岐
example (R S : Rel α β) :
    ∀ a b, relMul R (relAdd R S) a b ↔ R a b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 0（False関係）と合成
--------------------------------------------------------------------------------

-- 328：0 + R ↔ R
example (R : Rel α β) :
    ∀ a b, relAdd (relZero α β) R a b ↔ R a b := by
  -- TODO
  sorry

-- 329：0 ; R は常に False
-- 型に注意：0 : Rel α β, R : Rel β γ
example (R : Rel β γ) :
    ∀ a c, relComp (relZero α β) R a c ↔ False := by
  -- TODO
  sorry

-- 330：R ; 0 は常に False
example (R : Rel α β) :
    ∀ a c, relComp R (relZero β γ) a c ↔ False := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- transpose（converse）と合成/加法
--------------------------------------------------------------------------------

-- 331：(R;S)ᵀ ↔ Sᵀ;Rᵀ（順番が逆になる）
-- ヒント：∃ の witness をそのまま使って、And の順番を入れ替える
example (R : Rel α β) (S : Rel β γ) :
    ∀ c a, relTrans (relComp R S) c a ↔ relComp (relTrans S) (relTrans R) c a := by
  -- TODO
  sorry

-- 332：(R+S)ᵀ ↔ Rᵀ + Sᵀ（点ごと ↔）
example (R S : Rel α β) :
    ∀ b a, relTrans (relAdd R S) b a ↔ relAdd (relTrans R) (relTrans S) b a := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- domain/codomain（関係の「定義域」「値域」）
--------------------------------------------------------------------------------

-- 333：dom(R;S) ⊆ dom(R)
-- ヒント：obtain ⟨b, hb⟩ := ...
example (R : Rel α β) (S : Rel β γ) :
    ∀ a, relDom (relComp R S) a → relDom R a := by
  -- TODO
  sorry

-- 334：cod(R;S) ⊆ cod(S)
-- ヒント：∃a, ∃b, ... から ∃b, ... を作る
example (R : Rel α β) (S : Rel β γ) :
    ∀ c, relCod (relComp R S) c → relCod S c := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- ガード（∧で条件を付ける）を ∃ の外に出す
--------------------------------------------------------------------------------

-- 335：左ガードは合成の外へ出せる
-- relComp ((A∧R)) S ↔ A ∧ relComp R S
example (A : α → Prop) (R : Rel α β) (S : Rel β γ) :
    ∀ a c, relComp (relGuardL A R) S a c ↔ A a ∧ relComp R S a c := by
  -- TODO
  sorry

-- 336：右ガードも合成の外へ出せる
-- relComp R (S∧B) ↔ (relComp R S) ∧ B
example (B : γ → Prop) (R : Rel α β) (S : Rel β γ) :
    ∀ a c, relComp R (relGuardR B S) a c ↔ relComp R S a c ∧ B c := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 関数を「関係（グラフ）」として扱う
--------------------------------------------------------------------------------

-- 337：グラフの合成は関数合成に一致
-- relOfFun f ; relOfFun g ↔ relOfFun (g∘f)
example (f : α → β) (g : β → γ) :
    ∀ a c, relComp (relOfFun f) (relOfFun g) a c ↔ relOfFun (funComp g f) a c := by
  -- TODO
  sorry

-- 338：恒等関数のグラフ ↔ relId
example :
    ∀ a b : α, relOfFun (fun x : α => x) a b ↔ relId α a b := by
  -- TODO
  sorry

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
  -- TODO
  sorry

-- 340：tensor は relAdd に分配（左側）
-- (R+S)⊗T ↔ (R⊗T) + (S⊗T)
-- ヒント：((A∨B)∧C) ↔ ((A∧C)∨(B∧C)) を cases で作る
example (R S : Rel α β) (T : Rel γ δ) :
    ∀ p q,
      relTensor (relAdd R S) T p q ↔
        relAdd (relTensor R T) (relTensor S T) p q := by
  -- TODO
  sorry

end TL

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
