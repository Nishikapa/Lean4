--------------------------------------------------------------------------------
-- Basic_401.lean
-- 演習問題 401〜420（実践寄せ：残余のカリー化 / ∀逆像の計算則 / reach・must）
-- ※ import Mathlib なし（Lean4 core のみ）
--------------------------------------------------------------------------------

namespace TL

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 0) 基本定義：Relation / 合成 / 和 / 積 / 反転 / 恒等 / 包含
--------------------------------------------------------------------------------

def Rel (α β : Type) := α → β → Prop

def relComp {α β γ : Type} (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, R a b ∧ S b c

def relAdd {α β : Type} (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∨ S a b

def relMul {α β : Type} (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∧ S a b

def relTrans {α β : Type} (R : Rel α β) : Rel β α :=
  fun b a => R a b

def relId (α : Type) : Rel α α :=
  fun a b => a = b

def RelLe {α β : Type} (R S : Rel α β) : Prop :=
  ∀ a b, R a b → S a b

infix:50 " ⊆ " => RelLe

--------------------------------------------------------------------------------
-- 1) 残余（テンソル論理の含意の原型）
--------------------------------------------------------------------------------

-- 右残余：S ▷ T（型がひっくり返る点に注意）
def rRes {α β γ : Type} (S : Rel α γ) (T : Rel β γ) : Rel β α :=
  fun b a => ∀ c, S a c → T b c

-- 左残余：R ⊲ T
def lRes {α β γ : Type} (R : Rel α β) (T : Rel α γ) : Rel β γ :=
  fun b c => ∀ a, R a b → T a c

--------------------------------------------------------------------------------
-- 2) Pred（集合）側：像 / 逆像 / ∀逆像（must の基礎）
--------------------------------------------------------------------------------

def Pred (X : Type) := X → Prop

def PredLe {X : Type} (A B : Pred X) : Prop :=
  ∀ x, A x → B x

infix:50 " ⊆ₚ " => PredLe

def predAdd {X : Type} (A B : Pred X) : Pred X := fun x => A x ∨ B x
def predMul {X : Type} (A B : Pred X) : Pred X := fun x => A x ∧ B x

-- ∃-像（到達）
def relImg {α β : Type} (R : Rel α β) (A : Pred α) : Pred β :=
  fun b => ∃ a, A a ∧ R a b

-- ∃-逆像
def relPre {α β : Type} (R : Rel α β) (B : Pred β) : Pred α :=
  fun a => ∃ b, R a b ∧ B b

-- ∀-逆像（安全側）
def relPreAll {α β : Type} (R : Rel α β) (B : Pred β) : Pred α :=
  fun a => ∀ b, R a b → B b

--------------------------------------------------------------------------------
-- 3) 関数をグラフ関係として扱う
--------------------------------------------------------------------------------

def relGraph {α β : Type} (f : α → β) : Rel α β :=
  fun a b => f a = b

--------------------------------------------------------------------------------
-- 4) pow / star（反復合成＝到達可能性）
--------------------------------------------------------------------------------

def relPow {α : Type} (R : Rel α α) : Nat → Rel α α
  | 0          => relId α
  | Nat.succ n => relComp (relPow R n) R

def relStar {α : Type} (R : Rel α α) : Rel α α :=
  fun a b => ∃ n, relPow R n a b

--------------------------------------------------------------------------------
-- 5) reach / must（実務っぽく使うための道具）
--------------------------------------------------------------------------------

def reach {α : Type} (R : Rel α α) (A : Pred α) : Pred α :=
  relImg (relStar R) A

def Closed {α : Type} (R : Rel α α) (B : Pred α) : Prop :=
  relImg R B ⊆ₚ B

def must {α : Type} (R : Rel α α) (B : Pred α) : Pred α :=
  relPreAll (relStar R) B

--------------------------------------------------------------------------------
-- 401〜420：演習
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 401：右残余の「カリー化」：合成が含意のネストになる（超重要）
-- rRes (S;U) T = rRes S (rRes U T)
--------------------------------------------------------------------------------
theorem ex401 (S : Rel α β) (U : Rel β γ) (T : Rel δ γ) :
    rRes (relComp S U) T = rRes S (rRes U T) := by
  funext c1 a1
  dsimp [rRes, relComp]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 b1 h2 g1 h3
  apply h1
  exists b1

  -- hRight
  intro h1 g1 h2
  obtain ⟨b1, h4, h5⟩ := h2
  have h3 : S a1 b1 → U b1 g1 → T c1 g1 := by
    intro b2 h6
    apply h1 b1 h4
    exact h6
  apply h3
  exact h4
  exact h5

--------------------------------------------------------------------------------
-- 402：左残余の「カリー化」
-- lRes (R;S) T = lRes S (lRes R T)
--------------------------------------------------------------------------------
theorem ex402 (R : Rel α β) (S : Rel β γ) (T : Rel α δ) :
    lRes (relComp R S) T = lRes S (lRes R T) := by
  funext g1 c1
  dsimp [lRes, relComp]
  apply propext
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h1 b1 h2 a1 h3
  apply h1 a1
  exists b1
  -- hRight
  intro h1 a1 h2
  obtain ⟨b1, h4, h5⟩ := h2
  apply h1 b1
  exact h5
  exact h4

--------------------------------------------------------------------------------
-- 403：∀逆像（preAll）は合成に関して “結合的”
-- preAll (R;S) C = preAll R (preAll S C)
--------------------------------------------------------------------------------
theorem ex403 (R : Rel α β) (S : Rel β γ) (C : Pred γ) :
    relPreAll (relComp R S) C = relPreAll R (relPreAll S C) := by

  funext a1
  dsimp [relPreAll, relComp]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 b1 h2 g1 h3
  apply h1
  exists b1

  -- hRight
  intro h1 g1 h2
  obtain ⟨b1, h4, h5⟩ := h2
  have h3 : R a1 b1 → S b1 g1 → C g1 := by
    intro b2 h6
    apply h1 b1 h4
    exact h6
  apply h3
  exact h4
  exact h5

--------------------------------------------------------------------------------
-- 404：∀逆像は「和（∨）」を「積（∧）」に変える
-- preAll (R+S) C = preAll R C ∧ preAll S C
--------------------------------------------------------------------------------
theorem ex404 (R S : Rel α β) (C : Pred β) :
    relPreAll (relAdd R S) C = predMul (relPreAll R C) (relPreAll S C) := by
  funext a1
  dsimp [relPreAll, relAdd, predMul]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  constructor

  -- hLeft.left
  intro b1 h2
  apply h1
  left
  exact h2

  -- hLeft.right
  intro b1 h2
  apply h1
  right
  exact h2

  -- hRight
  intro h1 b1 h2
  obtain ⟨h3, h4⟩ := h1
  obtain h5 | h6 := h2
  apply h3
  exact h5
  apply h4
  exact h6

--------------------------------------------------------------------------------
-- 405：像は「和（∨）」に分配する
-- Img (R+S) A = Img R A ∪ Img S A
--------------------------------------------------------------------------------
theorem ex405 (R S : Rel α β) (A : Pred α) :
    relImg (relAdd R S) A = predAdd (relImg R A) (relImg S A) := by
  funext b1
  dsimp [relImg, relAdd, predAdd]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  obtain ⟨a1, h2, h3⟩ := h1
  obtain h4 | h5 := h3

  -- hLeft.inl
  left
  exists a1

  -- hLeft.inr
  right
  exists a1

  -- hRight
  intro h1
  obtain h2 | h3 := h1

  -- hRight.inl
  obtain ⟨a1, h4, h5⟩ := h2
  exists a1
  constructor
  exact h4
  left
  exact h5

  -- hRight.inr
  obtain ⟨a1, h4, h5⟩ := h3
  exists a1
  constructor
  exact h4
  right
  exact h5

--------------------------------------------------------------------------------
-- 406：像は「積（∧）」に“片方向”で反映される
-- Img (R∧S) A ⊆ Img R A ∩ Img S A
--------------------------------------------------------------------------------
theorem ex406 (R S : Rel α β) (A : Pred α) :
    (relImg (relMul R S) A ⊆ₚ predMul (relImg R A) (relImg S A)) := by
  dsimp [relImg, relMul, predMul, PredLe]
  intro b1 h1
  obtain ⟨a1, h2, ⟨h3,h4⟩⟩ := h1
  constructor
  -- left
  exists a1
  -- right
  exists a1

--------------------------------------------------------------------------------
-- 407：ガロア対応の unit 形
-- A ⊆ preAll R (Img R A)
--------------------------------------------------------------------------------
theorem ex407 (R : Rel α β) (A : Pred α) :
    (A ⊆ₚ relPreAll R (relImg R A)) := by
  dsimp [relImg, relPreAll, PredLe]
  intro a1 h1 b1 h2
  exists a1

--------------------------------------------------------------------------------
-- 408：ガロア対応の counit 形
-- Img R (preAll R B) ⊆ B
--------------------------------------------------------------------------------
theorem ex408 (R : Rel α β) (B : Pred β) :
    (relImg R (relPreAll R B) ⊆ₚ B) := by
  dsimp [relImg, relPreAll, PredLe]
  intro b1 h1
  obtain ⟨a1, h2, h3⟩ := h1
  apply h2
  exact h3

--------------------------------------------------------------------------------
-- 409：reach は単調（A ⊆ B なら reach R A ⊆ reach R B）
--------------------------------------------------------------------------------
theorem ex409 (R : Rel α α) (A B : Pred α) :
    (A ⊆ₚ B) → (reach R A ⊆ₚ reach R B) := by
  dsimp [reach, relImg, relStar, PredLe]
  intro h1 b1 h2
  obtain ⟨a1, h3, ⟨n1, h4⟩⟩ := h2
  exists a1
  constructor

  -- left
  apply h1
  exact h3

  -- right
  exists n1

--------------------------------------------------------------------------------
-- 410：reach は冪等（reach R (reach R A) = reach R A）
--------------------------------------------------------------------------------

theorem ex367 (R : Rel α α) :
    ∀ m n, RelLe (relComp (relPow R m) (relPow R n)) (relPow R (m + n)) := by
  intro a b
  induction b with
  | zero =>
    dsimp [relPow, relId]
    intro c d e
    obtain ⟨e1, e2, e3⟩ := e
    rw [←e3]
    exact e2
  | succ n ih =>
    dsimp [RelLe]
    intro c d e
    dsimp [relPow, relComp] at e
    obtain ⟨e1, e2, ⟨e3, e4, e5⟩⟩ := e
    rw [Nat.add_succ]
    dsimp [relPow, relComp]
    refine ⟨e3, ?f, ?g⟩
    apply ih
    exists e1
    exact e5

theorem ex410 (R : Rel α α) (A : Pred α) :
    reach R (reach R A) = reach R A := by
  funext b1
  dsimp [reach, relImg, relStar]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  obtain ⟨a1, h2, ⟨n1, h3⟩⟩ := h1
  obtain ⟨a2, h4, ⟨n2, h5⟩⟩ := h2
  exists a2
  constructor

  -- hLeft.left
  exact h4

  -- hLeft.right
  exists (n2 + n1)
  apply ex367 R n2 n1
  dsimp [relComp]
  exists a1

  -- hRight
  intro h1
  obtain ⟨a1, h2, ⟨n1, h3⟩⟩ := h1
  exists a1
  constructor

  -- hRight.left
  exists a1
  constructor

  -- hRight.left.left
  exact h2

  -- hRight.left.right
  exists 0

  -- hRight.right
  exists n1

--------------------------------------------------------------------------------
-- 411：不変集合 B を含むなら、到達集合もそこから出ない
-- A ⊆ B かつ Closed R B なら reach R A ⊆ B
--------------------------------------------------------------------------------




theorem ex411_pre (R : Rel α α) :
  ∀ m, RelLe (relComp (relPow R m) R) (relPow R (m + 1)) := by
  intro n
  dsimp [RelLe]
  intro a1 a2 h1
  dsimp [relComp] at h1
  dsimp [relPow, relComp]
  exact h1

theorem ex411 (R : Rel α α) (A B : Pred α) :
    (A ⊆ₚ B) → Closed R B → (reach R A ⊆ₚ B) := by

  dsimp [reach, relImg, relStar, Closed, PredLe]
  dsimp [Pred] at A B
  dsimp [Rel] at R
  intro h1 h2

  intro a1 h3
  obtain ⟨a2, h4, ⟨n1, h5⟩⟩ := h3
  revert a1

  have h6 : ∀ a3, relPow R n1 a2 a3 → B a3 := by
    induction n1 with
    | zero =>
      intro a3
      dsimp [relPow, relId]
      intro h7
      rw [←h7]
      apply h1
      exact h4
    | succ n2 ih =>
      intro a3 h7
      dsimp [relPow, relComp] at h7
      obtain ⟨a4, h8, h9⟩ := h7
      apply h2
      exists a4
      constructor
      apply ih
      exact h8
      exact h9

  intro a5 h7
  apply h6
  exact h7

--------------------------------------------------------------------------------
-- 412：reach R A は Closed（到達集合は一歩進んでも閉じている）
--------------------------------------------------------------------------------
theorem ex412 (R : Rel α α) (A : Pred α) :
    Closed R (reach R A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 413：A が Closed なら reach R A = A
--------------------------------------------------------------------------------
theorem ex413 (R : Rel α α) (A : Pred α) :
    Closed R A → reach R A = A := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 414：must は B に単調
--------------------------------------------------------------------------------
theorem ex414 (R : Rel α α) (B C : Pred α) :
    (B ⊆ₚ C) → (must R B ⊆ₚ must R C) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 415：must は 1ステップ後でも保たれる（安全性の伝播）
-- must R B ⊆ preAll R (must R B)
--------------------------------------------------------------------------------
theorem ex415 (R : Rel α α) (B : Pred α) :
    (must R B ⊆ₚ relPreAll R (must R B)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 416：reach と must のガロア対応（star 版）
-- reach R A ⊆ B  ↔  A ⊆ must R B
--------------------------------------------------------------------------------
theorem ex416 (R : Rel α α) (A B : Pred α) :
    (reach R A ⊆ₚ B) ↔ (A ⊆ₚ must R B) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- Nat / iterate（関数反復）
--------------------------------------------------------------------------------

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0          => fun x => x
  | Nat.succ n => fun x => f (iter f n x)

--------------------------------------------------------------------------------
-- 417：graph f の pow は iterate に一致
-- relPow (graph f) n a b ↔ iter f n a = b
--------------------------------------------------------------------------------
theorem ex417 (f : α → α) :
    ∀ n a b, relPow (relGraph f) n a b ↔ iter f n a = b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 418：graph f の star は「ある回数だけ iterate して到達」
--------------------------------------------------------------------------------
theorem ex418 (f : α → α) :
    ∀ a b, relStar (relGraph f) a b ↔ ∃ n, iter f n a = b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 419：reach (graph f) A の具体形
-- reach (graph f) A b ↔ ∃ a, A a ∧ ∃ n, iter f n a = b
--------------------------------------------------------------------------------
theorem ex419 (f : α → α) (A : Pred α) :
    ∀ b, reach (relGraph f) A b ↔ ∃ a, A a ∧ ∃ n, iter f n a = b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 420：Attention（合成＋和）への接続（multi-head の像の分解）
--------------------------------------------------------------------------------

def attnRel (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  relComp QK KV

theorem ex420 (QK1 QK2 : Rel α β) (KV : Rel β γ) (A : Pred α) :
    relImg (attnRel (relAdd QK1 QK2) KV) A
      = predAdd (relImg (attnRel QK1 KV) A) (relImg (attnRel QK2 KV) A) := by
  -- TODO
  sorry

end TL
