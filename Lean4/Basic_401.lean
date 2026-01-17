import Lean4.Basic_101
import Lean4.Basic_151
import Lean4.Basic_201
import Lean4.Basic_301
import Lean4.Basic_351

--------------------------------------------------------------------------------
-- Basic_401.lean
-- 演習問題 401〜420（実践寄せ：残余のカリー化 / ∀逆像の計算則 / reach・must）
-- ※ import Mathlib なし（Lean4 core のみ）
--------------------------------------------------------------------------------

namespace TL

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 5) reach / must（実務っぽく使うための道具）
--------------------------------------------------------------------------------

-- Aには指定した対象にRを何回か使ってたどり着けるものがある
def reach {α : Type} (R : Rel α α) (A : Pred α) : Pred α :=
  relImg (relStar R) A

-- BはRを「1回」使っても、たどり着いた先はBの中に留まる（1ステップで閉じている）
def Closed {α : Type} (R : Rel α α) (B : Pred α) : Prop :=
  relImg R B ⊆ₚ B

-- 指定した対象は、Rを何回か使うことでBへたどりつくことができる
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
  dsimp [Closed, reach, relImg, relStar, PredLe]
  intro a1 h1
  obtain ⟨a2, ⟨a3, h2, ⟨n1, h3⟩⟩, h4⟩ := h1
  exists a3
  constructor
  exact h2
  exists (n1 + 1)
  dsimp [relPow, relComp]
  exists a2

--------------------------------------------------------------------------------
-- 413：A が Closed なら reach R A = A
--------------------------------------------------------------------------------
theorem ex413 (R : Rel α α) (A : Pred α) :
    Closed R A → reach R A = A := by
  dsimp [reach, relImg, relStar, Closed, PredLe]
  intro h1
  funext a1
  dsimp [relImg, relStar]
  apply propext
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h2
  obtain ⟨a2, h3, ⟨n1, h4⟩⟩ := h2
  revert a1
  have h5 : ∀ a3, relPow R n1 a2 a3 → A a3 := by
    induction n1 with
    | zero =>
      intro a3
      dsimp [relPow, relId]
      intro h6
      rw [←h6]
      exact h3
    | succ n2 ih =>
      intro a3 h6
      dsimp [relPow, relComp] at h6
      obtain ⟨a4, h7, h8⟩ := h6
      apply h1
      exists a4
      constructor
      apply ih
      exact h7
      exact h8
  intro a5
  apply h5
  -- hRight
  intro h2
  exists a1
  constructor
  exact h2
  exists 0

--------------------------------------------------------------------------------
-- 414：must は B に単調
--------------------------------------------------------------------------------
theorem ex414 (R : Rel α α) (B C : Pred α) :
    (B ⊆ₚ C) → (must R B ⊆ₚ must R C) := by
  dsimp [must, relPreAll, PredLe]
  dsimp [Rel] at R
  dsimp [Pred] at B C
  intro h1 a1 h2 b1 h3
  apply h1
  apply h2
  exact h3

--------------------------------------------------------------------------------
-- 415：must は 1ステップ後でも保たれる（安全性の伝播）
-- must R B ⊆ preAll R (must R B)
--------------------------------------------------------------------------------

theorem ex415_pre (R : Rel α α) :
  ∀ m, RelLe (relComp R (relPow R m)) (relPow R (m + 1)) := by

  intro n1 a1
  induction n1 with
  | zero =>
    intro a3 h1
    dsimp [relPow, relComp, relId] at *
    obtain ⟨c, h2, h3⟩ := h1
    exists a1
    constructor
    rfl
    rw [←h3]
    exact h2
  | succ n ih =>
    intro a4 h4
    dsimp [relPow, relComp] at h4 ⊢
    obtain ⟨a5, h5, ⟨a6, h6, h7⟩⟩ := h4

    have h5 : relComp R (relPow R n) a1 a6 := by
      exists a5

    have h_comm : relPow R (n + 1) a1 a6 := by
      apply ih
      exact h5

    exists a6

theorem ex415 (R : Rel α α) (B : Pred α) :
    (must R B ⊆ₚ relPreAll R (must R B)) := by
  dsimp [must, relPreAll, PredLe, relStar]
  intro a1 h1 a2 h2 a3 h3
  obtain ⟨n1, h4⟩ := h3
  apply h1
  exists (n1 + 1)
  apply ex415_pre
  dsimp [relComp]
  exists a2

--------------------------------------------------------------------------------
-- 416：reach と must のガロア対応（star 版）
-- reach R A ⊆ B  ↔  A ⊆ must R B
--------------------------------------------------------------------------------
theorem ex416 (R : Rel α α) (A B : Pred α) :
    (reach R A ⊆ₚ B) ↔ (A ⊆ₚ must R B) := by
  dsimp [reach, must, relImg, relPreAll, relStar, PredLe]
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h1 a1 h2 b1 h3
  obtain ⟨n1, h4⟩ := h3
  apply h1
  exists a1
  constructor
  exact h2
  exists n1
  -- hRight
  intro h1 a1 h2
  obtain ⟨a2, h3, ⟨n1, h4⟩⟩ := h2
  have h5 : A a2 → (∃ n, relPow R n a2 a1) → B a1 := by
    intro h6 h7
    obtain ⟨n2, h8⟩ := h7
    apply h1 a2
    exact h3
    exists n2
  apply h5
  exact h3
  exists n1

--------------------------------------------------------------------------------
-- Nat / iterate（関数反復）
--------------------------------------------------------------------------------

-- 指定された回数 f を反復適用する
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0          => fun x => x
  | Nat.succ n => fun x => f (iter f n x)

--------------------------------------------------------------------------------
-- 417：graph f の pow は iterate に一致
-- relPow (graph f) n a b ↔ iter f n a = b
--------------------------------------------------------------------------------
theorem ex417 (f : α → α) :
    ∀ n a b, relPow (relGraph f) n a b ↔ iter f n a = b := by
  intro n1
  induction n1 with
  | zero =>
    intro a1 a2
    dsimp [relPow, relId, iter]
    refine ⟨?hLeft, ?hRight⟩
    -- hLeft
    intro h1
    exact h1
    -- hRight
    intro h1
    exact h1
  | succ n ih =>
    intro a1 a2
    -- dsimp で定義を展開
    dsimp [relPow, relComp, iter, relGraph]

    -- ゴールを左右に分割
    refine ⟨?hLeft2, ?hRight2⟩

    -- 【1つ目：左側の証明】 (relPow ... → iter ... = a2)
    case hLeft2 =>
      intro h3
      rcases h3 with ⟨a3, h4, h5⟩
      rw [ih] at h4
      rw [h4]
      rw [h5]

    -- 【2つ目：右側の証明】 (iter ... = a2 → relPow ...)
    case hRight2 =>
      intro h3
      let b := iter f n a1

      -- ゴールの形を ∃ に固定
      show ∃ b, relPow (relGraph f) n a1 b ∧ f b = a2

      -- 値 b と 右側の証拠 h3 を埋め込み、左側の証拠 ?_ だけを残す
      refine ⟨b, ⟨?_, h3⟩⟩

      -- 左側の証明：定義通りなので IH で完了
      rw [ih]

--------------------------------------------------------------------------------
-- 418：graph f の star は「ある回数だけ iterate して到達」
--------------------------------------------------------------------------------
theorem ex418 (f : α → α) :
    ∀ a b, relStar (relGraph f) a b ↔ ∃ n, iter f n a = b := by

  intro a1 a2
  have h1 : ∀ n, relPow (relGraph f) n a1 a2 ↔ iter f n a1 = a2 := by
    intro n1
    apply ex417 f

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h2
  obtain ⟨n1, h3⟩ := h2
  exists n1
  have h2 : relPow (relGraph f) n1 a1 a2 ↔ iter f n1 a1 = a2 := by
    apply h1 n1
  rw [h2] at h3
  exact h3

  -- hRight
  intro h2
  obtain ⟨n1, h3⟩ := h2
  exists n1
  have h2 : relPow (relGraph f) n1 a1 a2 ↔ iter f n1 a1 = a2 := by
    apply h1 n1
  rw [h2]
  exact h3

--------------------------------------------------------------------------------
-- 419：reach (graph f) A の具体形
-- reach (graph f) A b ↔ ∃ a, A a ∧ ∃ n, iter f n a = b
--------------------------------------------------------------------------------
theorem ex419 (f : α → α) (A : Pred α) :
    ∀ b, reach (relGraph f) A b ↔ ∃ a, A a ∧ ∃ n, iter f n a = b := by

  intro a1
  dsimp [reach, relImg, relStar]

  -- theorem ex417 (f : α → α) :
  --     ∀ n a b, relPow (relGraph f) n a b ↔ iter f n a = b := by

  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h1
  obtain ⟨a2, h2, ⟨n1, h3⟩⟩ := h1
  exists a2
  constructor

  -- hLeft.left
  exact h2

  -- hLeft.right
  exists n1
  have h4 : relPow (relGraph f) n1 a2 a1 ↔ iter f n1 a2 = a1 := by
    apply ex417 f
  rw [←h4]
  exact h3

  -- hRight
  intro h1
  obtain ⟨a2, h2, ⟨n1, h3⟩⟩ := h1
  exists a2
  constructor
  -- hRight.left
  exact h2
  -- hRight.right
  exists n1
  have h4 : relPow (relGraph f) n1 a2 a1 ↔ iter f n1 a2 = a1 := by
    apply ex417 f
  rw [h4]
  exact h3

--------------------------------------------------------------------------------
-- 420：Attention（合成＋和）への接続（multi-head の像の分解）
--------------------------------------------------------------------------------

def attnRel (QK : Rel α β) (KV : Rel β γ) : Rel α γ :=
  relComp QK KV

theorem ex420 (QK1 QK2 : Rel α β) (KV : Rel β γ) (A : Pred α) :
    relImg (attnRel (relAdd QK1 QK2) KV) A
      = predAdd (relImg (attnRel QK1 KV) A) (relImg (attnRel QK2 KV) A) := by
  dsimp [attnRel]

  have h1 : relImg (relAdd (relComp QK1 KV) (relComp QK2 KV)) A = predAdd (relImg (relComp QK1 KV) A) (relImg (relComp QK2 KV) A) := by
    apply ex405 (relComp QK1 KV) (relComp QK2 KV) A

  rw [←h1]

  funext g1
  dsimp [relImg]
  dsimp [relAdd]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h2
  obtain ⟨a1, h3, h4⟩ := h2
  dsimp [relComp] at h4
  dsimp [relComp]
  exists a1
  constructor

  -- hLeft.left
  exact h3

  -- hLeft.right
  obtain ⟨b1, h5 | h6, h7⟩ := h4

  -- hLeft.right.inl
  left
  exists b1

  -- hLeft.right.inr
  right
  exists b1

  -- hRight
  intro h2
  dsimp [relComp, relAdd]
  obtain ⟨a1, h3, h4⟩ := h2
  -- hRight
  exists a1
  obtain ⟨b1, ⟨h5, h6⟩⟩ | h7 := h4

  -- hRight.inl
  constructor

  -- hRight.inl.left
  exact h3

  -- hRight.inl.right
  exists b1

  constructor

  -- hRight.inl.right.left
  left
  exact h5

  -- hRight.inl.right.right
  exact h6

  -- hRight.inr
  dsimp [relComp] at h7
  obtain ⟨b1, h8, h9⟩ := h7
  constructor

  -- hRight.inr.left
  exact h3

  -- hRight.inr.right
  exists b1
  constructor

  -- hRight.inr.right.left
  right
  exact h8

  -- hRight.inr.right.right
  exact h9

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆

--------------------------------------------------------------------------------
-- 421〜440：演習（残余/Pred/閉包/不動点/graph/Attention：実践寄せ）
-- ※ Basic_401.lean の末尾に追記でOK
-- ※ 401〜420 の定義がある前提：
--   Rel, relComp, relAdd, relMul, relTrans, relId, RelLe (⊆),
--   rRes, lRes,
--   Pred, PredLe (⊆ₚ), predAdd, predMul,
--   relImg, relPre, relPreAll,
--   relGraph, relPow, relStar,
--   reach, Closed, must, iter, attnRel
--------------------------------------------------------------------------------

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 421：residuation（右残余のガロア対応：超重要）
-- (R;S) ⊆ T  ↔  R ⊆ (S ▷ T)
--
-- ヒント：
--   dsimp [RelLe, relComp, rRes]
--   (→) は「R a b と S b c から T a c」を作る形
--   (←) は obtain ⟨b, hR, hS⟩ := ... して、hRS a b hR c hS
--------------------------------------------------------------------------------
theorem ex421 (R : Rel β α) (S : Rel α γ) (T : Rel β γ) :
    (relComp R S ⊆ T) ↔ (R ⊆ rRes S T) := by

  dsimp [RelLe]
  dsimp [rRes]
  dsimp [relComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 b1 a1 h2 c1 h3
  apply h1
  exists a1

  -- hRight
  intro h1 b1 a1 h2
  obtain ⟨a2, h4, h5⟩ := h2
  apply h1 b1 a2
  exact h4
  exact h5

--------------------------------------------------------------------------------
-- 422：residuation（左残余のガロア対応）
-- (R;S) ⊆ T  ↔  S ⊆ (R ⊲ T)
--
-- ヒント：
--   dsimp [RelLe, relComp, lRes]
--------------------------------------------------------------------------------
theorem ex422 (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relComp R S ⊆ T) ↔ (S ⊆ lRes R T) := by

  dsimp [RelLe]
  dsimp [lRes]
  dsimp [relComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 b1 g1 h2 a1 h3
  apply h1
  exists b1

  -- hRight
  intro h1 b1 g1 h2
  obtain ⟨b2, h4, h5⟩ := h2
  apply h1 b2 g1
  exact h5
  exact h4

--------------------------------------------------------------------------------
-- 423：∀逆像（preAll）は rRes の特殊例（Unit 埋め込み）
--
-- predAsRel B : Rel Unit β := fun _ b => B b
-- relToPred Q : Pred α := fun a => Q () a
--
-- 目標：
--   relPreAll R B = relToPred (rRes R (predAsRel B))
--------------------------------------------------------------------------------
def predAsRel {β : Type} (B : Pred β) : Rel Unit β := fun _ b => B b
def relToPred {α : Type} (Q : Rel Unit α) : Pred α := fun a => Q () a

theorem ex423 (R : Rel α β) (B : Pred β) :
    relPreAll R B = relToPred (rRes R (predAsRel B)) := by
  funext a1
  dsimp [relPreAll]
  dsimp [relToPred]
  dsimp [rRes]
  dsimp [predAsRel]

--------------------------------------------------------------------------------
-- 424：像 relImg も Unit を使って「合成」で書ける
-- Img R A b  ↔  ((predAsRel A) ; R) () b
--
-- ヒント：
--   funext b; apply propext; dsimp [relImg, predAsRel, relComp]
--------------------------------------------------------------------------------
theorem ex424 (R : Rel α β) (A : Pred α) :
    relImg R A = (fun b => relComp (predAsRel A) R () b) := by
  funext b1
  dsimp [relImg]
  dsimp [relComp]
  dsimp [predAsRel]

--------------------------------------------------------------------------------
-- 425：must は B を含む（0歩到達があるので）
-- must R B ⊆ₚ B
--
-- ヒント：
--   dsimp [must, relPreAll, relStar, PredLe]
--   b := a, n := 0 を入れる
--------------------------------------------------------------------------------
theorem ex425 (R : Rel α α) (B : Pred α) :
    must R B ⊆ₚ B := by
  dsimp [Rel] at R
  dsimp [Pred] at B
  dsimp [must]
  dsimp [PredLe]
  dsimp [relPreAll]
  intro a1 h1
  apply h1
  dsimp [relStar]
  exists 0

--------------------------------------------------------------------------------
-- 426：must は Closed（安全集合は1歩で外へ出ない）
-- Closed R (must R B)
--
-- ヒント：
--   Closed は Img R X ⊆ₚ X
--   Img R (must R B) から witness を取り、
--   must の定義へ (n:=1) を押し込む
--------------------------------------------------------------------------------
theorem ex426 (R : Rel α α) (B : Pred α) :
    Closed R (must R B) := by

  intro a1 h1 a2 h2
  obtain ⟨a3, h3, h4⟩ := h1
  obtain ⟨n1, h5⟩ := h2
  apply h3
  exists (n1 + 1)
  apply ex415_pre R n1
  exists a1

--------------------------------------------------------------------------------
-- 427：must は「B の中で最大の Closed 集合」
-- X ⊆ₚ B かつ Closed R X なら X ⊆ₚ must R B
--
-- ヒント：
--   dsimp [must, relPreAll, relStar, PredLe]
--   star の証拠 ⟨n, hn⟩ に対して n で帰納法
--   0 は X⊆B で、succ は Closed を使って1歩ずつ進める
--------------------------------------------------------------------------------
theorem ex427_pre (R : Rel α α) (X : Pred α) :
  (∀ b, (∃ a, X a ∧ R a b) → X b) ↔
  (∀ a b, (X a ∧ R a b) → X b) := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 a1 a2 h2
  obtain ⟨h3, h4⟩ := h2
  apply h1 a2
  exists a1

  -- hRight
  intro h1 a1 h2
  obtain ⟨a2, h3, h4⟩ := h2
  apply h1 a2 a1
  constructor
  exact h3
  exact h4

theorem ex427 (R : Rel α α) (B X : Pred α) :
    (X ⊆ₚ B) → Closed R X → (X ⊆ₚ must R B) := by

  -- XはBの部分集合
  -- Closed R X : XについてRを適用してもその値域はXに含まれる
  -- X内はすべてBへたどり着ける

  -- 当たり前のことをいっている。
  -- Rを適用してもXに留まるなら、 何回Rを適用してもXに留まる。
  -- XはBの部分集合なのだから、Rを何回適用してもB内に留まる

  intro h1 h2 a1 h3 a2 h4
  dsimp [PredLe] at h1
  dsimp [Closed] at h2
  dsimp [PredLe] at h2
  dsimp [relImg] at h2
  rw [relStar] at h4
  obtain ⟨n1, h6⟩ := h4
  apply h1
  revert a2
  induction n1 with
  | zero =>
    intro a3 h6
    dsimp [relPow, relId] at h6
    rw [←h6]
    exact h3
  | succ n ih =>
    intro a3 h6
    dsimp [relPow, relComp] at h6
    obtain ⟨a4, h7, h8⟩ := h6
    apply h2
    exists a4
    constructor
    apply ih
    exact h7
    exact h8

--------------------------------------------------------------------------------
-- 428：star の展開（片方向）
-- star R ⊆ id + (R;star R)
--
-- ヒント：
--   dsimp [RelLe, relStar, relAdd, relId, relComp]
--   obtain ⟨n, hn⟩ := hstar
--   cases n with
--   | zero => left; ...（hn は id なので a=b）
--   | succ n => right; witness を作る（最初の1歩を切り出す）
--------------------------------------------------------------------------------

theorem ex428_pre (R : Rel α α) : relComp R (relStar R) ⊆ relStar R := by
  intro a1 b1 h1
  obtain ⟨a2, h2, ⟨n1, h3⟩⟩ := h1
  exists (n1 + 1)
  apply ex415_pre
  exists a2

theorem ex428 (R : Rel α α) :
    relStar R ⊆ relAdd (relId α) (relComp R (relStar R)) := by

  intro a1 a2 h1
  obtain ⟨n1, h2⟩ := h1
  revert a2
  induction n1 with
  | zero =>
    intro a3 h3
    left
    dsimp [relId]
    rw [←h3]
  | succ n2 ih =>
    intro a3 h3
    right
    obtain ⟨a4, h4, h5⟩ := h3
    have h6 : relPow R n2 a1 a4 → a1 = a4 ∨ ∃ b, R a1 b ∧ relStar R b a4 := by
      intro h6_1
      apply ih
      exact h6_1
    have h7 : a1 = a4 ∨ ∃ b, R a1 b ∧ relStar R b a4 := by
      apply h6
      exact h4
    obtain h8 | ⟨a5, h9, h10⟩ := h7
    rw [←h8] at h5
    exists a3
    constructor
    exact h5
    exists 0
    exists a5
    constructor
    exact h9
    obtain ⟨n3, h11⟩ := h10
    exists (n3 + 1)
    exists a4

--------------------------------------------------------------------------------
-- 429：star の展開（逆方向）
-- id + (R;star R) ⊆ star R
--
-- ヒント：
--   left: n := 0
--   right: witness (n+1)
--------------------------------------------------------------------------------
theorem ex429 (R : Rel α α) :
    relAdd (relId α) (relComp R (relStar R)) ⊆ relStar R := by

  intro s e h1
  obtain h2 | ⟨a1, h3, h4⟩ := h1

  -- inl
  exists 0

  -- inr
  obtain ⟨n1, h5⟩ := h4
  exists (n1 + 1)
  apply ex415_pre
  exists a1

--------------------------------------------------------------------------------
-- 430：star の展開を等式でまとめる
-- star R = id + (R;star R)
--
-- ヒント：
--   428/429 を両方向に使う
--------------------------------------------------------------------------------
theorem ex430 (R : Rel α α) :
    relStar R = relAdd (relId α) (relComp R (relStar R)) := by

  funext s e
  apply propext
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  apply ex428 R
  -- hRight
  apply ex429 R

--------------------------------------------------------------------------------
-- 431：must の安全性方程式（不動点/Bellman 形）
-- must R B = B ∩ preAll R (must R B)
--
-- ヒント：
--   funext a; apply propext
--   (→) は 425 + 「R a b なら star a b（n:=1）」で流す
--   (←) は 430 で star を (id) or (R;star) に分解すると楽
--------------------------------------------------------------------------------
theorem ex431 (R : Rel α α) (B : Pred α) :
    must R B = predMul B (relPreAll R (must R B)) := by
  funext a
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  constructor

  -- hLeft.left
  apply ex425 R B
  exact h1

  -- hLeft.right
  intro a1 h2 a2 h3
  obtain ⟨n1, h4⟩ := h3
  apply h1
  exists (n1 + 1)
  apply ex415_pre
  exists a1

  -- hRight
  intro h1 a3 h5
  rw [ex430 R] at h5
  obtain ⟨h6, h7⟩ := h1
  obtain h8 | ⟨a4, h9, ⟨n2, h10⟩⟩ := h5

  -- hRight.inl
  rw [←h8]
  exact h6

  -- hRight.inr
  apply h7 a4
  exact h9
  exists n2

--------------------------------------------------------------------------------
-- 432：must (graph f) の具体形（反復で常に B）
-- must (graph f) B a ↔ ∀ n, B (iter f n a)
--
-- ヒント：
--   「star(graph f) a b ↔ ∃ n, iter f n a = b」（あなたの ex418）を使うと一直線
--------------------------------------------------------------------------------
theorem ex432 (f : α → α) (B : Pred α) :
    ∀ a, must (relGraph f) B a ↔ ∀ n, B (iter f n a) := by
  -- 指定されたfを使ってBにたどり着けるたものの集合は、
  -- fを何回反復適用してもBに留まるものの集合に等しい

  -- theorem ex418 (f : α → α) :
  --     ∀ a b, relStar (relGraph f) a b ↔ ∃ n, iter f n a = b := by

  intro a
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h1
  dsimp [must] at h1
  dsimp [relPreAll] at h1
  intro n1
  apply h1
  rw [ex418 f a (iter f n1 a)]
  exists n1
  -- hRight
  intro h2
  dsimp [must]
  dsimp [relPreAll]
  intro a1
  intro h4
  rw [ex418 f a a1] at h4
  obtain ⟨n1, h5⟩ := h4
  have h6 : B (iter f n1 a) := by
    apply h2
  rw [←h5]
  exact h6

--------------------------------------------------------------------------------
-- 433：Attention の右 residuation（設計に直結）
-- (attnRel QK KV) ⊆ T  ↔  QK ⊆ (KV ▷ T)
--
-- ヒント：ex421 を attnRel の定義に当てるだけ
--------------------------------------------------------------------------------
theorem ex433 (QK : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    (attnRel QK KV ⊆ T) ↔ (QK ⊆ rRes KV T) := by
  -- 「QK→KV の2段到達が常に T に含まれる」ことは、
  -- 「QK が成り立つ各ペア (a,b) について、
  -- b から KV で到達できる先はすべて a から T でも到達できる」ことと同値。

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  intro a1
  intro b1
  intro h2
  intro g1
  intro h3
  apply h1
  exists b1

  -- hRight
  intro h1
  intro a1
  intro g1
  intro h2
  obtain ⟨b1, h3, h4⟩ := h2
  apply h1 a1 b1
  exact h3
  exact h4

--------------------------------------------------------------------------------
-- 434：Attention の左 residuation（もう片側）
-- (attnRel QK KV) ⊆ T  ↔  KV ⊆ (QK ⊲ T)
--------------------------------------------------------------------------------
theorem ex434 (QK : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    (attnRel QK KV ⊆ T) ↔ (KV ⊆ lRes QK T) := by
  -- 「QK→KV の2段到達が常に T に含まれる」ことは、
  -- 「KV が成り立つ各ペア (b,c) について、
  -- a から QK で b に到達できる任意の a に対して、a から T で c に到達できる」ことと同値。
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  intro b1
  intro g1
  intro h2
  intro a1
  intro h3
  apply h1
  exists b1

  -- hRight
  intro h1
  intro b1
  intro g1
  intro h2
  obtain ⟨a1, h3, h4⟩ := h2
  apply h1 a1 g1
  exact h4
  exact h3

--------------------------------------------------------------------------------
-- 435：multi-head（KV 側の加法）で Img が分解する
-- Img(attn QK (KV1+KV2)) A = Img(attn QK KV1) A ∪ Img(attn QK KV2) A
--
-- ヒント：
--   まず relComp QK (KV1+KV2) = (QK;KV1) + (QK;KV2) を点ごとに示してから
--   ex405（像の分配）へ
--------------------------------------------------------------------------------
theorem ex435 (QK : Rel α β) (KV1 KV2 : Rel β γ) (A : Pred α) :
    relImg (attnRel QK (relAdd KV1 KV2)) A
      = predAdd (relImg (attnRel QK KV1) A) (relImg (attnRel QK KV2) A) := by
  -- KV の条件を「KV1 または KV2（OR）」にすると、
  -- A から到達できる出力集合は
  -- 「KV1 を使って到達できる集合」∪「KV2 を使って到達できる集合」
  -- という和（predAdd）になる。
  funext g1
  dsimp [relImg]
  dsimp [attnRel]
  dsimp [relComp]
  dsimp [relAdd]
  dsimp [predAdd]
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  dsimp [relImg]
  dsimp [relComp]
  obtain ⟨a1, h2, ⟨b1, h3, h4|h5⟩⟩ := h1

  -- hLeft.inl
  left
  exists a1
  constructor

  -- hLeft.inl.left
  exact h2

  -- hLeft.inl.right
  exists b1

  -- hLeft.inr
  right
  exists a1
  constructor

  -- hLeft.inr.left
  exact h2

  -- hLeft.inr.right
  exists b1

  -- hRight
  dsimp [relImg]
  dsimp [relComp]
  intro h1
  obtain ⟨a1, h2, ⟨b1, h3, h4⟩⟩ | ⟨a2, h5, ⟨b2, h6, h7⟩⟩ := h1

  -- hRight.inl
  exists a1
  constructor

  -- hRight.inl.left
  exact h2

  -- hRight.inl.right
  exists b1
  constructor

  -- hRight.inl.right.left
  exact h3

  -- hRight.inl.right.right
  left
  exact h4

  -- hRight.inr
  exists a2
  constructor

  -- hRight.inr.left
  exact h5

  -- hRight.inr.right
  exists b2
  constructor

  -- hRight.inr.right.left
  exact h6

  -- hRight.inr.right.right
  right
  exact h7

--------------------------------------------------------------------------------
-- 436：Attention の単調性（両側）
-- QK ⊆ QK' かつ KV ⊆ KV' なら attnRel QK KV ⊆ attnRel QK' KV'
--
-- ヒント：
--   dsimp [RelLe, attnRel, relComp]
--   obtain ⟨b, hQK, hKV⟩ := h
--------------------------------------------------------------------------------
theorem ex436 (QK QK' : Rel α β) (KV KV' : Rel β γ) :
    (QK ⊆ QK') → (KV ⊆ KV') → (attnRel QK KV ⊆ attnRel QK' KV') := by
  -- QK を「より許す関係」（QK ⊆ QK'）に広げ、KV も「より許す関係」（KV ⊆ KV'）に広げると、
  -- 2段合成（attention の到達）でたどれるペアも広がる。
  -- つまり、部品を強化（候補を増やす）すると、合成した結果も単調に大きくなる（包含が保たれる）。
  intro h1 h2
  intro s e
  intro h3
  obtain ⟨b1, h4, h5⟩ := h3
  exists b1
  constructor
  -- left
  apply h1
  exact h4
  -- right
  apply h2
  exact h5

--------------------------------------------------------------------------------
-- 437：mask が “より強い条件” のとき吸収できる
-- M ⊆ QK なら (QK ∧ M) = M
--
-- ヒント：
--   funext a b; apply propext; constructor
--   (→) ⟨hQK, hM⟩ から hM
--   (←) hM から ⟨hMQK _ _ hM, hM⟩
--------------------------------------------------------------------------------
theorem ex437 (QK M : Rel α β) :
    (M ⊆ QK) → relMul QK M = M := by
  -- M ⊆ QK（M は QK の部分関係）なら、
  -- 「QK かつ M」（relMul = ∧）は結局 M と同じになる。
  -- 直感：M が成り立つときは自動的に QK も成り立つので、余計な条件（QK）は効かない。

  intro h1
  funext a b
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h3
  obtain ⟨h4, h5⟩ := h3
  exact h5

  -- hRight
  intro h3
  constructor

  -- hRight.left
  apply h1
  exact h3

  -- hRight.right
  exact h3

--------------------------------------------------------------------------------
-- 438：mask を入れた attention は “mask だけ” で同じになる（437 応用）
-- M ⊆ QK なら attnRel (QK ∧ M) KV = attnRel M KV
--------------------------------------------------------------------------------
theorem ex438 (QK M : Rel α β) (KV : Rel β γ) :
    (M ⊆ QK) → attnRel (relMul QK M) KV = attnRel M KV := by
  -- M ⊆ QK なら、QK と M の積（∧）は結局 M と同じ（ex437 と同じ発想）。
  -- したがって QK による「追加条件」を付けたまま attention 合成しても結果は変わらない。
  -- 直感：もともと M で許される遷移は全部 QK でも許されているので、フィルタが効かない。
  intro h1
  rw [ex437 QK M h1]

--------------------------------------------------------------------------------
-- 439：must は関係に反単調（遷移が増えるほど must は厳しくなる）
-- R ⊆ S なら must S B ⊆ₚ must R B
--
-- ヒント：
--   must = preAll (star ...) B
--   1) R ⊆ S なら star R ⊆ star S（pow の単調性を n で帰納）
--   2) preAll は関係に反単調（あなたの ex395_a の関係版）
--------------------------------------------------------------------------------
theorem ex439 (R S : Rel α α) (B : Pred α) :
    (R ⊆ S) → (must S B ⊆ₚ must R B) := by
  -- R ⊆ S（S のほうが遷移が多い）なら、star S の到達先の集合は star R より大きい。
  -- must は「到達しうる先が全部 B の中」という安全条件なので、
  -- 遷移が増えるほどチェック対象が増えて条件は厳しくなる。
  -- だから must S B ⊆ must R B（S で安全なら、より弱い R でも安全）。

  intro h1
  intro a1
  intro h2
  intro b1
  have h3 : relStar S a1 b1 → B b1 := by
    apply h2
  intro h4
  apply h3
  obtain ⟨n1, h5⟩ := h4
  exists n1
  revert a1 b1
  induction n1 with
  | zero =>
    intro a2 h5 h6 h7 h8
    rw [h8]
    dsimp [relPow, relId]
  | succ n2 ih =>
    intro a2 h5 h6 h7 h8
    obtain ⟨a3, h9, h10⟩ := h8
    exists a3
    constructor
    apply ih
    exact h5
    intro h12
    apply h5
    exact h12
    exact h9
    apply h1
    exact h10

--------------------------------------------------------------------------------
-- 440：reach は関係に単調（遷移が増えるほど到達集合は増える）
-- R ⊆ S なら reach R A ⊆ₚ reach S A
--
-- ヒント：
--   reach = Img (star ...) A
--   star の単調性（439 の途中で作る補題）を Img に流す
--------------------------------------------------------------------------------
theorem ex440 (R S : Rel α α) (A : Pred α) :
    (R ⊆ S) → (reach R A ⊆ₚ reach S A) := by
  -- R ⊆ S（S のほうが遷移が多い）なら、star S は star R より多く到達できる。
  -- reach は「A から到達できる点（∃で像を取る）」なので、遷移が増えるほど到達集合は広がる。
  -- したがって reach R A ⊆ reach S A（R で到達できるなら、S でも到達できる）。

  intro h1
  intro a1
  intro h2
  obtain ⟨a2, h3, ⟨n1, h4⟩⟩ := h2
  exists a2
  constructor

  -- left
  exact h3

  --right
  exists n1
  revert a1 a2
  induction n1 with
  | zero =>
    intro a3 h4 h5 h6
    exact h6
  | succ n2 ih =>
    intro a3 a4 h5 h6
    obtain ⟨a5, h7, h8⟩ := h6
    exists a5
    constructor
    apply ih
    exact h5
    exact h7
    apply h1
    exact h8

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆

--------------------------------------------------------------------------------
-- 441〜450：演習（Closed の意味の整理 / reach・must の不動点 / attention 実践）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 441：Closed の「点ごとの形」（あなたが議論していた同値の決定版）
-- Closed R X  ↔  ∀ a b, X a → R a b → X b
--
-- ヒント：
--   dsimp [Closed, relImg, PredLe]
--   「∃ a, X a ∧ R a b → X b」を a,b の形に直すだけ
--------------------------------------------------------------------------------
theorem ex441 (R : Rel α α) (X : Pred α) :
    Closed R X ↔ (∀ a b, X a → R a b → X b) := by
  -- Closed R X は「X から R で 1 歩進んでも、必ず X の中に留まる」という条件。
  -- 左辺の定義（Img R X ⊆ₚ X）を展開すると、「X a かつ R a b なら X b」に一致する。
  -- つまり “1ステップ遷移での不変性” の言い換え。
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  intro a1
  intro a2
  intro h2
  intro h3
  apply h1 a2
  exists a1

  -- hRight
  intro h1
  intro a1
  intro h2
  obtain ⟨a2, h3, h4⟩ := h2
  apply h1 a2 a1
  exact h3
  exact h4

--------------------------------------------------------------------------------
-- 442：reach は “拡大” (extensive) ：A ⊆ₚ reach R A
--
-- ヒント：
--   dsimp [PredLe, reach, relImg, relStar]
--   witness は a 自身、n:=0（relPow 0 = relId）で到達
--------------------------------------------------------------------------------
theorem ex442 (R : Rel α α) (A : Pred α) :
    A ⊆ₚ reach R A := by
  -- reach R A は「A から star R（0回以上の反復）で到達できる点」の集合。
  -- 0回到達（n = 0）では必ず自分自身に留まれるので、A の各要素は reach R A に含まれる。
  -- つまり A ⊆ₚ reach R A（到達閉包は元の集合を含む）。
  intro a1 h1
  exists a1
  constructor

  -- left
  exact h1

  -- right
  exists 0

--------------------------------------------------------------------------------
-- 443：像は合成に関して結合（到達集合の実用形）
-- Img (R;S) A = Img S (Img R A)
--
-- ヒント：
--   funext c; apply propext; constructor <;> intro h
--   h から witness を取り直すだけ
--------------------------------------------------------------------------------
theorem ex443 (R : Rel α β) (S : Rel β γ) (A : Pred α) :
    relImg (relComp R S) A = relImg S (relImg R A) := by
  -- A から (R;S) で到達するとは、「ある中間 b を経由して R で b に行き、S で目的地に行く」こと。
  -- これはまず R で到達できる集合 relImg R A を作り、そこから S で到達するのと同じ。
  -- つまり「像は合成に対して結合的」：Img(R;S) = Img S ∘ Img R。
  funext g1
  apply propext
  dsimp [relImg, relComp]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  obtain ⟨a1, h2, ⟨b1, h3, h4⟩⟩ := h1
  exists b1
  constructor

  -- hLeft.left
  exists a1
  exact h4

  -- hRight
  intro h1
  obtain ⟨b1, ⟨a1, h2, h3⟩, h4⟩ := h1
  exists a1
  constructor

  -- hRight.left
  exact h2

  -- hRight.right
  exists b1

--------------------------------------------------------------------------------
-- 444：reach の “Bellman 形” 不動点方程式
-- reach R A = A ∪ Img R (reach R A)
--
-- ヒント：
--   reach = Img (star R) A
--   ex430 : star R = id + (R;star R) を使って
--   Img の分配（ex405）と Img 合成（ex443）で整理
--------------------------------------------------------------------------------
theorem ex444 (R : Rel α α) (A : Pred α) :
    reach R A = predAdd A (relImg R (reach R A)) := by
  -- reach R A は「A から star R（0回以上）で到達できる点」。
  -- star の展開（0回の id か、1歩 R のあとにさらに star）に対応して、
  -- 到達集合は「元の A」または「reach から 1歩 R 進んだ先」の和に分解できる。

  funext a1
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a2
  obtain ⟨a3, h2, ⟨n1, h3⟩⟩ := a2
  revert a3
  induction n1 with
  | zero =>
    intro a4 h3 h4
    left
    rw [←h4]
    exact h3
  | succ n2 ih =>
    intro a4 h3 h4
    obtain ⟨a5, h5, h6⟩ := h4
    right
    exists a5
    constructor
    exists a4
    constructor
    exact h3
    exists n2
    exact h6

  -- hRight
  intro a2
  obtain h3 | ⟨a3, ⟨a4, h4, ⟨n1, h5⟩⟩, h6⟩ := a2
  exists a1
  constructor
  exact h3
  exists 0
  exists a4
  constructor
  exact h4
  exists (n1 + 1)
  exists a3

--------------------------------------------------------------------------------
-- 445：star の推移性（関係として）
-- star;star ⊆ star
--
-- ヒント：
--   dsimp [RelLe, relComp, relStar]
--   obtain ⟨m, hm⟩ と obtain ⟨n, hn⟩ を取り
--   witness を (m+n) にして ex367 を使う
--------------------------------------------------------------------------------
theorem ex445 (R : Rel α α) :
    relComp (relStar R) (relStar R) ⊆ relStar R := by
  -- star R は「R を0回以上たどって到達できる」関係。
  -- 0回以上たどった後に、さらに0回以上たどるのは、結局「0回以上たどる」のまま。
  -- つまり star は合成に対して閉じており、(star R);(star R) ⊆ star R。
  intro a1 a2 h1
  obtain ⟨a3, ⟨m1, h2⟩, ⟨n1, h3⟩⟩ := h1
  exists (m1 + n1)
  apply ex367
  exists a3

--------------------------------------------------------------------------------
-- 446：must の冪等性（interior operator っぽさ）
-- must R (must R B) = must R B
--
-- ヒント：
--   funext a; apply propext; constructor
--   (→) は b:=到達先, さらに 0歩到達（n:=0）で B を出す
--   (←) は ex445（star の推移性）で “到達の合成” を潰す
--------------------------------------------------------------------------------
theorem ex446 (R : Rel α α) (B : Pred α) :
    must R (must R B) = must R B := by
  -- must R B は「R を何回たどっても到達先が常に B に入る」という安全集合。
  -- いったん安全集合 must R B の中に入れてしまえば、そこからさらに must を掛けても条件は増えない。
  -- つまり must は冪等：must R (must R B) = must R B。

  funext a1
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1 a2 h2
  obtain ⟨n1, h3⟩ := h2
  apply h1
  exists 0
  exists n1

  -- hRight
  intro h1 a2 h2 a3 h3
  obtain ⟨n1, h4⟩ := h2
  obtain ⟨n2, h5⟩ := h3
  apply h1
  exists (n1 + n2)
  apply ex367
  exists a2

--------------------------------------------------------------------------------
-- 447：reach の “最小性”（A を含み 1-step で閉じる集合は reach を含む）
-- (A ∪ Img R X) ⊆ₚ X なら reach R A ⊆ₚ X
--
-- ヒント：
--   h : predAdd A (relImg R X) ⊆ₚ X から
--     (1) A ⊆ₚ X と (2) Closed R X を作って
--   ex411（不変集合から出ない）に流す
--------------------------------------------------------------------------------
theorem ex447 (R : Rel α α) (A X : Pred α) :
    (predAdd A (relImg R X) ⊆ₚ X) → (reach R A ⊆ₚ X) := by

  -- 仮定は「A ⊆ X かつ、X から R で 1歩進んでも X に入る（relImg R X ⊆ X）」をまとめたもの。
  -- つまり X は A を含み、R に対して 1ステップ閉じている不変集合。
  -- そのため A から star R で到達できる点（reach R A）はすべて X の中に収まる。

  -- -- AあるいはBで成り立つか確認
  -- def predAdd {X : Type} (A B : Pred X) : Pred X := fun x => A x ∨ B x

  -- -- ∃-像（到達）
  -- -- AにはRを一回使ってbにたどり着けるものがある
  -- def relImg {α β : Type} (R : Rel α β) (A : Pred α) : Pred β :=
  --   fun b => ∃ a, A a ∧ R a b

  -- -- Aで成り立つならBで成り立つ
  -- -- AはBの部分集合
  -- def PredLe {X : Type} (A B : Pred X) : Prop :=
  --   ∀ x, A x → B x

  -- infix:50 " ⊆ₚ " => PredLe

  -- -- Aには指定した対象にRを何回か使ってたどり着けるものがある
  -- def reach {α : Type} (R : Rel α α) (A : Pred α) : Pred α :=
  --   relImg (relStar R) A

  -- relImg R X
  -- Xを始点にRを使ってたどり着けるものの集合

  -- predAdd A (relImg R X)
  -- Xを始点にRを一回使ってたどり着けるか、あるいはAに含まれるものの集合

  -- predAdd A (relImg R X) ⊆ₚ X
  -- Xを始点にRを一回使ってたどり着けるか、あるいはAに含まれるものの集合が
  -- Xの部分集合である

  -- (predAdd A (relImg R X) ⊆ₚ X) →
  -- Xを始点にRを一回使ってたどり着けるか、あるいはAに含まれるものの集合が
  -- Xの部分集合であるならば、

  -- reach R A
  -- Aを始点にRを何回か使ってたどり着けるものの集合

  -- reach R A ⊆ₚ X
  -- Aを始点にRを何回か使ってたどり着けるものの集合はXの部分集合である

  -- (predAdd A (relImg R X) ⊆ₚ X) → (reach R A ⊆ₚ X)
  -- Xを始点にRを一回使ってたどり着けるか、あるいはAに含まれるものの集合が
  -- Xの部分集合であるならば、
  -- それはAを始点にRを何回か使ってたどり着けるものの集合はXの部分集合である

  intro h1 a1 h2
  obtain ⟨a2, h3, ⟨n1, h4⟩⟩ := h2

  have h5 : (relImg R X) ⊆ₚ X := by
    intro h5_a1 h5_h1
    apply h1
    right
    obtain ⟨h5_a2, h5_h2, h5_h3⟩ := h5_h1
    exists h5_a2

  have h6 : A ⊆ₚ X := by
    intro h6_a1 h6_h1
    apply h1
    left
    exact h6_h1

  revert a1 a2
  induction n1 with
  | zero =>
    intro a3 a4 h8 h9
    rw [←h9]
    apply h6
    exact h8
  | succ n2 ih =>
    intro a3 a4 h8 h9
    obtain ⟨a5, h10, h11⟩ := h9
    have h12 : X a5 := by
      apply ih a5 a4
      exact h8
      exact h10
    apply h5
    exists a5

--------------------------------------------------------------------------------
-- 448：multi-head を両側で入れたときの “4分解”（実践）
-- QK が 2-head, KV が 2-head だと、到達集合は4つの和に分解できる
--
-- ヒント：
--   まず ex435 で KV 側を分解（2つ）
--   次に各枝で ex420 で QK 側を分解（2つ）
--   ※括弧の形が合うように目標をこの形にしてあります（結合律不要）
--------------------------------------------------------------------------------
theorem ex448 (QK1 QK2 : Rel α β) (KV1 KV2 : Rel β γ) (A : Pred α) :
    relImg (attnRel (relAdd QK1 QK2) (relAdd KV1 KV2)) A
      =
    predAdd
      (predAdd (relImg (attnRel QK1 KV1) A) (relImg (attnRel QK2 KV1) A))
      (predAdd (relImg (attnRel QK1 KV2) A) (relImg (attnRel QK2 KV2) A)) := by
  -- QK 側が 2-head（QK1/QK2）、KV 側も 2-head（KV1/KV2）だと、
  -- 「どの head を選ぶか」が 2×2 通りに分岐する。
  -- そのため A から到達できる出力集合は、(QK1,KV1),(QK2,KV1),(QK1,KV2),(QK2,KV2) の
  -- 4つの attention の像の和（predAdd）に分解できる。

  funext g1
  apply propext
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro h1
  obtain ⟨a1, h2, ⟨b1, h3|h4, h5|h6⟩⟩ := h1
  left
  left
  exists a1
  constructor
  exact h2
  exists b1

  right
  left
  exists a1
  constructor
  exact h2
  exists b1

  left
  right
  exists a1
  constructor
  exact h2
  exists b1

  right
  right
  exists a1
  constructor
  exact h2
  exists b1

  -- hRight
  intro h1
  obtain ⟨ ⟨a1, h2, ⟨b1, h3, h4⟩⟩ | ⟨a2,h5,b2,h6,h7⟩ ⟩ | ⟨a3,h8,b3,h9,h10⟩ | ⟨a4,h11,b4,h12,h13⟩ := h1
  exists a1
  constructor
  exact h2
  exists b1
  constructor
  left
  exact h3
  left
  exact h4
  exists a2
  constructor
  exact h5
  exists b2
  constructor
  right
  exact h6
  left
  exact h7
  exists a3
  constructor
  exact h8
  exists b3
  constructor
  left
  exact h9
  right
  exact h10
  exists a4
  constructor
  exact h11
  exists b4
  constructor
  right
  exact h12
  right
  exact h13

--------------------------------------------------------------------------------
-- 449：関数グラフの attention は “関数合成のグラフ”
-- attnRel (graph f) (graph g) = graph (g ∘ f)
--
-- ヒント：
--   funext a c; apply propext
--   (→) witness b を取り、等式で書き換える
--   (←) witness は b := f a
--------------------------------------------------------------------------------
theorem ex449 (f : α → β) (g : β → γ) :
    attnRel (relGraph f) (relGraph g) = relGraph (fun x => g (f x)) := by
  -- graph f は「a から b へ行けるのは b = f a のときだけ」という決定的な関係。
  -- それを graph g と合成すると、a から c へ行けるのは「ある b = f a を経由して c = g b」のとき。
  -- つまり c = g (f a) に一致し、合成は関数合成 (g ∘ f) の graph そのものになる。
  funext a1 g1
  dsimp [relGraph]
  apply propext
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro h1
  obtain ⟨b1, h2, h3⟩ := h1
  rw [h2]
  rw [h3]
  -- hRight
  intro h1
  exists (f a1)

--------------------------------------------------------------------------------
-- 450：決定的遷移（graph f）での must：1-step で閉じていれば must = B
-- (∀ a, B a → B (f a)) → must (graph f) B = B
--
-- ヒント：
--   (→) は ex425（must ⊆ₚ B）
--   (←) は ex432 を使って「∀n, B(iter f n a)」を n で帰納
--------------------------------------------------------------------------------
theorem ex450 (f : α → α) (B : Pred α) :
    (∀ a, B a → B (f a)) → must (relGraph f) B = B := by
  -- 仮定「B a なら B (f a)」は、B が f による 1ステップ遷移で閉じている（不変）ことを意味する。
  -- graph f は決定的遷移なので、must (graph f) B は「反復しても常に B に留まる」集合になる（ex432）。
  -- その不変性から B の要素はすべて must に入り、逆向きは 0歩到達で自明なので、must (graph f) B = B。
  -- TODO
  sorry

end TL
