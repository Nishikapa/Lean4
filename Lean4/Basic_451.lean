--------------------------------------------------------------------------------
-- Basic_451.lean
-- 演習問題 451〜470（テンソル的法則 / reach・must の閉包演算子 / residual設計）
-- ※ import Mathlib なし
-- ※ 401〜450 は Basic_401 を import して再利用
--------------------------------------------------------------------------------

import Lean4.Basic_101
import Lean4.Basic_151
import Lean4.Basic_201
import Lean4.Basic_301
import Lean4.Basic_351
import Lean4.Basic_401

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 451：合成の結合律（テンソル縮約の結合性）
-- (R;S);T = R;(S;T)
--
-- ヒント：
--   funext a d; apply propext
--   constructor <;> intro h
--   h から witness を取り直す（∃ の並べ替え）
--------------------------------------------------------------------------------
theorem ex451 (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    relComp (relComp R S) T = relComp R (relComp S T) := by

  funext a1 g1
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  intro h1
  obtain ⟨g2, ⟨b1, h2, h3⟩, h4⟩ := h1
  exists b1
  constructor
  exact h2
  exists g2
  intro h5
  obtain ⟨c1, h6, ⟨g3, h7, h8⟩⟩ := h5
  exists g3
  constructor
  exists c1
  exact h8

--------------------------------------------------------------------------------
-- 452：左単位元（id;R = R）
--
-- ヒント：
--   funext a b; apply propext; constructor <;> intro h
--   relId の witness は rfl
--------------------------------------------------------------------------------
theorem ex452 (R : Rel α β) :
    relComp (relId α) R = R := by

  funext a1 b1
  dsimp [relComp, relId]
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  obtain ⟨b2, h2, h3⟩ := h1
  rw [h2]
  exact h3

  -- fRight
  intro h4
  exists a1

--------------------------------------------------------------------------------
-- 453：右単位元（R;id = R）
--------------------------------------------------------------------------------
theorem ex453 (R : Rel α β) :
    relComp R (relId β) = R := by
  funext a1 b1
  dsimp [relComp, relId]
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  obtain ⟨c1, h2, h3⟩ := h1
  rw [←h3]
  exact h2

  -- fRight
  intro h4
  exists b1

--------------------------------------------------------------------------------
-- 454：合成は左の和（∨）に分配する
-- (R+S);T = (R;T) + (S;T)
--
-- ヒント：
--   dsimp [relComp, relAdd]; funext a c; apply propext
--   witness を取り、cases で ∨ を分解
--------------------------------------------------------------------------------
theorem ex454 (R S : Rel α β) (T : Rel β γ) :
    relComp (relAdd R S) T = relAdd (relComp R T) (relComp S T) := by

  funext a1 g1
  apply propext
  refine ⟨?fLeft, ?fRight⟩
  -- fLeft
  intro h1
  obtain ⟨b1, h2|h3, h4⟩ := h1
  -- fLeft.inl
  left
  exists b1
  -- hLeft.inr
  right
  exists b1
  --- fRight
  intro h5
  obtain ⟨b1, h6, h7⟩ | ⟨b1, h8, h9⟩ := h5
  -- fRight.inl
  exists b1
  constructor
  left
  exact h6
  exact h7
  -- fRight.inr
  exists b1
  constructor
  right
  exact h8
  exact h9

--------------------------------------------------------------------------------
-- 455：合成は右の和（∨）に分配する
-- R;(S+T) = (R;S) + (R;T)
--------------------------------------------------------------------------------
theorem ex455 (R : Rel α β) (S T : Rel β γ) :
    relComp R (relAdd S T) = relAdd (relComp R S) (relComp R T) := by
  funext a1 g1
  apply propext
  refine ⟨?fLeft, ?fRight⟩
  -- fLeft
  intro h1
  obtain ⟨b1, h2, h3|h4⟩ := h1
  -- fLeft.inl
  left
  exists b1
  -- fLeft.inr
  right
  exists b1
  --- fRight
  intro h5
  obtain ⟨b1, h6, h7⟩ | ⟨b1, h8, h9⟩ := h5
  -- fRight.inl
  exists b1
  constructor
  -- fRight.inl.left
  exact h6
  -- fRight.inl.right
  left
  exact h7
  -- fRight.inr
  exists b1
  constructor
  -- fRight.inr.left
  exact h8
  -- fRight.inr.right
  right
  exact h9

--------------------------------------------------------------------------------
-- 456：transpose は 2回で元に戻る（反変×反変 = 共変）
-- (Rᵀ)ᵀ = R
--
-- ヒント：rfl で通るはず
--------------------------------------------------------------------------------
theorem ex456 (R : Rel α β) :
    relTrans (relTrans R) = R := by
  funext a1 b1
  rfl

--------------------------------------------------------------------------------
-- 457：transpose は合成の順序を逆にする
-- (R;S)ᵀ = Sᵀ ; Rᵀ
--
-- ヒント：
--   funext c a; apply propext; constructor <;> intro h
--   h の witness をそのまま使う
--------------------------------------------------------------------------------
theorem ex457 (R : Rel α β) (S : Rel β γ) :
    relTrans (relComp R S) = relComp (relTrans S) (relTrans R) := by
  funext g1 a1
  apply propext
  refine ⟨?fLeft, ?fRight⟩
  -- fLeft
  intro h1
  obtain ⟨b1, h2, h3⟩ := h1
  exists b1
  -- fRight
  intro h4
  obtain ⟨b1, h5, h6⟩ := h4
  exists b1

--------------------------------------------------------------------------------
-- Pred の補助：⊤ / ⊥
--------------------------------------------------------------------------------
def predTop {X : Type} : Pred X := fun _ => True
def predBot {X : Type} : Pred X := fun _ => False

--------------------------------------------------------------------------------
-- 458：reach は集合の和（∨）に分配する
-- reach R (A ∪ C) = reach R A ∪ reach R C
--
-- ヒント：
--   funext x; apply propext
--   dsimp [reach, relImg, relStar, predAdd]
--   ∃a, (A a ∨ C a) ∧ ... を ∨ に押し出す
--------------------------------------------------------------------------------
theorem ex458 (R : Rel α α) (A C : Pred α) :
    reach R (predAdd A C) = predAdd (reach R A) (reach R C) := by

  funext a1
  dsimp [reach]
  dsimp [relImg]
  dsimp [predAdd]
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  obtain ⟨a2, h2|h3, ⟨n1, h4⟩⟩ := h1

  -- fLeft.inl
  dsimp [relImg]
  dsimp [relStar]
  left
  exists a2
  constructor
  exact h2
  exists n1

  -- fLeft.inr
  dsimp [relImg]
  dsimp [relStar]
  right
  exists a2
  constructor
  exact h3
  exists n1

  --- fRight
  dsimp [relImg]
  dsimp [relStar]
  intro h5
  obtain ⟨a3, h6, ⟨n2, h7⟩⟩ | ⟨a4, h8, ⟨n3, h9⟩⟩ := h5

  -- fRight.inl
  exists a3
  constructor
  left
  exact h6
  exists n2

  -- fRight.inr
  exists a4
  constructor
  right
  exact h8
  exists n3

--------------------------------------------------------------------------------
-- 459：must は集合の積（∧）に分配する
-- must R (B ∩ C) = must R B ∩ must R C
--
-- ヒント：
--   funext a; apply propext
--   dsimp [must, relPreAll, relStar, predMul]
--   (A → (P ∧ Q)) ↔ (A→P) ∧ (A→Q)
--------------------------------------------------------------------------------
theorem ex459 (R : Rel α α) (B C : Pred α) :
    must R (predMul B C) = predMul (must R B) (must R C) := by

  funext a1
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  constructor

  -- fLeft.left
  intro b1 h2
  obtain ⟨h3, h4⟩ := h1 b1 h2
  exact h3

  -- fLeft.right
  intro b2 h5
  obtain ⟨h6,  h7⟩ := h1 b2 h5
  exact h7

  --- fRight
  intro h8 b3 h9
  obtain ⟨h10, h11⟩ := h8
  obtain h12 := h10 b3 h9
  obtain h13 := h11 b3 h9
  constructor
  exact h12
  exact h13

--------------------------------------------------------------------------------
-- 460：reach は ⊥ を保つ（空集合からは何も到達しない）
-- reach R ⊥ = ⊥
--------------------------------------------------------------------------------
theorem ex460 (R : Rel α α) :
    reach R (predBot : Pred α) = (predBot : Pred α) := by

  funext a1
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  obtain ⟨a2, h2, ⟨n1, h3⟩⟩ := h1
  exact h2

  -- fRight
  intro h4
  contradiction

--------------------------------------------------------------------------------
-- 461：must は ⊤ を保つ（どこに行っても True）
-- must R ⊤ = ⊤
--------------------------------------------------------------------------------
theorem ex461 (R : Rel α α) :
    must R (predTop : Pred α) = (predTop : Pred α) := by

  funext a1
  apply propext
  refine ⟨?fLeft, ?fRight⟩

  -- fLeft
  intro h1
  obtain h2 := h1 a1
  apply h2
  exists 0

  -- fRight
  intro h3 b1 h4
  exact h3

--------------------------------------------------------------------------------
-- 462：Closed は積（∧）で閉じる（共通部分も Closed）
-- Closed R X ∧ Closed R Y → Closed R (X ∩ Y)
--
-- ヒント：
--   dsimp [Closed, PredLe, relImg, predMul]
--   witness を取り、両方の Closed を使う
--------------------------------------------------------------------------------
theorem ex462 (R : Rel α α) (X Y : Pred α) :
    Closed R X → Closed R Y → Closed R (predMul X Y) := by

  intro h1 h2 a1 h3
  obtain ⟨a2, ⟨h4, h5⟩, h6⟩ := h3
  obtain h7 := h1 a1
  obtain h8 := h2 a1
  constructor

  -- left
  apply h7
  exists a2

  -- hLeft
  apply h8
  exists a2

--------------------------------------------------------------------------------
-- 463：Closed は和（∨）で閉じる（和集合も Closed）
--------------------------------------------------------------------------------
theorem ex463 (R : Rel α α) (X Y : Pred α) :
    Closed R X → Closed R Y → Closed R (predAdd X Y) := by

  intro h1 h2 a1 h3
  obtain h4 := h1 a1
  obtain h5 := h2 a1
  obtain ⟨a2, h6|h7, h8⟩ := h3

  -- inl
  left
  apply h4
  exists a2

  -- inr
  right
  apply h5
  exists a2

--------------------------------------------------------------------------------
-- 464：reach は「A を含む最小の Closed 集合」（実用形）
-- A ⊆ X かつ Closed R X なら reach R A ⊆ X
--
-- ヒント：Basic_401 の ex411 を B := X で使うと一瞬
--------------------------------------------------------------------------------
theorem ex464 (R : Rel α α) (A X : Pred α) :
    (A ⊆ₚ X) → Closed R X → (reach R A ⊆ₚ X) := by

  intro h1 h2 a1 h3
  obtain ⟨a2, h4, ⟨n1, h5⟩⟩ := h3
  revert a1 a2
  induction n1 with
  | zero =>
    intro a1 a2 h6 h7
    apply h1
    rw [←h7]
    exact h6
  | succ n1 ih =>
    intro a3 a4 h6 h7
    obtain ⟨a5, h8, h9⟩ := h7
    obtain h10 := ih a5 a4
    apply h2
    exists a5
    constructor
    apply h10
    exact h6
    exact h8
    exact h9

--------------------------------------------------------------------------------
-- 465：must は「B の中で最大の Closed 集合」（実用形）
-- X ⊆ B かつ Closed R X なら X ⊆ must R B
--
-- ヒント：Basic_401 の ex427 をそのまま使える
--------------------------------------------------------------------------------
theorem ex465 (R : Rel α α) (B X : Pred α) :
    (X ⊆ₚ B) → Closed R X → (X ⊆ₚ must R B) := by

  dsimp [PredLe]
  dsimp [Closed]
  dsimp [must]
  dsimp [relPreAll]
  dsimp [relStar]
  intro h1 h2 a1 h3 a2 h4
  dsimp [PredLe, relImg] at h2
  obtain ⟨n1, h5⟩ := h4
  revert a1 a2
  induction n1 with
  | zero =>
    intro a1 a2 h6 h7
    apply h1
    rw [←h7]
    exact a2
  | succ n1 ih =>
    intro a3 h8 a4 h9
    apply h1
    apply h2
    dsimp [relPow, relComp] at h9
    obtain ⟨a5, h10, h11⟩ := h9

    sorry


--------------------------------------------------------------------------------
-- 466：安全集合から到達しても安全（counit 的コロラリ）
-- reach R (must R B) ⊆ B
--
-- ヒント：
--   ex416 : (reach R A ⊆ B) ↔ (A ⊆ must R B)
--   A := must R B を入れて、右側は refl で終わり
--------------------------------------------------------------------------------
theorem ex466 (R : Rel α α) (B : Pred α) :
    reach R (must R B) ⊆ₚ B := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 467：仕様 T を満たす head が2つあるなら、和(head1+head2) も仕様を満たす
-- attn(QK1,KV)⊆T かつ attn(QK2,KV)⊆T なら attn(QK1+QK2,KV)⊆T
--
-- ヒント：
--   ex454 で (QK1+QK2);KV を分解して cases で流す
--------------------------------------------------------------------------------
theorem ex467 (QK1 QK2 : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    (attnRel QK1 KV ⊆ T) →
    (attnRel QK2 KV ⊆ T) →
    (attnRel (relAdd QK1 QK2) KV ⊆ T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 468：和(head1+head2) が仕様を満たすなら、それぞれの head も満たす
--
-- ヒント：
--   QK1 ⊆ QK1+QK2 は自明
--   ex436（attn の単調性）で attn QK1 KV ⊆ attn (QK1+QK2) KV
--   あとは推移
--------------------------------------------------------------------------------
theorem ex468 (QK1 QK2 : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    (attnRel (relAdd QK1 QK2) KV ⊆ T) →
      (attnRel QK1 KV ⊆ T) ∧ (attnRel QK2 KV ⊆ T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 469：residual で “最大の QK” を作る（仕様を必ず満たす）
-- attn( (KV ▷ T) , KV ) ⊆ T
--
-- ヒント：ex433 の (←) 方向を使うだけ
--------------------------------------------------------------------------------
theorem ex469 (KV : Rel β γ) (T : Rel α γ) :
    attnRel (rRes KV T) KV ⊆ T := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 470：residual の最大性（これ以上大きい QK は仕様を壊す）
-- attn(QK,KV) ⊆ T なら QK ⊆ (KV ▷ T)
--
-- ヒント：ex433 の (→) 方向
--------------------------------------------------------------------------------
theorem ex470 (QK : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    (attnRel QK KV ⊆ T) → (QK ⊆ rRes KV T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 471〜500：演習（star の単調性 / reach・must の閉包演算子 / residual の単調性 / 安全設計）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 471：pow の単調性（関係側）
-- R ⊆ S なら pow R n ⊆ pow S n
--
-- ヒント：
--   intro hRS n; induction n with
--   | zero => dsimp [relPow, relId]
--   | succ n ih =>
--       dsimp [relPow, relComp]
--       intro a b h; obtain ⟨m, hm, hR⟩ := h
--       refine ⟨m, ?_, ?_⟩
--       · exact ih _ _ hm
--       · exact hRS _ _ hR
--------------------------------------------------------------------------------
theorem ex471 (R S : Rel α α) :
    (R ⊆ S) → ∀ n, (relPow R n ⊆ relPow S n) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 472：star の単調性（関係側）
-- R ⊆ S なら star R ⊆ star S
--
-- ヒント：
--   dsimp [relStar, RelLe]; intro hRS a b ⟨n, hn⟩; exact ⟨n, (ex471 R S hRS n _ _ hn)⟩
--------------------------------------------------------------------------------
theorem ex472 (R S : Rel α α) :
    (R ⊆ S) → (relStar R ⊆ relStar S) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 473：reach は関係に単調（遷移が増えるほど到達集合は増える）
-- R ⊆ S なら reach R A ⊆ₚ reach S A
--
-- ヒント：
--   dsimp [reach, relImg, PredLe]
--   witness の star を ex472 で押し上げる
--------------------------------------------------------------------------------
theorem ex473 (R S : Rel α α) (A : Pred α) :
    (R ⊆ S) → (reach R A ⊆ₚ reach S A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 474：must は関係に反単調（遷移が増えるほど must は厳しくなる）
-- R ⊆ S なら must S B ⊆ₚ must R B
--
-- ヒント：
--   must = preAll (star ...) B
--   ex472 で starR ⊆ starS を作り、preAll の反単調性を使う
--------------------------------------------------------------------------------
theorem ex474 (R S : Rel α α) (B : Pred α) :
    (R ⊆ S) → (must S B ⊆ₚ must R B) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 475：star の右展開（片方向）
-- star R ⊆ id + (star R ; R)
--
-- ヒント：
--   dsimp [RelLe, relStar, relAdd, relId, relComp]
--   obtain ⟨n, hn⟩ := h; cases n with
--   | zero => left; exact hn
--   | succ n =>
--       right
--       -- hn : relPow R (succ n) a b = relComp (relPow R n) R a b
--       -- witness を hn から取り出し、左側は star で包む
--------------------------------------------------------------------------------
theorem ex475 (R : Rel α α) :
    relStar R ⊆ relAdd (relId α) (relComp (relStar R) R) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 476：star の右展開（逆方向）
-- id + (star R ; R) ⊆ star R
--
-- ヒント：
--   left: n:=0
--   right: (∃m, pow m a x) と R x b から witness (m+1)
--------------------------------------------------------------------------------
theorem ex476 (R : Rel α α) :
    relAdd (relId α) (relComp (relStar R) R) ⊆ relStar R := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 477：star の右展開（等式）
-- star R = id + (star R ; R)
--
-- ヒント：475/476 を両方向で
--------------------------------------------------------------------------------
theorem ex477 (R : Rel α α) :
    relStar R = relAdd (relId α) (relComp (relStar R) R) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 478：reach は「閉包演算子」(closure operator) である（まとめ）
-- (1) A ⊆ₚ reach R A
-- (2) A ⊆ₚ B → reach R A ⊆ₚ reach R B
-- (3) reach R (reach R A) = reach R A
--
-- ヒント：
--   (1) ex442, (2) ex409, (3) ex410 を使って pack するだけ
--------------------------------------------------------------------------------
theorem ex478 (R : Rel α α) :
    (∀ A : Pred α, A ⊆ₚ reach R A) ∧
    (∀ A B : Pred α, (A ⊆ₚ B) → (reach R A ⊆ₚ reach R B)) ∧
    (∀ A : Pred α, reach R (reach R A) = reach R A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 479：must は「内点演算子」(interior operator) である（まとめ）
-- (1) must R B ⊆ₚ B
-- (2) B ⊆ₚ C → must R B ⊆ₚ must R C
-- (3) must R (must R B) = must R B
--
-- ヒント：
--   (1) ex425, (2) ex414, (3) ex446
--------------------------------------------------------------------------------
theorem ex479 (R : Rel α α) :
    (∀ B : Pred α, must R B ⊆ₚ B) ∧
    (∀ B C : Pred α, (B ⊆ₚ C) → (must R B ⊆ₚ must R C)) ∧
    (∀ B : Pred α, must R (must R B) = must R B) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 480：閉じた集合は must で不動点（一般化 ex450）
-- Closed R B → must R B = B
--
-- ヒント：
--   (→) は ex425（must ⊆ B）
--   (←) は B ⊆ must R B を示す：star の証拠 ⟨n, hn⟩ で n に帰納法
--------------------------------------------------------------------------------
theorem ex480 (R : Rel α α) (B : Pred α) :
    Closed R B → must R B = B := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 481：ガロア対応の unit（star 版）
-- A ⊆ₚ must R (reach R A)
--
-- ヒント：
--   ex416 を使って
--     (reach R A ⊆ₚ reach R A) ↔ (A ⊆ₚ must R (reach R A))
--   の左側を refl で潰す
--------------------------------------------------------------------------------
theorem ex481 (R : Rel α α) (A : Pred α) :
    A ⊆ₚ must R (reach R A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 482：ガロア対応の counit（star 版）
-- reach R (must R B) ⊆ₚ B
--
-- ヒント：これは ex466 と同じ。ここでは “再証明” か “exact ex466 _ _”
--------------------------------------------------------------------------------
theorem ex482 (R : Rel α α) (B : Pred α) :
    reach R (must R B) ⊆ₚ B := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 483：rRes は右引数に単調（T ⊆ T' なら S▷T ⊆ S▷T'）
--
-- ヒント：
--   dsimp [RelLe, rRes]
--------------------------------------------------------------------------------
theorem ex483 (S : Rel α γ) (T T' : Rel β γ) :
    (T ⊆ T') → (rRes S T ⊆ rRes S T') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 484：rRes は左引数に反単調（S ⊆ S' なら S'▷T ⊆ S▷T）
--
-- ヒント：
--   dsimp [RelLe, rRes]
--------------------------------------------------------------------------------
theorem ex484 (S S' : Rel α γ) (T : Rel β γ) :
    (S ⊆ S') → (rRes S' T ⊆ rRes S T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 485：lRes は右引数に単調（T ⊆ T' なら R⊲T ⊆ R⊲T'）
--------------------------------------------------------------------------------
theorem ex485 (R : Rel α β) (T T' : Rel α γ) :
    (T ⊆ T') → (lRes R T ⊆ lRes R T') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 486：lRes は左引数に反単調（R ⊆ R' なら R'⊲T ⊆ R⊲T）
--------------------------------------------------------------------------------
theorem ex486 (R R' : Rel α β) (T : Rel α γ) :
    (R ⊆ R') → (lRes R' T ⊆ lRes R T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 487：reach の “反復閉包” 版：reach (star R) A = reach R A
-- （star をさらに star しても到達集合は変わらない）
--
-- ヒント：
--   reach (star R) A = Img(star (star R)) A
--   既に star(star R) = star R を示しているならそれを使う（以前の ex382 相当）
--------------------------------------------------------------------------------
theorem ex487 (R : Rel α α) (A : Pred α) :
    reach (relStar R) A = reach R A := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 488：must の “反復閉包” 版：must (star R) B = must R B
-- （star をさらに star しても must は変わらない）
--
-- ヒント：487 と同様に star(star R)=star R を使う
--------------------------------------------------------------------------------
theorem ex488 (R : Rel α α) (B : Pred α) :
    must (relStar R) B = must R B := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 489：reach は関係の和に対して “下から” 単調
-- reach R A ∪ reach S A ⊆ₚ reach (R+S) A
--
-- ヒント：
--   left/right それぞれ、R ⊆ (R+S) と S ⊆ (R+S) を使って ex473
--------------------------------------------------------------------------------
theorem ex489 (R S : Rel α α) (A : Pred α) :
    predAdd (reach R A) (reach S A) ⊆ₚ reach (relAdd R S) A := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 490：must は関係の和に対して “上から” 反単調
-- must (R+S) B ⊆ₚ must R B ∩ must S B
--
-- ヒント：
--   (R ⊆ R+S) と (S ⊆ R+S) から ex474 を2回使う
--------------------------------------------------------------------------------
theorem ex490 (R S : Rel α α) (B : Pred α) :
    must (relAdd R S) B ⊆ₚ predMul (must R B) (must S B) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 491：Closed は関係の和に関して “積” に分解できる
-- Closed (R+S) X ↔ Closed R X ∧ Closed S X
--
-- ヒント：
--   dsimp [Closed, predMul, PredLe]
--   Img(R+S)X = Img R X ∪ Img S X（あなたの ex405 相当）
--------------------------------------------------------------------------------
theorem ex491 (R S : Rel α α) (X : Pred α) :
    Closed (relAdd R S) X ↔ (Closed R X ∧ Closed S X) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 492：graph の rRes は「右合成」になる
-- rRes (graph f) T b a ↔ T b (f a)
--
-- ヒント：
--   dsimp [rRes, relGraph]
--   (→) は c := f a
--   (←) は h : f a = c で rw [←h]
--------------------------------------------------------------------------------
theorem ex492 (f : α → γ) (T : Rel β γ) :
    rRes (relGraph f) T = (fun b a => T b (f a)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 493：mask を入れると attention の到達は減る（単調性の具体例）
-- attnRel (QK ∧ M) KV ⊆ attnRel QK KV
--
-- ヒント：
--   relMul QK M ⊆ QK は ∧ の左射影
--   ex436（attn の単調性）を使う
--------------------------------------------------------------------------------
theorem ex493 (QK : Rel α β) (M : Rel α β) (KV : Rel β γ) :
    attnRel (relMul QK M) KV ⊆ attnRel QK KV := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 494：residual を使った “安全な QK” 設計（重要）
-- QKsafe := QK ∧ (KV ▷ T) とすると attnRel QKsafe KV ⊆ T
--
-- ヒント：
--   QKsafe ⊆ (KV ▷ T) は ∧ の右射影
--   それを ex433 の (←) へ入れる
--------------------------------------------------------------------------------
theorem ex494 (QK : Rel α β) (KV : Rel β γ) (T : Rel α γ) :
    attnRel (relMul QK (rRes KV T)) KV ⊆ T := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 495：must の “最大性” を residual で言い換える（Unit 埋め込み応用）
-- predAsRel, relToPred を使って：
--   must R B = relToPred (rRes (relStar R) (predAsRel B))
--
-- ヒント：
--   must = preAll(star R) B
--   ex423 を R := (star R) に適用
--------------------------------------------------------------------------------
theorem ex495 (R : Rel α α) (B : Pred α) :
    must R B = relToPred (rRes (relStar R) (predAsRel B)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 496：reach も Unit 埋め込みで合成表示できる（設計の見通し）
-- reach R A b ↔ (predAsRel A ; star R) () b
--
-- ヒント：
--   reach = Img(star R) A
--   ex424 を R := star R に適用
--------------------------------------------------------------------------------
theorem ex496 (R : Rel α α) (A : Pred α) :
    reach R A = (fun b => relComp (predAsRel A) (relStar R) () b) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 497：到達集合 reach R A は “R で閉じている”（再掲の別ルート）
-- Closed R (reach R A)
--
-- ヒント：これはあなたの ex412 と同じ。ここでは別証明でもOK
--------------------------------------------------------------------------------
theorem ex497 (R : Rel α α) (A : Pred α) :
    Closed R (reach R A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 498：安全集合 must R B も “R で閉じている”
-- Closed R (must R B)
--
-- ヒント：これは ex426 と同じ
--------------------------------------------------------------------------------
theorem ex498 (R : Rel α α) (B : Pred α) :
    Closed R (must R B) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 499：Closed の別表現（点ごとの形：再掲）
-- Closed R X ↔ ∀ a b, X a → R a b → X b
--
-- ヒント：これは ex441 と同じ（Basic_401 側にあるはず）
--------------------------------------------------------------------------------
theorem ex499 (R : Rel α α) (X : Pred α) :
    Closed R X ↔ (∀ a b, X a → R a b → X b) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 500：最終：reach/must の “吸収” 形（設計で頻出）
-- reach R (must R B) ⊆ₚ must R B
--
-- ヒント：
--   must R B は Closed（ex498）かつ A := must R B を含むので、
--   「Closed を含むなら reach はそこから出ない」（ex464）を使う
--------------------------------------------------------------------------------
theorem ex500 (R : Rel α α) (B : Pred α) :
    reach R (must R B) ⊆ₚ must R B := by
  -- TODO
  sorry

end TL
