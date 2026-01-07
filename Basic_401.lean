--------------------------------------------------------------------------------
-- Basic_401.lean
-- 演習問題 401〜420（ホーア論理 / シミュレーション / 交換性）
-- ※ import Mathlib なし
--------------------------------------------------------------------------------

variable {α β γ : Type}

-- =============================================================================
-- 前提定義 (Definitions from 301-400)
-- =============================================================================

-- ■ 二項関係と基本演算
def Rel (α β : Type) := α → β → Prop

def relComp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, R a b ∧ S b c

def relAdd (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∨ S a b

def relMul (R S : Rel α β) : Rel α β :=
  fun a b => R a b ∧ S a b

def RelLe (R S : Rel α β) : Prop :=
  ∀ a b, R a b → S a b

def relId (α : Type) : Rel α α :=
  fun a b => a = b

def relTrans (R : Rel α β) : Rel β α :=
  fun b a => R a b

-- ■ 閉包 (Kleene Star)
def relPow (R : Rel α α) : Nat → Rel α α
  | 0 => relId α
  | Nat.succ n => relComp (relPow R n) R

def relStar (R : Rel α α) : Rel α α :=
  fun a b => ∃ n, relPow R n a b

-- ■ 述語 (Pred) と像・逆像
def Pred (X : Type) := X → Prop

def PredLe {X : Type} (A B : Pred X) : Prop := ∀ x, A x → B x
infix:50 " ⊆ₚ " => PredLe

def predAdd {X : Type} (A B : Pred X) : Pred X := fun x => A x ∨ B x
def predMul {X : Type} (A B : Pred X) : Pred X := fun x => A x ∧ B x

def relImg (R : Rel α β) (A : Pred α) : Pred β :=
  fun b => ∃ a, A a ∧ R a b

-- 最弱前置条件 (Weakest Precondition) の全称版
def relPreAll (R : Rel α β) (B : Pred β) : Pred α :=
  fun a => ∀ b, R a b → B b

-- =============================================================================
-- 必要な補題 (Lemmas from 301-400)
-- ※ 401以降の演習で「証明済み」として使って良い定理です
-- =============================================================================

-- star は reflexive
theorem ex368 (R : Rel α α) : RelLe (relId α) (relStar R) := sorry

-- star の最小性 (Induction Principle)
-- Reflexive かつ Transitive な X に R が含まれるなら、star R も X に含まれる
def Reflexive (X : Rel α α) : Prop := RelLe (relId α) X
def Transitive (X : Rel α α) : Prop := RelLe (relComp X X) X

theorem ex388 (R X : Rel α α) :
    Reflexive X → Transitive X → RelLe R X → RelLe (relStar R) X := sorry

-- star の冪等性
theorem ex382 (R : Rel α α) : relStar (relStar R) = relStar R := sorry

-- R ; star ⊆ star
theorem ex387 (R : Rel α α) : RelLe (relComp R (relStar R)) (relStar R) := sorry

-- =============================================================================
-- 演習問題 401〜420
-- =============================================================================

--------------------------------------------------------------------------------
-- ホーア論理（Hoare Logic）の基礎
-- プログラム検証で使われる {P} c {Q} を関係代数で定式化します。
--------------------------------------------------------------------------------

-- ■ ホーアトリプル (Hoare Triple)
-- 意味：「状態 P からプログラム R を実行して停止したならば、その後の状態は必ず Q である」
-- （部分正当性：停止しない場合は問わない）
def Hoare (P : Pred α) (R : Rel α α) (Q : Pred α) : Prop :=
  ∀ s e, P s → R s e → Q e

-- 401：ホーアトリプル ↔ 像の包含
-- {P} R {Q} ↔ Img R P ⊆ Q
theorem ex401 (P : Pred α) (R : Rel α α) (Q : Pred α) :
    Hoare P R Q ↔ (relImg R P ⊆ₚ Q) := by
  dsimp [Hoare, PredLe, relImg]
  refine ⟨?hLeft, ?hRight⟩
  sorry
  sorry

-- 402：ホーアトリプル ↔ 最弱前置条件（wp）への包含
-- {P} R {Q} ↔ P ⊆ PreAll R Q
-- ヒント：relPreAll の定義（∀ b, R a b → B b）を思い出す
theorem ex402 (P : Pred α) (R : Rel α α) (Q : Pred α) :
    Hoare P R Q ↔ (P ⊆ₚ relPreAll R Q) := by
  dsimp [Hoare, PredLe, relPreAll]
  sorry

-- 403：SKIP 規則
-- 「何もしない」プログラムでは、事前条件と事後条件が同じなら成り立つ
-- {P} id {P}
theorem ex403 (P : Pred α) :
    Hoare P (relId α) P := by
  dsimp [Hoare, relId]
  sorry

-- 404：合成規則（Sequence Rule）
-- {P} R {Q} かつ {Q} S {T} ならば {P} (R;S) {T}
-- プログラムを連結する際の基本ルール
theorem ex404 (P Q T : Pred α) (R S : Rel α α) :
    Hoare P R Q → Hoare Q S T → Hoare P (relComp R S) T := by
  dsimp [Hoare, relComp]
  sorry

-- 405：帰結規則（Consequence Rule）
-- 事前条件を強めても(P'⊆P)、事後条件を弱めても(Q⊆Q')、正当性は保たれる
theorem ex405 (P P' Q Q' : Pred α) (R : Rel α α) :
    (P' ⊆ₚ P) → (Q ⊆ₚ Q') → Hoare P R Q → Hoare P' R Q' := by
  dsimp [Hoare, PredLe]
  sorry

-- 406：選択規則（Choice / If Rule）
-- {P} R {Q} かつ {P} S {Q} ならば {P} (R ∪ S) {Q}
-- ※ if文の分岐に相当（ガード条件は R, S 側に組み込まれていると考える）
theorem ex406 (P Q : Pred α) (R S : Rel α α) :
    Hoare P R Q → Hoare P S Q → Hoare P (relAdd R S) Q := by
  dsimp [Hoare, relAdd]
  sorry

-- 407：ループ規則（While Rule / Loop Invariant）
-- {I} R {I} （ループ不変条件 I が保たれる）ならば {I} R* {I}
-- ヒント：388 (star の最小性) あるいは induction を使う
theorem ex407 (I : Pred α) (R : Rel α α) :
    Hoare I R I → Hoare I (relStar R) I := by
  dsimp [Hoare]
  sorry

--------------------------------------------------------------------------------
-- 408：PreAll (wp) の分配法則（AND）
-- wp(R, A ∩ B) ↔ wp(R, A) ∩ wp(R, B)
-- 「両方を満たす状態へ行く」↔「Aへ行く条件 かつ Bへ行く条件」
theorem ex408 (R : Rel α α) (A B : Pred α) :
    relPreAll R (predMul A B) = predMul (relPreAll R A) (relPreAll R B) := by
  funext s
  dsimp [relPreAll, predMul]
  apply propext
  refine ⟨?hLeft, ?hRight⟩
  sorry
  sorry

-- 409：PreAll (wp) の分配法則（OR）についての注意
-- wp(R, A ∪ B) ← wp(R, A) ∪ wp(R, B) は成り立つが、逆は一般に成り立たない
-- （非決定性計算の場合、「Aに行くかBに行くか決まっていないがどちらかには行く」状態がありうるため）
-- ここでは片方向（安全側）のみ証明
theorem ex409 (R : Rel α α) (A B : Pred α) :
    (predAdd (relPreAll R A) (relPreAll R B)) ⊆ₚ (relPreAll R (predAdd A B)) := by
  dsimp [PredLe, predAdd, relPreAll]
  sorry

-- 410：矛盾からの帰結
-- {False} R {Q} は常に成り立つ（Ex Falso Quodlibet）
theorem ex410 (R : Rel α α) (Q : Pred α) :
    Hoare (fun _ => False) R Q := by
  dsimp [Hoare]
  sorry

--------------------------------------------------------------------------------
-- シミュレーション（Simulation）
-- 2つのシステム（関係）R1, R2 の間の「振る舞いの包含」を定義します。
--------------------------------------------------------------------------------

-- 定義：関係 S が R1 から R2 へのシミュレーションであるとは、
-- 「R1 で1歩進めるなら、Sで対応する先でも R2 で1歩進んで、再び S で対応する」こと。
-- 図式： R1 ; S ⊆ S ; R2  (可換図式の不等式版)
--     s1 --S--> s2
--     |         |
--    R1        R2
--     ↓         ↓
--    e1 --S--> e2
--
def Simulation (S : Rel α β) (R1 : Rel α α) (R2 : Rel β β) : Prop :=
  RelLe (relComp R1 S) (relComp S R2)

-- 411：恒等関係はシミュレーション（自分自身は自分自身をシミュレートする）
theorem ex411 (R : Rel α α) :
    Simulation (relId α) R R := by
  dsimp [Simulation, RelLe, relComp, relId]
  sorry

-- 412：シミュレーションの合成
-- S が R1→R2、T が R2→R3 のシミュレーションなら、S;T は R1→R3 のシミュレーション
theorem ex412 (S : Rel α β) (T : Rel β γ) (R1 : Rel α α) (R2 : Rel β β) (R3 : Rel γ γ) :
    Simulation S R1 R2 → Simulation T R2 R3 → Simulation (relComp S T) R1 R3 := by
  dsimp [Simulation, RelLe]
  sorry

-- 413：冪乗のシミュレーション
-- S が R1→R2 のシミュレーションなら、R1^n → R2^n も S でシミュレートできる
-- ヒント：induction n
theorem ex413 (S : Rel α β) (R1 : Rel α α) (R2 : Rel β β) :
    Simulation S R1 R2 → ∀ n, Simulation S (relPow R1 n) (relPow R2 n) := by
  intro hSim n
  induction n with
  | zero => sorry
  | succ n ih => sorry

-- 414：スター閉包のシミュレーション（重要定理）
-- S が R1→R2 のシミュレーションなら、Star R1 → Star R2 も S でシミュレートできる
-- ヒント：ex413 を使う
theorem ex414 (S : Rel α β) (R1 : Rel α α) (R2 : Rel β β) :
    Simulation S R1 R2 → Simulation S (relStar R1) (relStar R2) := by
  dsimp [Simulation, RelLe, relComp, relStar]
  sorry

--------------------------------------------------------------------------------
-- 可換性とコンフルエンス（Confluence）
--------------------------------------------------------------------------------

-- 415：可換な関係 (Commuting Relations)
-- R ; S = S ; R
-- これが成り立つと (R;S)^n = R^n ; S^n が言える（ex384の一般化）
theorem ex415 (R S : Rel α α) (n : Nat) :
    relComp R S = relComp S R → relComp (relPow R n) (relPow S n) = relPow (relComp R S) n := by
  -- 実は「relComp R S = relComp S R」だけだと証明はかなり面倒（二項定理的な展開が必要）
  -- ここでは簡単なケース：R と S が可換なら、(R;S)^2 = R^2 ; S^2 の包含だけでもやってみましょう
  -- または問題を単純化して「R;S ⊆ S;R (Diamond Property) なら R^n;S ⊆ S;R^n」など
  sorry -- 難易度が高いのでスキップ、または挑戦したい場合はどうぞ

-- 代わりに基礎的な可換性の補題
-- 415 (改)：Diamond Property (局所合流性)
-- R⁻¹ ; R ⊆ R ; R⁻¹  （山を登って下りる経路は、下りてから登る経路で代替できる）
def DiamondProperty (R : Rel α α) : Prop :=
  RelLe (relComp (relTrans R) R) (relComp R (relTrans R))

-- 416：Church-Rosser Property (合流性)
-- R* ; (R*)⁻¹ ⊆ (R*)⁻¹ ; R*
-- 「計算の分岐はいずれ合流する」
def Confluence (R : Rel α α) : Prop :=
  RelLe (relComp (relStar R) (relTrans (relStar R))) (relComp (relTrans (relStar R)) (relStar R))

-- 417：Semi-Confluence implies Confluence (概要のみ)
-- 実は「DiamondProperty R」ならば「Confluence R」が成り立ちます（証明は長いので定義のみ確認）
-- これが λ計算の計算結果の一意性保証に使われます。

--------------------------------------------------------------------------------
-- 418〜420：Star の代数的性質（総仕上げ）
--------------------------------------------------------------------------------

-- 418：Star の展開（左再帰）
-- R* = id ∪ R ; R*
theorem ex418 (R : Rel α α) :
    relStar R = relAdd (relId α) (relComp R (relStar R)) := by
  funext a b
  apply propext
  constructor
  -- (→)
  · intro h
    dsimp [relStar] at h
    obtain ⟨n, hn⟩ := h
    cases n with
    | zero => sorry
    | succ n => sorry
  -- (←)
  · intro h
    cases h with
    | inl hId => sorry
    | inr hComp => sorry

-- 419：Star の冪等性
-- (R*)* = R*
-- ※ ex382 で証明済みですが、シミュレーションの観点で再確認
theorem ex419 (R : Rel α α) :
    relStar (relStar R) = relStar R := by
  sorry

-- 420：2つの関係の Star の包含
-- (R ∪ S)* = (R* ; S)* ; R*
-- これは正規表現の重要公式ですが、証明は大変なので、
-- もっと簡単な「R ⊆ S → R* ⊆ S*」は証明済み (ex370) なので、
-- 「(R ∪ S)* は R と S を含む最小の Star」であることを確認する問題にします。
-- (relAdd R S) ⊆ X ∧ Reflexive X ∧ Transitive X → (relStar (relAdd R S)) ⊆ X
theorem ex420 (R S X : Rel α α) :
    Reflexive X → Transitive X → RelLe R X → RelLe S X → RelLe (relStar (relAdd R S)) X := by
  sorry
