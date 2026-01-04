namespace TL
--------------------------------------------------------------------------------
-- 演習問題 351〜370（実践寄せ：残余 / ガロア対応 / 閉包 / グラフ関係で単射・全射）
-- ※ import Mathlib なし
-- ※ 301〜340 で定義した Rel / relComp / relAdd / relMul / relTrans / relTensor / RelLe / rRes がある前提
--------------------------------------------------------------------------------

variable {α β γ δ ε : Type}

def Rel (α β : Type) := α → β → Prop

-- 関係の合成（＝ 収縮 / 最小の Einstein summation）
def relComp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, R a b ∧ S b c

def relAdd (R S : Rel α β) : Rel α β := fun a b => R a b ∨ S a b
def relMul (R S : Rel α β) : Rel α β := fun a b => R a b ∧ S a b

def RelLe (R S : Rel α β) : Prop := ∀ a b, R a b → S a b

def rRes (S : Rel α γ) (T : Rel β γ) : Rel β α :=
  fun b a => ∀ c, S a c → T b c

def relTrans (R : Rel α β) : Rel β α := fun b a => R a b

def relId (α : Type) : Rel α α := fun a b => a = b

--------------------------------------------------------------------------------
-- 351：residuation（ガロア対応）完全版（右残余）
-- (R;S) ⊆ T  ↔  R ⊆ (S ▷ T)
--
-- ヒント：
--   (→) は 350 と同じ
--   (←) は witness b を取り、(R ⊆ rRes S T) を b に適用して c に流す
example (R : Rel β α) (S : Rel α γ) (T : Rel β γ) :
    RelLe (relComp R S) T ↔ RelLe R (rRes S T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 352：左残余を定義して residuation（左側版）
-- (R;S) ⊆ T  ↔  S ⊆ (R ⊲ T)
--
-- 定義：lRes R T : Rel β γ
--   lRes R T b c := ∀ a, R a b → T a c
def lRes (R : Rel α β) (T : Rel α γ) : Rel β γ :=
  fun b c => ∀ a, R a b → T a c

example (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    RelLe (relComp R S) T ↔ RelLe S (lRes R T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 353：右残余 rRes の単調性（T側は単調、S側は反単調）
-- (a) S ⊆ S' なら  (S' ▷ T) ⊆ (S ▷ T)   （反単調）
example (S S' : Rel α γ) (T : Rel β γ) :
    RelLe S S' → RelLe (rRes S' T) (rRes S T) := by
  -- TODO
  sorry

-- (b) T ⊆ T' なら  (S ▷ T) ⊆ (S ▷ T')   （単調）
example (S : Rel α γ) (T T' : Rel β γ) :
    RelLe T T' → RelLe (rRes S T) (rRes S T') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 354：左残余 lRes も同様（R側は反単調、T側は単調）
-- (a) R ⊆ R' なら  (R' ⊲ T) ⊆ (R ⊲ T)
example (R R' : Rel α β) (T : Rel α γ) :
    RelLe R R' → RelLe (lRes R' T) (lRes R T) := by
  -- TODO
  sorry

-- (b) T ⊆ T' なら  (R ⊲ T) ⊆ (R ⊲ T')
example (R : Rel α β) (T T' : Rel α γ) :
    RelLe T T' → RelLe (lRes R T) (lRes R T') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 355：transpose と残余の対応（式変形できるように）
-- (S ▷ T)ᵀ = (Sᵀ ⊲ Tᵀ)
--
-- ヒント：funext a; funext b; rfl（dsimp すると同じ形になる）
example (S : Rel α γ) (T : Rel β γ) :
    relTrans (rRes S T) = lRes (relTrans S) (relTrans T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 356：合成の domain（到達可能な入力）を“実用形”に展開
-- dom(R;S) a ↔ ∃b, R a b ∧ dom(S) b
def dom (R : Rel α β) : α → Prop := fun a => ∃ b, R a b

example (R : Rel α β) (S : Rel β γ) :
    ∀ a, dom (relComp R S) a ↔ ∃ b, R a b ∧ dom S b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 357：合成の codomain（到達可能な出力）を“実用形”に展開
-- cod(R;S) c ↔ ∃b, cod(R) b ∧ S b c
def cod (R : Rel α β) : β → Prop := fun b => ∃ a, R a b

example (R : Rel α β) (S : Rel β γ) :
    ∀ c, cod (relComp R S) c ↔ ∃ b, cod R b ∧ S b c := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 358：∧（mask）を合成の左から押し込む（片方向だけ成り立つ）
-- (R∧M);S ⊆ (R;S) ∧ (M;S)
example (R M : Rel α β) (S : Rel β γ) :
    RelLe (relComp (relMul R M) S) (relMul (relComp R S) (relComp M S)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 359：∧（mask）を合成の右から押し込む（片方向）
-- R;(S∧T) ⊆ (R;S) ∧ (R;T)
example (R : Rel α β) (S T : Rel β γ) :
    RelLe (relComp R (relMul S T)) (relMul (relComp R S) (relComp R T)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 360：mask と add の分配（点ごとの ↔）
-- (R∨S)∧M ↔ (R∧M) ∨ (S∧M)
example (R S M : Rel α β) :
    ∀ a b,
      relMul (relAdd R S) M a b ↔ relAdd (relMul R M) (relMul S M) a b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 361〜365：関数をグラフ関係として見たときの単射・全射
--------------------------------------------------------------------------------

def relGraph (f : α → β) : Rel α β := fun a b => f a = b

-- 361：常に成り立つ：id ⊆ graph ; graphᵀ（反射性）
-- ヒント：a=a を仮定して witness を f a にする
example (f : α → β) :
    RelLe (relId α) (relComp (relGraph f) (relTrans (relGraph f))) := by
  -- TODO
  sorry

-- 362：単射 ↔ graph ; graphᵀ ⊆ id
-- ヒント：
--   (→) ∃b, f a=b ∧ f a'=b から f a = f a' を作って injective で落とす
--   (←) f a = f a' から witness b := f a で合成を作って ⊆id で落とす
example (f : α → β) :
    _root_.Function.Injective f ↔
      RelLe (relComp (relGraph f) (relTrans (relGraph f))) (relId α) := by
  -- TODO
  sorry

-- 363：常に成り立つ：graphᵀ ; graph ⊆ id（同じ x から出たら同じ y）
example (f : α → β) :
    RelLe (relComp (relTrans (relGraph f)) (relGraph f)) (relId β) := by
  -- TODO
  sorry

-- 364：全射 ↔ id ⊆ graphᵀ ; graph
-- ヒント：
--   (→) y を任意に、全射で x を取って witness にする
--   (←) id y y を ⊆ に流して witness x を回収する
example (f : α → β) :
    _root_.Function.Surjective f ↔
      RelLe (relId β) (relComp (relTrans (relGraph f)) (relGraph f)) := by
  -- TODO
  sorry

-- 365：全単射 ↔ 「両側が id になる」（関係的な“逆行列”）
-- ※ Function.Bijective f は Injective ∧ Surjective

-- Mathlib なし環境では Function.Bijective が無いことがあるので自作する
def Bijective (f : α → β) : Prop :=
  _root_.Function.Injective f ∧ _root_.Function.Surjective f

example (f : α → β) :
    Bijective f ↔
      (relComp (relGraph f) (relTrans (relGraph f)) = relId α) ∧
      (relComp (relTrans (relGraph f)) (relGraph f) = relId β) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 366〜370：閉包（Kleene star の入口：反復合成）
--------------------------------------------------------------------------------

def relPow (R : Rel α α) : Nat → Rel α α
  | 0       => relId α
  | Nat.succ n => relComp (relPow R n) R

def relStar (R : Rel α α) : Rel α α :=
  fun a b => ∃ n, relPow R n a b

-- 366：relPow は関係に関して単調（R ⊆ S なら pow R n ⊆ pow S n）
-- ヒント：induction n with | zero => ... | succ n ih => ...
example (R S : Rel α α) :
    RelLe R S → ∀ n, RelLe (relPow R n) (relPow S n) := by
  -- TODO
  sorry

-- 367：反復の連結（経路の連結）：pow m ; pow n ⊆ pow (m+n)
-- ヒント：induction n
--   n=0: 右単位元（308 相当）で
--   succ: 306 で括弧を動かして ih を使う（最後に Nat.add_succ ）
example (R : Rel α α) :
    ∀ m n, RelLe (relComp (relPow R m) (relPow R n)) (relPow R (m + n)) := by
  -- TODO
  sorry

-- 368：star は reflexive：id ⊆ star
-- ヒント：n := 0 を witness に
example (R : Rel α α) : RelLe (relId α) (relStar R) := by
  -- TODO
  sorry

-- 369：star は transitive：star ; star ⊆ star
-- ヒント：
--   obtain ⟨m, hm⟩ := ...
--   obtain ⟨n, hn⟩ := ...
--   witness は m+n、367 を使う
example (R : Rel α α) :
    RelLe (relComp (relStar R) (relStar R)) (relStar R) := by
  -- TODO
  sorry

-- 370：star は単調（R ⊆ S なら star R ⊆ star S）
-- ヒント：
--   obtain ⟨n, hn⟩ := hstar
--   exact ⟨n, (366 hRS n _ _ hn)⟩
example (R S : Rel α α) :
    RelLe R S → RelLe (relStar R) (relStar S) := by
  -- TODO
  sorry

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
end TL
