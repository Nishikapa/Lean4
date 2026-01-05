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
theorem theorem351 (R : Rel β α) (S : Rel α γ) (T : Rel β γ) :
    RelLe (relComp R S) T ↔ RelLe R (rRes S T) := by
  dsimp [RelLe, relComp, rRes]
  dsimp [Rel] at R S T
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a b c d e f
  apply a
  refine ⟨?g, ?h, ?i⟩

  -- g
  exact c

  -- h
  exact d

  -- i
  exact f

  -- hRight
  intro g h i j
  obtain ⟨j1, j2, j3⟩ := j
  apply g
  apply j2
  exact j3

--------------------------------------------------------------------------------
-- 352：左残余を定義して residuation（左側版）
-- (R;S) ⊆ T  ↔  S ⊆ (R ⊲ T)
--
-- 定義：lRes R T : Rel β γ
--   lRes R T b c := ∀ a, R a b → T a c
def lRes (R : Rel α β) (T : Rel α γ) : Rel β γ :=
  fun b c => ∀ a, R a b → T a c

theorem theorem352 (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    RelLe (relComp R S) T ↔ RelLe S (lRes R T) := by
  dsimp [RelLe, relComp, lRes]
  dsimp [Rel] at R S T
  refine ⟨?hLeft, ?hRight⟩
  intro a b c d e f
  apply a
  refine ⟨?g, ?h, ?i⟩

  -- g
  exact b

  -- h
  exact f

  -- i
  exact d

  -- hRight
  intro j k l m
  obtain ⟨m1, m2, m3⟩ := m
  apply j
  apply m3
  exact m2

--------------------------------------------------------------------------------
-- 353：右残余 rRes の単調性（T側は単調、S側は反単調）
-- (a) S ⊆ S' なら  (S' ▷ T) ⊆ (S ▷ T)   （反単調）
theorem theorem353_1 (S S' : Rel α γ) (T : Rel β γ) :
    RelLe S S' → RelLe (rRes S' T) (rRes S T) := by
  dsimp [RelLe, rRes]
  dsimp [Rel] at S S' T
  intro h a b c d e
  apply c
  apply h
  exact e

-- (b) T ⊆ T' なら  (S ▷ T) ⊆ (S ▷ T')   （単調）
theorem theorem353_2 (S : Rel α γ) (T T' : Rel β γ) :
    RelLe T T' → RelLe (rRes S T) (rRes S T') := by
  dsimp [RelLe, rRes]
  dsimp [Rel] at S T T'
  intro a b c d e f
  apply a
  apply d
  exact f

--------------------------------------------------------------------------------
-- 354：左残余 lRes も同様（R側は反単調、T側は単調）
-- (a) R ⊆ R' なら  (R' ⊲ T) ⊆ (R ⊲ T)
theorem theorem354_1 (R R' : Rel α β) (T : Rel α γ) :
    RelLe R R' → RelLe (lRes R' T) (lRes R T) := by
  dsimp [RelLe, lRes]
  dsimp [Rel] at R R' T
  intro a b c d e f
  apply d
  apply a
  exact f

-- (b) T ⊆ T' なら  (R ⊲ T) ⊆ (R ⊲ T')
theorem theorem354_2 (R : Rel α β) (T T' : Rel α γ) :
    RelLe T T' → RelLe (lRes R T) (lRes R T') := by
  dsimp [RelLe, lRes]
  dsimp [Rel] at R T T'
  intro a b c d e f
  apply a
  apply d
  exact f

--------------------------------------------------------------------------------
-- 355：transpose と残余の対応（式変形できるように）
-- (S ▷ T)ᵀ = (Sᵀ ⊲ Tᵀ)
--
-- ヒント：funext a; funext b; rfl（dsimp すると同じ形になる）
theorem theorem355 (S : Rel α γ) (T : Rel β γ) :
    relTrans (rRes S T) = lRes (relTrans S) (relTrans T) := by
  funext a b
  dsimp [relTrans, rRes, lRes]

--------------------------------------------------------------------------------
-- 356：合成の domain（到達可能な入力）を“実用形”に展開
-- dom(R;S) a ↔ ∃b, R a b ∧ dom(S) b
def dom (R : Rel α β) : α → Prop := fun a => ∃ b, R a b

theorem theorem356 (R : Rel α β) (S : Rel β γ) :
    ∀ a, dom (relComp R S) a ↔ ∃ b, R a b ∧ dom S b := by
  dsimp [dom, relComp]
  intro a
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro a
  obtain ⟨a1, a2, ⟨a3, a4⟩⟩ := a
  refine ⟨?c, ?d, ?e⟩

  -- c
  exact a2

  -- d
  exact a3

  -- e
  exists a1

  -- hRight
  intro f
  obtain ⟨f1, f2, ⟨f3, f4⟩⟩ := f
  refine ⟨?g, ?h, ?i⟩

  -- g
  exact f3

  -- h
  exact f1

  -- i
  constructor

  -- i.left
  exact f2

  -- i.right
  exact f4

--------------------------------------------------------------------------------
-- 357：合成の codomain（到達可能な出力）を“実用形”に展開
-- cod(R;S) c ↔ ∃b, cod(R) b ∧ S b c
def cod (R : Rel α β) : β → Prop := fun b => ∃ a, R a b

theorem theorem357 (R : Rel α β) (S : Rel β γ) :
    ∀ c, cod (relComp R S) c ↔ ∃ b, cod R b ∧ S b c := by
  dsimp [cod, relComp]
  dsimp [Rel] at R S
  intro a
  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro a
  obtain ⟨a1, a2, ⟨a3, a4⟩⟩ := a

  refine ⟨?c, ⟨?d, ?e⟩, ?f⟩
  -- c
  exact a2

  -- d
  exact a1

  -- e
  exact a3

  -- f
  exact a4

  -- hRight
  intro g
  obtain ⟨g1, ⟨g2, g3⟩, g4⟩ := g
  refine ⟨?h, ?i, ?j, ?k⟩

  -- h
  exact g2

  -- i
  exact g1

  -- j
  exact g3

  -- k
  exact g4

--------------------------------------------------------------------------------
-- 358：∧（mask）を合成の左から押し込む（片方向だけ成り立つ）
-- (R∧M);S ⊆ (R;S) ∧ (M;S)
theorem theorem358 (R M : Rel α β) (S : Rel β γ) :
    RelLe (relComp (relMul R M) S) (relMul (relComp R S) (relComp M S)) := by
  dsimp [RelLe, relComp, relMul]
  dsimp [Rel] at R M S
  intro a b c
  obtain ⟨c1, ⟨c2, c3⟩, c4⟩ := c
  refine ⟨⟨?d, ?e, ?f⟩, ⟨?g,?h,?i⟩⟩
  -- d
  exact c1
  -- e
  exact c2
  -- f
  exact c4
  -- g
  exact c1
  -- h
  exact c3
  -- i
  exact c4

--------------------------------------------------------------------------------
-- 359：∧（mask）を合成の右から押し込む（片方向）
-- R;(S∧T) ⊆ (R;S) ∧ (R;T)
theorem theorem359 (R : Rel α β) (S T : Rel β γ) :
    RelLe (relComp R (relMul S T)) (relMul (relComp R S) (relComp R T)) := by
  dsimp [RelLe, relComp, relMul]
  dsimp [Rel] at R S T
  intro a b c
  obtain ⟨c1, c2, ⟨c3, c4⟩⟩ := c
  refine ⟨⟨?d, ?e, ?f⟩, ⟨?g,?h,?i⟩⟩
  -- d
  exact c1
  -- e
  exact c2
  -- f
  exact c3
  -- g
  exact c1
  -- h
  exact c2
  -- i
  exact c4

--------------------------------------------------------------------------------
-- 360：mask と add の分配（点ごとの ↔）
-- (R∨S)∧M ↔ (R∧M) ∨ (S∧M)
theorem theorem360 (R S M : Rel α β) :
    ∀ a b,
      relMul (relAdd R S) M a b ↔ relAdd (relMul R M) (relMul S M) a b := by
  dsimp [relMul, relAdd]
  dsimp [Rel] at R S M
  intro a b
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro c
  obtain ⟨c1 | c2, c3⟩ := c

  -- hLeft.inl
  left
  exact ⟨c1, c3⟩

  -- hLeft.inr
  right
  exact ⟨c2, c3⟩

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

--------------------------------------------------------------------------------
-- 361〜365：関数をグラフ関係として見たときの単射・全射
--------------------------------------------------------------------------------

def relGraph (f : α → β) : Rel α β := fun a b => f a = b

-- 361：常に成り立つ：id ⊆ graph ; graphᵀ（反射性）
-- ヒント：a=a を仮定して witness を f a にする
theorem theorem361 (f : α → β) :
    RelLe (relId α) (relComp (relGraph f) (relTrans (relGraph f))) := by
  dsimp [RelLe, relId, relComp, relGraph, relTrans]
  intro a b c
  refine ⟨?d, ?e, ?f⟩

  -- d
  apply f
  exact a

  -- e
  rfl

  -- f
  rw [c]

-- 362：単射 ↔ graph ; graphᵀ ⊆ id
-- ヒント：
--   (→) ∃b, f a=b ∧ f a'=b から f a = f a' を作って injective で落とす
--   (←) f a = f a' から witness b := f a で合成を作って ⊆id で落とす
theorem theorem362 (f : α → β) :
    _root_.Function.Injective f ↔
      RelLe (relComp (relGraph f) (relTrans (relGraph f))) (relId α) := by
  dsimp [RelLe, relComp, relGraph, relTrans, relId,Function.Injective]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a b c d
  apply a
  obtain ⟨d1, d2, d3⟩ := d
  rw [d2, d3]

  -- hRight
  intro g h i j
  apply g
  exists (f h)
  rw [j]
  constructor
  -- left
  rfl
  -- right
  rfl

-- 363：常に成り立つ：graphᵀ ; graph ⊆ id（同じ x から出たら同じ y）
theorem theorem363 (f : α → β) :
    RelLe (relComp (relTrans (relGraph f)) (relGraph f)) (relId β) := by
  dsimp [RelLe, relComp, relTrans, relGraph, relId]
  intro a b c
  obtain ⟨c1, c2, c3⟩ := c
  rw [←c2, ←c3]

-- 364：全射 ↔ id ⊆ graphᵀ ; graph
-- ヒント：
--   (→) y を任意に、全射で x を取って witness にする
--   (←) id y y を ⊆ に流して witness x を回収する
theorem theorem364 (f : α → β) :
    _root_.Function.Surjective f ↔
      RelLe (relId β) (relComp (relTrans (relGraph f)) (relGraph f)) := by
  dsimp [RelLe, relComp, relTrans, relId, relGraph, Function.Surjective]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a c d e
  obtain ⟨a1, a2⟩ := a c
  refine ⟨a1, a2, ?_⟩
  rw [←e]
  exact a2

  -- hRight
  intro g h
  have i : ∃ b_1, f b_1 = h ∧ f b_1 = h := by
    apply g
    rfl
  obtain ⟨i1, i2, i3⟩ := i
  exact ⟨i1, i2⟩

-- 365：全単射 ↔ 「両側が id になる」（関係的な“逆行列”）
-- ※ Function.Bijective f は Injective ∧ Surjective

-- Mathlib なし環境では Function.Bijective が無いことがあるので自作する
def Bijective (f : α → β) : Prop :=
  _root_.Function.Injective f ∧ _root_.Function.Surjective f

theorem theorem365 (f : α → β) :
    Bijective f ↔
      (relComp (relGraph f) (relTrans (relGraph f)) = relId α) ∧
      (relComp (relTrans (relGraph f)) (relGraph f) = relId β) := by
  dsimp [Bijective, Function.Injective, Function.Surjective]
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  obtain ⟨a1, a2⟩ := a
  constructor

  -- hLeft.left
  funext x y
  dsimp [relComp , relGraph, relTrans, relId]
  have h : f x = f y → x = y := by
    apply a1
  apply propext
  refine ⟨?bLeft, ?bRight⟩

  -- bLeft
  intro i
  apply h
  obtain ⟨i1, i2, i3⟩ := i
  rw [i2, i3]

  -- bRight
  intro j
  exists (f x)
  constructor

  -- bRight.left
  rfl

  -- bRight.right
  rw [j]

  -- hLeft.right
  funext x y
  apply propext
  dsimp [relComp , relGraph, relTrans, relId]
  --  apply a2
  refine ⟨?cLeft, ?cRight⟩

  -- cLeft
  intro l
  obtain ⟨l1, l2, l3⟩ := l
  rw [←l2, ←l3]

  -- cRight
  intro m
  have n : ∃ a, f a = x := by
    apply a2
  obtain ⟨n1, n2⟩ := n
  exists n1
  constructor
  -- cRight.left
  exact n2
  -- cRight.right
  rw [←m]
  exact n2

  -- hRight
  intro b
  obtain ⟨b1, b2⟩ := b
  refine ⟨?d, ?e⟩

  -- d
  intro g h i
  have hb1xy := congrFun (congrFun b1 g) h
  dsimp [relComp, relGraph, relTrans, relId] at hb1xy
  rw [←hb1xy]
  exists (f g)
  constructor
  -- d.left
  rfl
  -- d.right
  rw [i]

  -- e
  intro j
  have hb2y := congrFun (congrFun b2 j) j
  dsimp [relComp, relGraph, relTrans, relId] at hb2y
  have n : ∃ b, f b = j := by
    have n1 : j = j := by rfl
    rw [←hb2y] at n1
    obtain ⟨n2, n3, n4⟩ := n1
    exists n2
  obtain ⟨n5, n6⟩ := n
  exists n5

--------------------------------------------------------------------------------
-- 366〜370：閉包（Kleene star の入口：反復合成）
--------------------------------------------------------------------------------

def relPow (R : Rel α α) : Nat → Rel α α
  | 0       => relId α
  | Nat.succ n => relComp (relPow R n) R

def relStar (R : Rel α α) : Rel α α :=
  fun a b => ∃ n, relPow R n a b

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- 366：relPow は関係に関して単調（R ⊆ S なら pow R n ⊆ pow S n）
-- ヒント：induction n with | zero => ... | succ n ih => ...
theorem theorem366 (R S : Rel α α) :
  RelLe R S → ∀ n, RelLe (relPow R n) (relPow S n) := by
  -- intro a b c d eとはやらないのが重要
  intro a b
  dsimp [Rel] at R S
  dsimp [RelLe] at a
  dsimp [RelLe]
  induction b with
  | zero =>
    dsimp [relPow, relId]
    intro c d e
    exact e
  | succ n ih =>
    dsimp [RelLe, relPow, relComp]
    intro c d e
    obtain ⟨e1, e2, e3⟩ := e
    refine ⟨e1, ?g, ?h⟩
    -- g
    apply ih
    exact e2
    -- h
    apply a
    exact e3

-- ☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- 367：反復の連結（経路の連結）：pow m ; pow n ⊆ pow (m+n)
-- ヒント：induction n
--   n=0: 右単位元（308 相当）で
--   succ: 306 で括弧を動かして ih を使う（最後に Nat.add_succ ）
theorem theorem367 (R : Rel α α) :
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

-- 368：star は reflexive：id ⊆ star
-- ヒント：n := 0 を witness に
theorem theorem368 (R : Rel α α) : RelLe (relId α) (relStar R) := by
  dsimp [RelLe, relId, relStar, relPow]
  intro a b c
  refine ⟨?d, ?e⟩
  -- d
  exact 0
  -- e
  dsimp [relPow, relId]
  exact c

-- 369：star は transitive：star ; star ⊆ star
-- ヒント：
--   obtain ⟨m, hm⟩ := ...
--   obtain ⟨n, hn⟩ := ...
--   witness は m+n、367 を使う
theorem theorem369 (R : Rel α α) :
    RelLe (relComp (relStar R) (relStar R)) (relStar R) := by
  dsimp [RelLe, relComp, relStar]
  intro a b c
  obtain ⟨c1, ⟨c2, c3⟩⟩ := c
  obtain ⟨c4, c5⟩ := c2
  obtain ⟨c6, c7⟩ := c3
  exists (c4 + c6)
  apply theorem367 R c4 c6
  dsimp [relComp]
  exists c1

-- 370：star は単調（R ⊆ S なら star R ⊆ star S）
-- ヒント：
--   obtain ⟨n, hn⟩ := hstar
--   exact ⟨n, (366 hRS n _ _ hn)⟩
theorem theorem370 (R S : Rel α α) :
    RelLe R S → RelLe (relStar R) (relStar S) := by

  intro a b c d
  obtain ⟨d1, d2⟩ := d
  exists d1

  apply theorem366 R S a d1
  exact d2


--------------------------------------------------------------------------------
-- 演習問題 371〜390（残余 / 像・逆像 / スター閉包：実践寄せ）
-- ※ import Mathlib なし
-- ※ 351〜370 の定義がある前提：
--   Rel, relComp, relAdd, relMul, RelLe, rRes, lRes, relTrans, relId,
--   relGraph, relPow, relStar
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 371：右残余は「左引数の +（∨）」を ∧ に変える（分配）★★★★☆
-- rRes (S + S') T = (rRes S T) ∧ (rRes S' T)
--
-- ヒント：
--   funext b a; apply propext
--   目標は
--     (∀ c, (S a c ∨ S' a c) → T b c) ↔
--     ( (∀ c, S a c → T b c) ∧ (∀ c, S' a c → T b c) )
theorem ex371 (S S' : Rel α γ) (T : Rel β γ) :
    rRes (relAdd S S') T = relMul (rRes S T) (rRes S' T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 372：右残余は「右引数の ∧」に分配する ★★★★☆
-- rRes S (T ∧ T') = (rRes S T) ∧ (rRes S T')
--
-- ヒント： (A → (B ∧ C)) ↔ (A→B) ∧ (A→C)
theorem ex372 (S : Rel α γ) (T T' : Rel β γ) :
    rRes S (relMul T T') = relMul (rRes S T) (rRes S T') := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 373：左残余も「左引数の +」を ∧ に変える ★★★★☆
theorem ex373 (R R' : Rel α β) (T : Rel α γ) :
    lRes (relAdd R R') T = relMul (lRes R T) (lRes R' T) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 374：左残余も「右引数の ∧」に分配する ★★★★☆
theorem ex374 (R : Rel α β) (T T' : Rel α γ) :
    lRes R (relMul T T') = relMul (lRes R T) (lRes R T') := by
  -- TODO
  sorry


--------------------------------------------------------------------------------
-- 像/逆像（到達集合）＝ “関係を集合に作用させる”
--------------------------------------------------------------------------------

def Pred (X : Type) := X → Prop

def relImg (R : Rel α β) (A : Pred α) : Pred β :=
  fun b => ∃ a, A a ∧ R a b

def relPre (R : Rel α β) (B : Pred β) : Pred α :=
  fun a => ∃ b, R a b ∧ B b

--------------------------------------------------------------------------------
-- 375：像は合成に関して結合的（到達集合の実用形）★★★★★
-- Img (R;S) A = Img S (Img R A)
--
-- ヒント：funext c; apply propext; constructor <;> intro h; ...
theorem ex375 (R : Rel α β) (S : Rel β γ) (A : Pred α) :
    relImg (relComp R S) A = relImg S (relImg R A) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 376：逆像も合成に関して結合的 ★★★★★
-- Pre (R;S) C = Pre R (Pre S C)
theorem ex376 (R : Rel α β) (S : Rel β γ) (C : Pred γ) :
    relPre (relComp R S) C = relPre R (relPre S C) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 377：関数 f をグラフ関係にしたとき、逆像は普通の合成になる ★★★★☆
-- Pre (graph f) B = fun a => B (f a)
--
-- ヒント：
--   funext a; apply propext
--   (→) obtain ⟨b, hb, hB⟩ := ...
--       -- hb : f a = b なので rw で潰せる
--   (←) witness は b := f a
theorem ex377 (f : α → β) (B : Pred β) :
    relPre (relGraph f) B = (fun a => B (f a)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 378：関数合成のグラフは、グラフ関係の合成に一致 ★★★★☆
-- graph (g∘f) = graph f ; graph g
--
-- ヒント：funext a c; apply propext; constructor <;> intro h
theorem ex378 (f : α → β) (g : β → γ) :
    relGraph (fun x => g (f x)) = relComp (relGraph f) (relGraph g) := by
  -- TODO
  sorry


--------------------------------------------------------------------------------
-- pow / star（反復合成＝到達可能性）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 379：pow 1 は R 自身（点ごと ↔）★★★★☆
-- relPow R (Nat.succ 0) a b ↔ R a b
--
-- ヒント：
--   relPow (succ 0) = relComp (relPow 0) R = relComp (relId) R
--   307/308 相当の “単位元” 展開を自前でやる感じ
theorem ex379 (R : Rel α α) :
    ∀ a b, relPow R (Nat.succ 0) a b ↔ R a b := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 380：R ⊆ star R（1ステップ到達は到達）★★★★☆
-- ヒント：n := 1（= succ 0）を witness にして 379 を使う
theorem ex380 (R : Rel α α) :
    RelLe R (relStar R) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 381：star は “合成で冪等”（star;star = star）★★★★★
-- ヒント：
--   (⊆) は 369 を使う（既に証明済なら）
--   (⊇) は star の reflexive性（368）を使って witness を b にする
theorem ex381 (R : Rel α α) :
    relComp (relStar R) (relStar R) = relStar R := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 382：star は “演算として冪等”（star(star R) = star R）★★★★★
-- ここまでくると “閉包演算子” の感じが出ます
--
-- ヒント（方針）：
--   1) relStar R ⊆ relStar (relStar R) は 380 + 370（単調性）で
--   2) relStar (relStar R) ⊆ relStar R は
--      「relStar R が reflexive & transitive」であることから
--      pow (star R) n ⊆ star R を帰納法で示して star を潰す
theorem ex382 (R : Rel α α) :
    relStar (relStar R) = relStar R := by
  -- TODO
  sorry


--------------------------------------------------------------------------------
-- transpose と pow / star（“逆向き到達”）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 383：transpose は合成の順序を逆にする（等式版）★★★★☆
-- relTrans (R;S) = Sᵀ ; Rᵀ
--
-- ヒント：funext c a; apply propext; constructor <;> intro h; ...
theorem ex383 (R : Rel α β) (S : Rel β γ) :
    relTrans (relComp R S) = relComp (relTrans S) (relTrans R) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 384：transpose は pow に分配する（n回到達を逆向きに）★★★★★
-- relTrans (pow R n) = pow (Rᵀ) n
--
-- ヒント：induction n with | zero => ... | succ n ih => ...
--   succ で 383 と ih を使う
theorem ex384 (R : Rel α α) :
    ∀ n, relTrans (relPow R n) = relPow (relTrans R) n := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 385：transpose は star にも分配する（到達可能性の逆）★★★★★
-- (star R)ᵀ = star (Rᵀ)
--
-- ヒント：
--   funext a b; apply propext
--   (→) obtain ⟨n, hn⟩ := ...
--       exact ⟨n, ?_⟩ で 384 を使って書き換え
theorem ex385 (R : Rel α α) :
    relTrans (relStar R) = relStar (relTrans R) := by
  -- TODO
  sorry


--------------------------------------------------------------------------------
-- star の「実用補題」（到達を1歩伸ばす）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 386：star ; R ⊆ star（到達してから1歩進んでも到達）★★★★★
-- ヒント：R ⊆ star（380）と、star の推移性（369）を組み合わせる
theorem ex386 (R : Rel α α) :
    RelLe (relComp (relStar R) R) (relStar R) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 387：R ; star ⊆ star（最初に1歩進んでから到達しても到達）★★★★★
theorem ex387 (R : Rel α α) :
    RelLe (relComp R (relStar R)) (relStar R) := by
  -- TODO
  sorry


--------------------------------------------------------------------------------
-- star の本質：最小の reflexive-transitive 閉包
--------------------------------------------------------------------------------

def Reflexive (X : Rel α α) : Prop := RelLe (relId α) X
def Transitive (X : Rel α α) : Prop := RelLe (relComp X X) X

--------------------------------------------------------------------------------
-- 388：star の “最小性”（閉包としての実用定理）★★★★★
-- X が reflexive & transitive で、さらに R ⊆ X なら star R ⊆ X
--
-- ヒント：
--   dsimp [RelLe, relStar] ; intro a b ⟨n, hn⟩
--   n で帰納法：0 は reflexive、succ は transitive を使う
theorem ex388 (R X : Rel α α) :
    Reflexive X → Transitive X → RelLe R X → RelLe (relStar R) X := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 389：上の最小性からの即コロラリ：X が閉包なら star R ⊆ X ↔ R ⊆ X ★★★★★
-- （テンソル論理の「閉包＝自由な推移閉包」感を掴む問題）
--
-- ヒント：
--   (→) は 380（R ⊆ star R）と推移で
--   (←) は 388 を使う
theorem ex389 (R X : Rel α α) :
    Reflexive X → Transitive X → (RelLe (relStar R) X ↔ RelLe R X) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 390：実用：star R が reflexive & transitive であることを “最小性” から回収 ★★★★★
-- Reflexive (star R) ∧ Transitive (star R)
--
-- ヒント：
--   Reflexive は 368 相当：n:=0
--   Transitive は 369 相当：pow の連結（367）を使う
theorem ex390 (R : Rel α α) :
    Reflexive (relStar R) ∧ Transitive (relStar R) := by
  -- TODO
  sorry


end TL
