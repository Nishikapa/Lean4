--------------------------------------------------------------------------------
-- Basic_501.lean
-- 演習問題 501〜550（Weighted Rel / list-sum / masking / attention）
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 401〜450 は Basic_451 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_451

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) Weighted Relation（Nat 値の関係）
--------------------------------------------------------------------------------

def WRel (α β : Type) := α → β → Nat

def wZero (α β : Type) : WRel α β := fun _ _ => 0

def wAdd {α β : Type} (R S : WRel α β) : WRel α β :=
  fun a b => R a b + S a b

-- pointwise ≤
def WLe {α β : Type} (R S : WRel α β) : Prop :=
  ∀ a b, R a b ≤ S a b

--------------------------------------------------------------------------------
-- 1) List 上の有限和
--------------------------------------------------------------------------------

def wsum {X : Type} : List X → (X → Nat) → Nat
  | [],     _ => 0
  | x :: xs, f => f x + wsum xs f

--------------------------------------------------------------------------------
-- 2) keys（中間インデックスの有限リスト）での “合成”（縮約）
--------------------------------------------------------------------------------

-- (R : α→β→Nat) と (S : β→γ→Nat) を keys : List β で縮約して α→γ→Nat を作る
def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  fun a c => wsum keys (fun b => R a b * S b c)

--------------------------------------------------------------------------------
-- 3) mask（Prop を 0/1 にする）
-- ※ if を使うので Decidable が必要
-- ※ M : Rel α β は一般には Decidable でないため classical を使う
-- ※ classical は noncomputable なので def も noncomputable にする
--------------------------------------------------------------------------------

noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  classical
  exact fun a b => if M a b then 1 else 0

noncomputable def wMask {α β : Type} (R : WRel α β) (M : Rel α β) : WRel α β :=
  fun a b => R a b * maskW M a b

--------------------------------------------------------------------------------
-- 4) score / attention（Nat）
--------------------------------------------------------------------------------

noncomputable def maskScore (M : Rel α β) (score : α → β → Nat) : α → β → Nat := by
  classical
  exact fun a b => score a b * (if M a b then 1 else 0)

-- keys を走査して Σ_b score(a,b) * val(b)
def attnNat (keys : List β) (score : α → β → Nat) (val : β → Nat) : α → Nat :=
  fun a => wsum keys (fun b => score a b * val b)

--------------------------------------------------------------------------------
-- 501〜550：演習（解答は書かない）
--------------------------------------------------------------------------------

-- 501：wsum [] = 0
theorem ex501 {X : Type} (f : X → Nat) :
    wsum ([] : List X) f = 0 := by
  dsimp [wsum]

-- 502：wsum (x::xs) = f x + wsum xs
theorem ex502 {X : Type} (x : X) (xs : List X) (f : X → Nat) :
    wsum (x :: xs) f = f x + wsum xs f := by
  dsimp [wsum]

-- 503：wsum の単調性（点ごと ≤ なら和も ≤）
theorem ex503 {X : Type} (xs : List X) (f g : X → Nat) :
    (∀ x, f x ≤ g x) → wsum xs f ≤ wsum xs g := by

  intro h1
  induction xs with
  | nil =>
    dsimp [wsum]
    apply Nat.zero_le
  | cons x xs ih =>
    dsimp [wsum]
    apply Nat.add_le_add
    apply h1
    apply ih

-- 504：空 keys の合成はゼロ
theorem ex504 (R : WRel α β) (S : WRel β γ) :
    wCompList ([] : List β) R S = wZero α γ := by

  funext a1 g1
  dsimp [wCompList]
  dsimp [wZero]
  dsimp [wsum]

-- 505：keys = [b] のとき 1 項だけ
theorem ex505 (b : β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c, wCompList [b] R S a c = R a b * S b c := by

  intro a1 g1
  dsimp [wCompList]
  dsimp [wsum]

-- 506：wAdd の点ごとの形
theorem ex506 (R S : WRel α β) :
    ∀ a b, wAdd R S a b = R a b + S a b := by

  intro a1 b1
  dsimp [wAdd]

-- 507：wAdd の可換
theorem ex507 (R S : WRel α β) :
    wAdd R S = wAdd S R := by

  funext a1 b1
  apply Nat.add_comm

-- 508：wAdd の結合
theorem ex508 (R S T : WRel α β) :
    wAdd (wAdd R S) T = wAdd R (wAdd S T) := by

  funext a1 b1
  dsimp [wAdd]
  apply Nat.add_assoc

-- 509：0 + R = R
theorem ex509 (R : WRel α β) :
    wAdd (wZero α β) R = R := by

  funext a1 b1
  dsimp [wAdd]
  dsimp [wZero]
  apply Nat.zero_add

-- 510：R + 0 = R
theorem ex510 (R : WRel α β) :
    wAdd R (wZero α β) = R := by

  funext a1 b1
  dsimp [wAdd]
  dsimp [wZero]

-- 511：左線形性（(R+S);T = R;T + S;T）
theorem ex511 (keys : List β) (R S : WRel α β) (T : WRel β γ) :
    wCompList keys (wAdd R S) T
      = wAdd (wCompList keys R T) (wCompList keys S T) := by

  funext a1 g1
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wCompList] at ih
    dsimp [wAdd] at ih
    dsimp [wCompList]
    dsimp [wsum]
    dsimp [wAdd]
    rw [ih]
    dsimp [wCompList]
    dsimp [wsum]
    rw [Nat.right_distrib (R a1 b) (S a1 b) (T b g1)]
    rw [←Nat.add_assoc]
    rw [←Nat.add_assoc]
    rw [Nat.add_assoc (R a1 b * T b g1) (S a1 b * T b g1) (wsum keys fun b => R a1 b * T b g1)]
    rw [Nat.add_comm (S a1 b * T b g1) (wsum keys fun b => R a1 b * T b g1)]
    rw [←Nat.add_assoc]

-- 512：右線形性（R;(S+T) = R;S + R;T）
theorem ex512 (keys : List β) (R : WRel α β) (S T : WRel β γ) :
    wCompList keys R (wAdd S T)
      = wAdd (wCompList keys R S) (wCompList keys R T) := by
  funext a1 g1
  dsimp [wAdd]
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wCompList] at ih
    dsimp [wAdd] at ih
    dsimp [wCompList]
    dsimp [wsum]
    dsimp [wAdd]
    rw [ih]
    rw [Nat.left_distrib]
    rw [←Nat.add_assoc]
    rw [←Nat.add_assoc]
    rw [Nat.add_assoc (R a1 b * S b g1) (R a1 b * T b g1) (wsum keys fun b => R a1 b * S b g1)]
    rw [Nat.add_comm (R a1 b * T b g1) (wsum keys fun b => R a1 b * S b g1)]
    rw [←Nat.add_assoc]

-- 513：0 ≤ wCompList ...
theorem ex513 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c, 0 ≤ wCompList keys R S a c := by

  intro a1 g1
  apply Nat.zero_le

-- 514：maskW は 0 か 1
theorem ex514 (M : Rel α β) :
    ∀ a b, maskW M a b = 0 ∨ maskW M a b = 1 := by
  -- ヒント：by classical; by_cases h : M a b; simp [maskW, h]
  intro a1 b1
  classical
  dsimp [maskW]
  by_cases h : M a1 b1
  right
  rw [if_pos h]
  left
  rw [if_neg h]

-- 515：wMask の if 展開形
theorem ex515 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b = R a b * maskW M a b := by

  intro a1 b1
  dsimp [wMask]

-- 516：True マスクは恒等
theorem ex516 (R : WRel α β) :
    wMask R (fun _ _ => True) = R := by

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  rw [if_pos (by trivial)]
  rw [Nat.mul_one]

-- 517：False マスクは 0
theorem ex517 (R : WRel α β) :
    wMask R (fun _ _ => False) = wZero α β := by

  funext a1 b1
  dsimp [wMask]
  dsimp [maskW]
  dsimp [wZero]
  rw [if_neg (by trivial)]
  rw [Nat.mul_zero]

-- 518：WLe は pointwise ≤
theorem ex518 (R S : WRel α β) :
    WLe R S ↔ (∀ a b, R a b ≤ S a b) := by

  refine ⟨?hLeft, ?hRight⟩

  -- fLeft
  dsimp [WLe]
  intro h1 a1 b1
  apply h1

  -- fRight
  dsimp [WLe]
  intro h2 a1 b1
  apply h2

-- 519：wAdd の単調性（左）
theorem ex519 (R R' S : WRel α β) :
    WLe R R' → WLe (wAdd R S) (wAdd R' S) := by

  intro h1 a1 b1
  apply Nat.add_le_add_right
  apply h1

-- 520：wCompList の単調性（左）
theorem ex520 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    WLe R R' → WLe (wCompList keys R S) (wCompList keys R' S) := by

  intro h1 a1 g1
  -- theorem ex503 {X : Type} (xs : List X) (f g : X → Nat) :
  --     (∀ x, f x ≤ g x) → wsum xs f ≤ wsum xs g
  apply ex503
  intro b1
  apply Nat.mul_le_mul_right
  apply h1

-- 521：wCompList の単調性（右）
theorem ex521 (keys : List β) (R : WRel α β) (S S' : WRel β γ) :
    WLe S S' → WLe (wCompList keys R S) (wCompList keys R S') := by

  intro h1 a1 g1
  apply ex503
  intro b1
  apply Nat.mul_le_mul_left
  apply h1

-- 522：右 0（R ; 0 = 0）
theorem ex522 (keys : List β) (R : WRel α β) :
    wCompList keys R (wZero β γ) = wZero α γ := by

  funext a1 g1
  dsimp [wCompList, wZero]
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

-- 523：左 0（0 ; R = 0）
-- ★修正点：R の型は WRel β γ（中間の型が β なので）
theorem ex523 (keys : List β) (R : WRel β γ) :
    wCompList keys (wZero α β) R = wZero α γ := by

  -- def wCompList {α β γ : Type} (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => wsum keys (fun b => R a b * S b c)

  -- def wZero (α β : Type) : WRel α β := fun _ _ => 0

  funext a1 g1
  dsimp [wCompList, wZero]
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    exact ih

-- 524：マスクすると値は増えない（≤）
-- ★Decidable(M a b) は maskW 側で classical を使っているので定義は通る
theorem ex524 (R : WRel α β) (M : Rel α β) :
    WLe (wMask R M) R := by
  -- ヒント：by classical; by_cases h : M a b; simp [wMask, maskW, h]

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  -- noncomputable def wMask {α β : Type} (R : WRel α β) (M : Rel α β) : WRel α β :=
  --   fun a b => R a b * maskW M a b

  -- def WLe {α β : Type} (R S : WRel α β) : Prop :=
  --   ∀ a b, R a b ≤ S a b

  intro a1 b1
  classical
  dsimp [wMask]
  dsimp [maskW]
  by_cases h : M a1 b1

  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  apply Nat.le_refl

  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  apply Nat.zero_le

-- 525：wMask は点ごとに 0 か元の値
theorem ex525 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b = 0 ∨ wMask R M a b = R a b := by

  intro a1 b1
  classical
  dsimp [wMask]
  dsimp [maskW]
  by_cases h : M a1 b1

  -- pos
  right
  rw [if_pos h]
  rw [Nat.mul_one]

  -- neg
  left
  rw [if_neg h]
  rw [Nat.mul_zero]

-- 526：maskScore は score を超えない
theorem ex526 (M : Rel α β) (score : α → β → Nat) :
    ∀ a b, maskScore M score a b ≤ score a b := by

  -- noncomputable def maskScore (M : Rel α β) (score : α → β → Nat) : α → β → Nat := by
  --   classical
  --   exact fun a b => score a b * (if M a b then 1 else 0)

  intro a1 b1
  classical
  dsimp [maskScore]
  by_cases h : M a1 b1

  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  apply Nat.le_refl

  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  apply Nat.zero_le

-- 527：attnNat の単調性（score）
theorem ex527 (keys : List β) (score score' : α → β → Nat) (val : β → Nat) :
    (∀ a b, score a b ≤ score' a b) →
    ∀ a, attnNat keys score val a ≤ attnNat keys score' val a := by

  -- def attnNat (keys : List β) (score : α → β → Nat) (val : β → Nat) : α → Nat :=
  --   fun a => wsum keys (fun b => score a b * val b)

  intro h1 a1
  dsimp [attnNat]

  -- theorem ex503 {X : Type} (xs : List X) (f g : X → Nat) :
  --     (∀ x, f x ≤ g x) → wsum xs f ≤ wsum xs g := by

  apply ex503
  intro b1
  apply Nat.mul_le_mul_right
  apply h1

-- 528：空 keys の attnNat は 0
theorem ex528 (score : α → β → Nat) (val : β → Nat) :
    ∀ a, attnNat ([] : List β) score val a = 0 := by

  intro a1
  dsimp [attnNat]
  dsimp [wsum]

-- 529：attnNat の単調性（val）
theorem ex529 (keys : List β) (score : α → β → Nat) (val val' : β → Nat) :
    (∀ b, val b ≤ val' b) →
    ∀ a, attnNat keys score val a ≤ attnNat keys score val' a := by

  intro h1 a1
  dsimp [attnNat]
  apply ex503
  intro b1
  apply Nat.mul_le_mul_left
  apply h1

-- 530：マスクすると attention 出力は増えない
-- ★Decidable(M a b) は maskScore 側で classical を使っているので定義は通る
theorem ex530 (keys : List β) (M : Rel α β) (score : α → β → Nat) (val : β → Nat) :
    ∀ a, attnNat keys (maskScore M score) val a ≤ attnNat keys score val a := by

  intro a1
  dsimp [attnNat]
  apply ex503
  intro b1
  apply Nat.mul_le_mul_right
  apply ex526

--------------------------------------------------------------------------------
-- 5) WRel 版 attention（縮約としての view）
--------------------------------------------------------------------------------

def attnWRel {α β γ : Type} (keys : List β) (QK : WRel α β) (KV : WRel β γ) : WRel α γ :=
  wCompList keys QK KV

-- 531：attnWRel は wCompList の別名
theorem ex531 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    attnWRel keys QK KV = wCompList keys QK KV := by
  rfl

-- 532：attnWRel の左 0
theorem ex532 (keys : List β) (KV : WRel β γ) :
    attnWRel keys (wZero α β) KV = wZero α γ := by

  funext a1 g1
  dsimp [attnWRel]
  dsimp [wCompList]
  dsimp [wZero]
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wsum]
    rw [Nat.zero_mul]
    rw [Nat.zero_add]
    exact ih

-- 533：wMask の点ごとの ≤ 形
theorem ex533 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b ≤ R a b := by
  intro a1 b1
  dsimp [wMask]
  dsimp [maskW]
  classical
  by_cases h : M a1 b1

  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  apply Nat.le_refl

  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  apply Nat.zero_le

-- 534：maskScore の点ごとの ≤ 形
theorem ex534 (M : Rel α β) (score : α → β → Nat) :
    ∀ a b, maskScore M score a b ≤ score a b := by

  intro a1 b1
  dsimp [maskScore]
  classical
  by_cases h : M a1 b1
  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  apply Nat.le_refl
  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  apply Nat.zero_le

-- 535：score が全部 0 なら attnNat も 0
theorem ex535 (keys : List β) (val : β → Nat) :
    ∀ a : α, attnNat keys (fun _ _ => 0) val a = 0 := by

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
-- 536〜550：テンソルっぽい法則（分配 / 結合 / 二重和）
--------------------------------------------------------------------------------

-- 536：wsum は append に分配
theorem ex536 {X : Type} (xs ys : List X) (f : X → Nat) :
    wsum (xs ++ ys) f = wsum xs f + wsum ys f := by

  induction xs with
  | nil =>
    dsimp [wsum]
    rw [Nat.zero_add]
  | cons x xs ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_assoc]

-- 537：wsum は点ごとの加法に分配
theorem ex537 {X : Type} (xs : List X) (f g : X → Nat) :
    wsum xs (fun x => f x + g x) = wsum xs f + wsum xs g := by

  induction xs with
  | nil =>
    dsimp [wsum]
  | cons x xs ih =>
    dsimp [wsum]
    rw [ih]
    rw [←Nat.add_assoc (f x + wsum xs f) (g x) (wsum xs g)]
    rw [Nat.add_assoc (f x) (wsum xs f) (g x)]
    rw [Nat.add_comm (wsum xs f) (g x)]
    rw [Nat.add_assoc (f x) (g x + wsum xs f) (wsum xs g)]
    rw [Nat.add_assoc (g x) (wsum xs f) (wsum xs g)]
    rw [←Nat.add_assoc (f x) (g x)  (wsum xs f + wsum xs g)]

-- 538：(Σ f) * t = Σ (f*t)
theorem ex538 {X : Type} (xs : List X) (f : X → Nat) (t : Nat) :
    wsum xs f * t = wsum xs (fun x => f x * t) := by

  induction xs with
  | nil =>
    dsimp [wsum]
    rw [Nat.zero_mul]
  | cons x xs ih =>
    dsimp [wsum]
    rw [←ih]
    rw [Nat.add_mul]

-- 539：t * (Σ f) = Σ (t*f)
theorem ex539 {X : Type} (xs : List X) (f : X → Nat) (t : Nat) :
    t * wsum xs f = wsum xs (fun x => t * f x) := by
  induction xs with
  | nil =>
    dsimp [wsum]
  | cons x xs ih =>
    dsimp [wsum]
    rw [←ih]
    rw [Nat.mul_add]

-- 540：wCompList は keys の append に分配（合計を 2 ブロックに分割）
theorem ex540 (keys1 keys2 : List β) (R : WRel α β) (S : WRel β γ) :
    wCompList (keys1 ++ keys2) R S
      = wAdd (wCompList keys1 R S) (wCompList keys2 R S) := by

  funext a1 g1
  -- theorem ex536 {X : Type} (xs ys : List X) (f : X → Nat) :
  --     wsum (xs ++ ys) f = wsum xs f + wsum ys f
  apply ex536


-- 541：wCompList の結合（有限二重和の入れ替えが本体）
theorem ex541 (keysβ : List β) (keysγ : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wCompList keysγ (wCompList keysβ R S) T
      = wCompList keysβ R (wCompList keysγ S T) := by

  funext a1 s1
  dsimp [wCompList]

  induction keysβ with
  | nil =>
    dsimp [wsum]
    induction keysγ with
    | nil =>
      dsimp [wsum]
    | cons g1 keysγ ihγ =>
      dsimp [wsum]
      rw [Nat.zero_mul]
      rw [Nat.zero_add]
      exact ihγ

  | cons b1 keysβ ihβ =>

    dsimp [wsum]
    rw [←ihβ]

    rw [ex539]
    rw [←ex537]

    conv =>
      rhs
      arg 2
      intro xor
      rw [←Nat.mul_assoc]
      rw [←Nat.add_mul]

-- 542：AND マスクは 0/1 の積になる
theorem ex542 (M1 M2 : Rel α β) :
    maskW (fun a b => M1 a b ∧ M2 a b)
      = (fun a b => maskW M1 a b * maskW M2 a b) := by

  funext a1 b1
  dsimp [maskW]
  classical
  by_cases h1 : M1 a1 b1
  by_cases h2 : M2 a1 b1
  -- both true
  rw [if_pos h1]
  rw [if_pos h2]
  rw [Nat.mul_one]
  have h3: M1 a1 b1 ∧ M2 a1 b1 := by
    constructor
    exact h1
    exact h2
  rw [if_pos h3]
  rw [if_neg h2]
  have h4: ¬ (M1 a1 b1 ∧ M2 a1 b1) := by
    intro h
    obtain ⟨h4_1, h4_2⟩ := h
    apply h2
    exact h4_2
  rw [if_neg h4]
  rw [Nat.mul_zero]
  have h5 : ¬ (M1 a1 b1 ∧ M2 a1 b1) := by
    intro h
    obtain ⟨h5_1, h5_2⟩ := h
    apply h1
    exact h5_1
  rw [if_neg h5]
  rw [if_neg h1]
  rw [Nat.zero_mul]

-- 543：二重マスク = AND マスク
theorem ex543 (R : WRel α β) (M1 M2 : Rel α β) :
    wMask (wMask R M1) M2 = wMask R (fun a b => M1 a b ∧ M2 a b) := by

  funext a1 b1
  dsimp [wMask]

-- theorem ex542 (M1 M2 : Rel α β) :
--     maskW (fun a b => M1 a b ∧ M2 a b)
--       = (fun a b => maskW M1 a b * maskW M2 a b)

  rw [ex542]
  dsimp
  rw [Nat.mul_assoc]

-- 544：WLe の refl
theorem ex544 (R : WRel α β) :
    WLe R R := by

  intro a b
  apply Nat.le_refl

-- 545：WLe の trans
theorem ex545 (R S T : WRel α β) :
    WLe R S → WLe S T → WLe R T := by
  intro h1 h2 a1 b1
  dsimp [WLe] at h1 h2
  have h3 : ∀ a b, R a b ≤ T a b := by
    intro a1 b1
    obtain h1_ := h1 a1 b1
    obtain h2_ := h2 a1 b1
    apply Nat.le_trans h1_ h2_
  apply h3

-- 546：wAdd は両側単調
theorem ex546 (R R' S S' : WRel α β) :
    WLe R R' → WLe S S' → WLe (wAdd R S) (wAdd R' S') := by

  intro h1 h2 a1 b1
  apply Nat.add_le_add (h1 a1 b1) (h2 a1 b1)

-- 547：wMask は R に単調
theorem ex547 (R R' : WRel α β) (M : Rel α β) :
    WLe R R' → WLe (wMask R M) (wMask R' M) := by

  intro h1 a1 b1
  dsimp [wMask]
  dsimp [maskW]
  dsimp [WLe] at h1
  by_cases h : M a1 b1
  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  apply h1

  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  apply Nat.zero_le

-- 548：wCompList は両側単調
theorem ex548 (keys : List β) (R R' : WRel α β) (S S' : WRel β γ) :
    WLe R R' → WLe S S' → WLe (wCompList keys R S) (wCompList keys R' S') := by
  intro h1 h2 a1 g1
  apply ex503
  intro b1
  dsimp [WLe] at h1 h2
  apply Nat.mul_le_mul (h1 a1 b1) (h2 b1 g1)

-- 549：左をマスクすると合成結果も増えない
theorem ex549 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
    WLe (wCompList keys (wMask R M) S) (wCompList keys R S) := by
  intro a1 g1
  apply ex503
  intro b1
  dsimp [wMask]
  dsimp [maskW]
  by_cases h : M a1 b1
  -- pos
  rw [if_pos h]
  rw [Nat.mul_one]
  dsimp [WRel] at R S
  apply Nat.mul_le_mul_right
  apply Nat.le_refl
  -- neg
  rw [if_neg h]
  rw [Nat.mul_zero]
  rw [Nat.zero_mul]
  apply Nat.zero_le

-- 550：True マスクは合成しても変わらない
theorem ex550 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wCompList keys (wMask QK (fun _ _ => True)) KV = wCompList keys QK KV := by

  funext a1 g1
  dsimp [wCompList]
  dsimp [wMask]
  induction keys with
  | nil =>
    rfl
  | cons b keys ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.add_right_cancel_iff]
    rw [maskW]
    rw [if_pos (by trivial)]
    rw [Nat.mul_one]

end TL
