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
  -- TODO
  sorry

-- 502：wsum (x::xs) = f x + wsum xs
theorem ex502 {X : Type} (x : X) (xs : List X) (f : X → Nat) :
    wsum (x :: xs) f = f x + wsum xs f := by
  -- TODO
  sorry

-- 503：wsum の単調性（点ごと ≤ なら和も ≤）
theorem ex503 {X : Type} (xs : List X) (f g : X → Nat) :
    (∀ x, f x ≤ g x) → wsum xs f ≤ wsum xs g := by
  -- TODO
  sorry

-- 504：空 keys の合成はゼロ
theorem ex504 (R : WRel α β) (S : WRel β γ) :
    wCompList ([] : List β) R S = wZero α γ := by
  -- TODO
  sorry

-- 505：keys = [b] のとき 1 項だけ
theorem ex505 (b : β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c, wCompList [b] R S a c = R a b * S b c := by
  -- TODO
  sorry

-- 506：wAdd の点ごとの形
theorem ex506 (R S : WRel α β) :
    ∀ a b, wAdd R S a b = R a b + S a b := by
  -- TODO
  sorry

-- 507：wAdd の可換
theorem ex507 (R S : WRel α β) :
    wAdd R S = wAdd S R := by
  -- TODO
  sorry

-- 508：wAdd の結合
theorem ex508 (R S T : WRel α β) :
    wAdd (wAdd R S) T = wAdd R (wAdd S T) := by
  -- TODO
  sorry

-- 509：0 + R = R
theorem ex509 (R : WRel α β) :
    wAdd (wZero α β) R = R := by
  -- TODO
  sorry

-- 510：R + 0 = R
theorem ex510 (R : WRel α β) :
    wAdd R (wZero α β) = R := by
  -- TODO
  sorry

-- 511：左線形性（(R+S);T = R;T + S;T）
theorem ex511 (keys : List β) (R S : WRel α β) (T : WRel β γ) :
    wCompList keys (wAdd R S) T
      = wAdd (wCompList keys R T) (wCompList keys S T) := by
  -- TODO
  sorry

-- 512：右線形性（R;(S+T) = R;S + R;T）
theorem ex512 (keys : List β) (R : WRel α β) (S T : WRel β γ) :
    wCompList keys R (wAdd S T)
      = wAdd (wCompList keys R S) (wCompList keys R T) := by
  -- TODO
  sorry

-- 513：0 ≤ wCompList ...
theorem ex513 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c, 0 ≤ wCompList keys R S a c := by
  -- TODO
  sorry

-- 514：maskW は 0 か 1
theorem ex514 (M : Rel α β) :
    ∀ a b, maskW M a b = 0 ∨ maskW M a b = 1 := by
  -- ヒント：by classical; by_cases h : M a b; simp [maskW, h]
  -- TODO
  sorry

-- 515：wMask の if 展開形
theorem ex515 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b = R a b * maskW M a b := by
  -- TODO
  sorry

-- 516：True マスクは恒等
theorem ex516 (R : WRel α β) :
    wMask R (fun _ _ => True) = R := by
  -- TODO
  sorry

-- 517：False マスクは 0
theorem ex517 (R : WRel α β) :
    wMask R (fun _ _ => False) = wZero α β := by
  -- TODO
  sorry

-- 518：WLe は pointwise ≤
theorem ex518 (R S : WRel α β) :
    WLe R S ↔ (∀ a b, R a b ≤ S a b) := by
  -- TODO
  sorry

-- 519：wAdd の単調性（左）
theorem ex519 (R R' S : WRel α β) :
    WLe R R' → WLe (wAdd R S) (wAdd R' S) := by
  -- TODO
  sorry

-- 520：wCompList の単調性（左）
theorem ex520 (keys : List β) (R R' : WRel α β) (S : WRel β γ) :
    WLe R R' → WLe (wCompList keys R S) (wCompList keys R' S) := by
  -- TODO
  sorry

-- 521：wCompList の単調性（右）
theorem ex521 (keys : List β) (R : WRel α β) (S S' : WRel β γ) :
    WLe S S' → WLe (wCompList keys R S) (wCompList keys R S') := by
  -- TODO
  sorry

-- 522：右 0（R ; 0 = 0）
theorem ex522 (keys : List β) (R : WRel α β) :
    wCompList keys R (wZero β γ) = wZero α γ := by
  -- TODO
  sorry

-- 523：左 0（0 ; R = 0）
-- ★修正点：R の型は WRel β γ（中間の型が β なので）
theorem ex523 (keys : List β) (R : WRel β γ) :
    wCompList keys (wZero α β) R = wZero α γ := by
  -- TODO
  sorry

-- 524：マスクすると値は増えない（≤）
-- ★Decidable(M a b) は maskW 側で classical を使っているので定義は通る
theorem ex524 (R : WRel α β) (M : Rel α β) :
    WLe (wMask R M) R := by
  -- ヒント：by classical; by_cases h : M a b; simp [wMask, maskW, h]
  -- TODO
  sorry

-- 525：wMask は点ごとに 0 か元の値
theorem ex525 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b = 0 ∨ wMask R M a b = R a b := by
  -- TODO
  sorry

-- 526：maskScore は score を超えない
theorem ex526 (M : Rel α β) (score : α → β → Nat) :
    ∀ a b, maskScore M score a b ≤ score a b := by
  -- TODO
  sorry

-- 527：attnNat の単調性（score）
theorem ex527 (keys : List β) (score score' : α → β → Nat) (val : β → Nat) :
    (∀ a b, score a b ≤ score' a b) →
    ∀ a, attnNat keys score val a ≤ attnNat keys score' val a := by
  -- TODO
  sorry

-- 528：空 keys の attnNat は 0
theorem ex528 (score : α → β → Nat) (val : β → Nat) :
    ∀ a, attnNat ([] : List β) score val a = 0 := by
  -- TODO
  sorry

-- 529：attnNat の単調性（val）
theorem ex529 (keys : List β) (score : α → β → Nat) (val val' : β → Nat) :
    (∀ b, val b ≤ val' b) →
    ∀ a, attnNat keys score val a ≤ attnNat keys score val' a := by
  -- TODO
  sorry

-- 530：マスクすると attention 出力は増えない
-- ★Decidable(M a b) は maskScore 側で classical を使っているので定義は通る
theorem ex530 (keys : List β) (M : Rel α β) (score : α → β → Nat) (val : β → Nat) :
    ∀ a, attnNat keys (maskScore M score) val a ≤ attnNat keys score val a := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 5) WRel 版 attention（縮約としての view）
--------------------------------------------------------------------------------

def attnWRel {α β γ : Type} (keys : List β) (QK : WRel α β) (KV : WRel β γ) : WRel α γ :=
  wCompList keys QK KV

-- 531：attnWRel は wCompList の別名
theorem ex531 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    attnWRel keys QK KV = wCompList keys QK KV := by
  -- TODO
  sorry

-- 532：attnWRel の左 0
theorem ex532 (keys : List β) (KV : WRel β γ) :
    attnWRel keys (wZero α β) KV = wZero α γ := by
  -- TODO
  sorry

-- 533：wMask の点ごとの ≤ 形
theorem ex533 (R : WRel α β) (M : Rel α β) :
    ∀ a b, wMask R M a b ≤ R a b := by
  -- TODO
  sorry

-- 534：maskScore の点ごとの ≤ 形
theorem ex534 (M : Rel α β) (score : α → β → Nat) :
    ∀ a b, maskScore M score a b ≤ score a b := by
  -- TODO
  sorry

-- 535：score が全部 0 なら attnNat も 0
theorem ex535 (keys : List β) (val : β → Nat) :
    ∀ a : α, attnNat keys (fun _ _ => 0) val a = 0 := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 536〜550：テンソルっぽい法則（分配 / 結合 / 二重和）
--------------------------------------------------------------------------------

-- 536：wsum は append に分配
theorem ex536 {X : Type} (xs ys : List X) (f : X → Nat) :
    wsum (xs ++ ys) f = wsum xs f + wsum ys f := by
  -- TODO
  sorry

-- 537：wsum は点ごとの加法に分配
theorem ex537 {X : Type} (xs : List X) (f g : X → Nat) :
    wsum xs (fun x => f x + g x) = wsum xs f + wsum xs g := by
  -- TODO
  sorry

-- 538：(Σ f) * t = Σ (f*t)
theorem ex538 {X : Type} (xs : List X) (f : X → Nat) (t : Nat) :
    wsum xs f * t = wsum xs (fun x => f x * t) := by
  -- TODO
  sorry

-- 539：t * (Σ f) = Σ (t*f)
theorem ex539 {X : Type} (xs : List X) (f : X → Nat) (t : Nat) :
    t * wsum xs f = wsum xs (fun x => t * f x) := by
  -- TODO
  sorry

-- 540：wCompList は keys の append に分配（合計を 2 ブロックに分割）
theorem ex540 (keys1 keys2 : List β) (R : WRel α β) (S : WRel β γ) :
    wCompList (keys1 ++ keys2) R S
      = wAdd (wCompList keys1 R S) (wCompList keys2 R S) := by
  -- TODO
  sorry

-- 541：wCompList の結合（有限二重和の入れ替えが本体）
theorem ex541 (keysβ : List β) (keysγ : List γ)
    (R : WRel α β) (S : WRel β γ) (T : WRel γ δ) :
    wCompList keysγ (wCompList keysβ R S) T
      = wCompList keysβ R (wCompList keysγ S T) := by
  -- TODO
  sorry

-- 542：AND マスクは 0/1 の積になる
theorem ex542 (M1 M2 : Rel α β) :
    maskW (fun a b => M1 a b ∧ M2 a b)
      = (fun a b => maskW M1 a b * maskW M2 a b) := by
  -- TODO
  sorry

-- 543：二重マスク = AND マスク
theorem ex543 (R : WRel α β) (M1 M2 : Rel α β) :
    wMask (wMask R M1) M2 = wMask R (fun a b => M1 a b ∧ M2 a b) := by
  -- TODO
  sorry

-- 544：WLe の refl
theorem ex544 (R : WRel α β) :
    WLe R R := by
  -- TODO
  sorry

-- 545：WLe の trans
theorem ex545 (R S T : WRel α β) :
    WLe R S → WLe S T → WLe R T := by
  -- TODO
  sorry

-- 546：wAdd は両側単調
theorem ex546 (R R' S S' : WRel α β) :
    WLe R R' → WLe S S' → WLe (wAdd R S) (wAdd R' S') := by
  -- TODO
  sorry

-- 547：wMask は R に単調
theorem ex547 (R R' : WRel α β) (M : Rel α β) :
    WLe R R' → WLe (wMask R M) (wMask R' M) := by
  -- TODO
  sorry

-- 548：wCompList は両側単調
theorem ex548 (keys : List β) (R R' : WRel α β) (S S' : WRel β γ) :
    WLe R R' → WLe S S' → WLe (wCompList keys R S) (wCompList keys R' S') := by
  -- TODO
  sorry

-- 549：左をマスクすると合成結果も増えない
theorem ex549 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
    WLe (wCompList keys (wMask R M) S) (wCompList keys R S) := by
  -- TODO
  sorry

-- 550：True マスクは合成しても変わらない
theorem ex550 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wCompList keys (wMask QK (fun _ _ => True)) KV = wCompList keys QK KV := by
  -- TODO
  sorry

end TL
