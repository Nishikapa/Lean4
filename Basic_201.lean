--------------------------------------------------------------------------------
-- 演習問題 201〜220（系統チェンジ：帰納型 Tree / Unit・Empty / Sigma(依存ペア)）
-- ※ import Mathlib なしでOK
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 準備：自作の Tree 型
--------------------------------------------------------------------------------
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

namespace Tree

def map (f : α → β) : Tree α → Tree β
  | leaf a   => leaf (f a)
  | node l r => node (map f l) (map f r)

def mirror : Tree α → Tree α
  | leaf a   => leaf a
  | node l r => node (mirror r) (mirror l)

def all (P : α → Prop) : Tree α → Prop
  | leaf a   => P a
  | node l r => all P l ∧ all P r

def any (P : α → Prop) : Tree α → Prop
  | leaf a   => P a
  | node l r => any P l ∨ any P r

def fold (leafF : α → β) (nodeF : β → β → β) : Tree α → β
  | leaf a   => leafF a
  | node l r => nodeF (fold leafF nodeF l) (fold leafF nodeF r)

end Tree

--------------------------------------------------------------------------------
-- Tree：帰納法（induction）で解く問題
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 201：mirror は2回で元に戻る ★★★☆
-- ヒント: induction t with | leaf a => ... | node l r ihL ihR => ...
example (t : Tree α) : Tree.mirror (Tree.mirror t) = t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 202：map id = id ★★★☆
-- ヒント: induction t <;> dsimp [Tree.map]
example (t : Tree α) : Tree.map (fun x => x) t = t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 203：map の合成則 ★★★★
-- map g (map f t) = map (fun x => g (f x)) t
-- ヒント: induction t <;> dsimp [Tree.map] <;> rw [*]
example (f : α → β) (g : β → γ) (t : Tree α) :
    Tree.map g (Tree.map f t) = Tree.map (fun x => g (f x)) t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 204：mirror と map の可換 ★★★★
-- mirror (map f t) = map f (mirror t)
-- ヒント: induction t <;> dsimp [Tree.map, Tree.mirror] <;> rw [*]
example (f : α → β) (t : Tree α) :
    Tree.mirror (Tree.map f t) = Tree.map f (Tree.mirror t) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 205：all と map（全称の押し込み）★★★★
-- all P (map f t) ↔ all (fun a => P (f a)) t
-- ヒント: induction t <;> dsimp [Tree.all, Tree.map] <;> constructor <;> intro h
example (P : β → Prop) (f : α → β) (t : Tree α) :
    Tree.all P (Tree.map f t) ↔ Tree.all (fun a => P (f a)) t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 206：all と mirror（左右を入れ替えても all は同じ）★★★☆
-- all P (mirror t) ↔ all P t
-- ヒント: induction t <;> dsimp [Tree.all, Tree.mirror] <;> constructor <;> intro h
example (P : α → Prop) (t : Tree α) :
    Tree.all P (Tree.mirror t) ↔ Tree.all P t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 207：fold と map（葉の関数が合成される）★★★★☆
-- fold leafF nodeF (map f t) = fold (fun a => leafF (f a)) nodeF t
-- ヒント: induction t <;> dsimp [Tree.fold, Tree.map] <;> rw [*]
example (f : α → β) (leafF : β → γ) (nodeF : γ → γ → γ) (t : Tree α) :
    Tree.fold leafF nodeF (Tree.map f t)
      = Tree.fold (fun a => leafF (f a)) nodeF t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 208：fold と mirror（nodeF を左右反転すると一致）★★★★☆
-- fold leafF nodeF (mirror t) = fold leafF (fun x y => nodeF y x) t
-- ヒント: induction t <;> dsimp [Tree.fold, Tree.mirror] <;> rw [*]
example (leafF : α → β) (nodeF : β → β → β) (t : Tree α) :
    Tree.fold leafF nodeF (Tree.mirror t)
      = Tree.fold leafF (fun x y => nodeF y x) t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 209：nodeF が可換なら fold は mirror で不変 ★★★★★
-- (∀x y, nodeF x y = nodeF y x) → fold ... (mirror t) = fold ... t
-- ヒント: 208 を使って、最後に可換性で書き換える
example (leafF : α → β) (nodeF : β → β → β) (t : Tree α) :
    (∀ x y, nodeF x y = nodeF y x) →
    Tree.fold leafF nodeF (Tree.mirror t) = Tree.fold leafF nodeF t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 210：Tree版ド・モルガン（any の否定）★★★★☆
-- ¬ any P t ↔ all (fun a => ¬ P a) t
-- ヒント: induction t
--   - leaf: ¬P a ↔ ¬P a
--   - node: ¬(A ∨ B) ↔ (¬A ∧ ¬B) を手で作る
example (P : α → Prop) (t : Tree α) :
    ¬ Tree.any P t ↔ Tree.all (fun a => ¬ P a) t := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- Unit / Empty：データ型の“万能性”（cases / funext）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 211：Unit の万能性（Unit→β は β と同じ情報）★★★★
-- 「相互変換 + 往復恒等」で示す
example :
  ∃ toVal : (Unit → β) → β,
  ∃ fromVal : β → (Unit → β),
    (∀ h : Unit → β, fromVal (toVal h) = h) ∧
    (∀ b : β, toVal (fromVal b) = b) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 212：Prod の右単位元（α×Unit は α と同じ）★★★☆
example :
  ∃ toVal : (α × Unit) → α,
  ∃ fromVal : α → (α × Unit),
    (∀ p : α × Unit, fromVal (toVal p) = p) ∧
    (∀ a : α, toVal (fromVal a) = a) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 213：Prod の左単位元（Unit×α は α と同じ）★★★☆
example :
  ∃ toVal : (Unit × α) → α,
  ∃ fromVal : α → (Unit × α),
    (∀ p : Unit × α, fromVal (toVal p) = p) ∧
    (∀ a : α, toVal (fromVal a) = a) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 214：Empty からの関数は一意 ★★★☆
-- ヒント: funext e; cases e
example (f g : Empty → α) : f = g := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 215：Sum Empty α は α と同じ ★★★★
-- toVal : Sum Empty α → α
-- fromVal : α → Sum Empty α
-- 往復恒等
example :
  ∃ toVal : Sum Empty α → α,
  ∃ fromVal : α → Sum Empty α,
    (∀ s : Sum Empty α, fromVal (toVal s) = s) ∧
    (∀ a : α, toVal (fromVal a) = a) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- Sigma（依存ペア）：Nonempty / ∃ / 依存カリー化
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 216：Nonempty (Sigma P) ↔ ∃x, P x （P:Prop版）★★★★
-- ヒント:
--   (→) obtain ⟨s⟩ := h; exact ⟨s.1, s.2⟩
--   (←) obtain ⟨x,hx⟩ := hex; exact ⟨⟨x,hx⟩⟩
example (P : α → Prop) :
    Nonempty { x : α // P x } ↔ ∃ x, P x := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 217：Sigma が定数なら Prod と同じ（Σ _ : α, β ≈ α×β）★★★★
example :
  ∃ toProd : (Sigma (fun _ : α => β)) → (α × β),
  ∃ fromProd : (α × β) → Sigma (fun _ : α => β),
    (∀ s : Sigma (fun _ : α => β), fromProd (toProd s) = s) ∧
    (∀ p : α × β, toProd (fromProd p) = p) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 218：Sigma と Sum の分配（Type族版）★★★★★
-- P Q : α → Type のとき
-- Σ x, (P x ⊕ Q x)   と   (Σ x, P x) ⊕ (Σ x, Q x)  は同じ情報
example (P Q : α → Type) :
  ∃ toSum :
      (Sigma (fun x : α => Sum (P x) (Q x))) → Sum (Sigma P) (Sigma Q),
  ∃ fromSum :
      Sum (Sigma P) (Sigma Q) → (Sigma (fun x : α => Sum (P x) (Q x))),
    (∀ s, fromSum (toSum s) = s) ∧
    (∀ t, toSum (fromSum t) = t) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 219：依存関数の funext（dependent funext）★★★★
-- f g : (x:α) → B x で、点ごとに等しいなら関数として等しい
-- ヒント: intro h; funext x; exact h x
example {B : α → Type} (f g : (x : α) → B x) :
    (∀ x, f x = g x) → f = g := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 220：Sigma からの関数は「依存カリー化」できる ★★★★★
-- (Σ x, B x) → γ   と   (∀ x, B x → γ)  の相互変換（往復恒等）
example {B : α → Type} :
  ∃ toDep : ((Sigma B) → γ) → (∀ x : α, B x → γ),
  ∃ fromDep : (∀ x : α, B x → γ) → ((Sigma B) → γ),
    (∀ h, fromDep (toDep h) = h) ∧
    (∀ k, toDep (fromDep k) = k) := by
  -- TODO
  sorry
