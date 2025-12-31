
-- Basic_101.lean
--------------------------------------------------------------------------------
-- 演習問題 101：∃ の二重否定除去（古典）
-- ¬¬(∃x, P x) → ∃x, P x
-- ヒント: apply Classical.byContradiction; intro hnot; apply hnn; exact hnot
example (P : α → Prop) :
    ¬¬ (∃ x, P x) → ∃ x, P x := by
  intro a
  apply Classical.byContradiction
  intro b
  apply a
  exact b
--------------------------------------------------------------------------------
-- 演習問題 102：「全員¬Pではない」→「Pな人がいる」（古典）
-- ¬(∀x, ¬P x) → ∃x, P x
-- ヒント:
--   1) 84を S x := ¬P x に適用すると ∃x, ¬¬P x が出る
--   2) その x について ¬¬P x から P x を古典で出す（byContradiction）
example (P : α → Prop) :
    ¬ (∀ x, ¬ P x) → ∃ x, P x := by
  intro a
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  intro d
  apply b
  exists c
--------------------------------------------------------------------------------
-- 演習問題 103：∃ と定数Aの“くくり出し”（直観主義でOK）
-- (∃x, P x ∧ A) ↔ (∃x, P x) ∧ A
-- ヒント:
--   (→) obtain ⟨x, hp, ha⟩ := ... して両方作る
--   (←) obtain ⟨⟨x,hp⟩, ha⟩ := ... して exists x; exact ⟨hp, ha⟩
example (P : α → Prop) (A : Prop) :
    (∃ x, P x ∧ A) ↔ (∃ x, P x) ∧ A := by
  constructor
  intro a
  obtain ⟨b, c⟩ := a
  constructor
  exists b
  exact c.left
  exact c.right
  intro d
  obtain ⟨⟨e, f⟩, g⟩ := d
  exists e
--------------------------------------------------------------------------------
-- 演習問題 104：A→∃ と ∃(A→) の行き来（Inhabited が必要・直観主義でOK）
-- (A → ∃x, P x) ↔ ∃x, (A → P x)
-- ヒント（左→右）:
--   by_cases a : A
--   - Aが真なら h a から witness を取り、A→P x を作る（fun _ => px）
--   - Aが偽なら default を選び、A→P default は偽から何でも言える
example (P : α → Prop) (A : Prop) [Inhabited α] :
    (A → ∃ x, P x) ↔ ∃ x, (A → P x) := by
  constructor
  intro a
  by_cases b : A
  have c: ∃ x, P x := by
    apply a
    exact b
  obtain ⟨d, e⟩ := c
  exists d
  intro f
  exact e
  exists Inhabited.default
  intro g
  exfalso
  apply b
  exact g
  intro h
  intro i
  obtain ⟨j, k⟩ := h
  have l : P j := by
    apply k
    exact i
  exists j
--------------------------------------------------------------------------------
-- 演習問題 105：∀(P→Q) と ¬∃(P∧¬Q) の同値（古典）
-- (∀x, P x → Q x) ↔ ¬(∃x, P x ∧ ¬Q x)
-- ヒント:
--   (→) は直観主義でOK（P∧¬Q を仮定すると矛盾）
--   (←) xとhpを固定して Q x を示す：¬Q x を仮定して ∃ を作って矛盾（古典）
example (P Q : α → Prop) :
    (∀ x, P x → Q x) ↔ ¬ (∃ x, P x ∧ ¬ Q x) := by
  constructor
  intro a
  intro b
  obtain ⟨c, d⟩ := b
  have e : P c := by
    exact d.left
  have f : ¬ Q c := by
    exact d.right
  apply f
  have g : P c → Q c := by
    apply a
  apply g
  exact e
  intro h
  intro i
  intro j
  apply Classical.byContradiction
  intro k
  apply h
  exists i
--------------------------------------------------------------------------------
-- 演習問題 106：∃x∀y を否定すると ∀x∃y¬ に（古典）
-- ¬(∃x, ∀y, R x y) ↔ ∀x, ∃y, ¬R x y
-- ヒント:
--   (→) まず ¬∃ を ∀¬ にする：intro x; （直観主義でOK）
--       次に「¬∀y, R x y → ∃y, ¬R x y」を古典で（84をyに適用）
--   (←) obtain ⟨x, hx⟩ := ...; obtain ⟨y, hny⟩ := ...; exact hny (hx y)
example (R : α → β → Prop) :
    ¬ (∃ x, ∀ y, R x y) ↔ ∀ x, ∃ y, ¬ R x y := by
  constructor
  intro a
  intro b
  apply Classical.byContradiction
  intro c
  apply a
  exists b
  intro d
  apply Classical.byContradiction
  intro e
  apply c
  exists d
  intro f
  intro g
  obtain ⟨h, i⟩ := g
  have j:  (∃y, ¬R h y) := by
    apply f
  obtain ⟨k, l⟩ := j
  apply l
  apply i
------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 107〜116（解ける問題のみ）
-- 量化子×否定（18・84系）に加えて、Natのrw、関数の外延性、Listの帰納法など
-- 少し系統の違うものも混ぜています。
-- ※ import Mathlib なしでもOKな範囲で出題しています。
--------------------------------------------------------------------------------
variable {α β γ : Type}
--------------------------------------------------------------------------------
-- 演習問題 107：∃ と = の基本（直観主義でOK）
-- 「a という値で P が成り立つ」と「x=a かつ P x を満たす x が存在する」は同じ
-- ヒント:
--   (→) obtain ⟨x, hx⟩ := ...
--       hx.left : x = a で rw して P a を作る
--   (←) exists a; constructor; rfl; exact ha
example (P : α → Prop) (a : α) : (∃ x, x = a ∧ P x) ↔ P a := by
  constructor
  intro a
  obtain ⟨b, c⟩ := a
  have d : b = a := by
    exact c.left
  have e : P b := by
    exact c.right
  rw [← d]
  exact e
  intro f
  exists a
--------------------------------------------------------------------------------
-- 演習問題 108：存在 → 全称否定（直観主義でOK）
-- 「Pな人がいる」なら「全員Pじゃない」はありえない
-- ヒント: obtain ⟨x, hx⟩ := hex; apply (hallnot x); exact hx
example (P : α → Prop) : (∃ x, P x) → ¬ (∀ x, ¬ P x) := by
  intro a
  intro b
  obtain ⟨c, d⟩ := a
  have e : ¬ P c := by
    apply b
  apply e
  exact d
--------------------------------------------------------------------------------
-- 演習問題 109：98の逆向き（古典）
-- 「反例（¬Pな人）が存在しない」なら「全員P」
-- ヒント:
--   classical
--   intro hno x
--   P x を byContradiction で作る：
--     ¬P x を仮定すると ⟨x, ¬P x⟩ ができて hno と矛盾
example (P : α → Prop) : ¬ (∃ x, ¬ P x) → ∀ x, P x := by
  intro a
  intro b
  apply Classical.byContradiction
  intro c
  apply a
  exists b
--------------------------------------------------------------------------------
-- 演習問題 110：「全員P」か「反例がいる」か（古典）
-- 84（¬∀→∃¬）の “結果だけ” を OR で表現した形
-- ヒント:
--   classical
--   by_cases h : ∃ x, ¬ P x
--   · right; exact h
--   · left; 109 と同じ発想で ∀x, P x を作る（各xを背理法）
example (P : α → Prop) : (∀ x, P x) ∨ (∃ x, ¬ P x) := by
  by_cases a : (∃ x, ¬ P x)
  right
  exact a
  left
  intro b
  apply Classical.byContradiction
  intro c
  apply a
  exists b
--------------------------------------------------------------------------------
-- Nat 系（rwパズル）
--------------------------------------------------------------------------------
variable (a b c d : Nat)
--------------------------------------------------------------------------------
-- 演習問題 111：3項の展開（分配法則を2回）
-- ヒント: rw [Nat.left_distrib] を2回
example : a * (b + c + d) = a * b + a * c + a * d := by
  rw [Nat.left_distrib]
  rw [Nat.left_distrib]
--------------------------------------------------------------------------------
-- 演習問題 112：3項の因数分解（逆分配を2回）
-- ヒント: rw [← Nat.left_distrib] を2回
example : a * b + a * c + a * d = a * (b + c + d) := by
  rw [Nat.left_distrib]
  rw [Nat.left_distrib]
--------------------------------------------------------------------------------
-- 演習問題 113：succ と足し算（書き換え練習）
-- ヒント: rw [Nat.add_succ]
example : a + Nat.succ b = Nat.succ (a + b) := by
  rw [Nat.add_succ]
--------------------------------------------------------------------------------
-- 関数系（外延性 / funext）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 114：関数の外延性（funext）
-- 「全てのxで同じ値」なら「関数として等しい」
-- ヒント: intro h; funext x; apply h
example (f g : α → β) : (∀ x, f x = g x) → f = g := by
  intro a
  funext x
  apply a
--------------------------------------------------------------------------------
-- List 系（帰納法を1つだけ）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 115：List の ++ と []（帰納法の最初の一歩）
-- xs ++ [] = xs
-- ヒント:
--   induction xs with
--   | nil => rfl
--   | cons x xs ih =>
--       -- (x::xs) ++ [] は x :: (xs ++ []) に展開されるので ih を使う
--       simp [List.append, ih]
example (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp
--------------------------------------------------------------------------------
-- 論理系（分配の↔：命題論理、直観主義でOK）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 116：∧ のくくり出し（∨ との分配：双方向）
-- (P∧Q) ∨ (P∧R) ↔ P ∧ (Q ∨ R)
-- ヒント:
--   (→) cases h with | inl hpq => ... | inr hpr => ...
--   (←) cases h.right with | inl hq => ... | inr hr => ...
example (P Q R : Prop) : (P ∧ Q) ∨ (P ∧ R) ↔ P ∧ (Q ∨ R) := by
  constructor
  intro a
  cases a with
  | inl b =>
    constructor
    exact b.left
    left
    exact b.right
  | inr c =>
    constructor
    exact c.left
    right
    exact c.right
  intro d
  cases d.right with
  | inl e =>
    left
    constructor
    exact d.left
    exact e
  | inr f =>
    right
    constructor
    exact d.left
    exact f
------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 117〜126（10問）
-- 量化子×否定（18・84系）を少しひねる + 古典論理パズル + Natのrw + funext + List帰納
-- ※ import Mathlib なし想定（Lean4標準）で解ける命題だけです。
--------------------------------------------------------------------------------
variable {α β γ : Type}
--------------------------------------------------------------------------------
-- 演習問題 117：∀∃ の否定（古典）☆☆☆☆☆☆☆☆☆☆☆☆☆☆☆
-- ¬(∀x, ∃y, R x y) なら、ある x について全ての y がダメ（∀y, ¬R x y）
-- ヒント:
--   classical
--   1) ¬∀x... から ∃x, ¬(...) を作る（84系）
--   2) ¬(∃y, R x y) ↔ ∀y, ¬R x y は直観主義でOK（18系）
example (R : α → β → Prop) :
    ¬ (∀ x, ∃ y, R x y) → ∃ x, ∀ y, ¬ R x y := by
  intro a
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  apply Classical.byContradiction
  intro d
  apply b
  exists c
  intro e
  intro f
  apply d
  exists e
--------------------------------------------------------------------------------
-- 演習問題 118：∀∃ を「使って」結論を引き出す（直観主義OK）
-- (∀x, ∃y, R x y) と (∀x∀y, R x y → S x) から ∀x, S x
-- ヒント:
--   intro x; obtain ⟨y, rxy⟩ := h1 x; exact h2 x y rxy
example (R : α → β → Prop) (S : α → Prop) :
    (∀ x, ∃ y, R x y) → (∀ x, ∀ y, R x y → S x) → ∀ x, S x := by
  intro a
  intro b
  intro c
  have d: ∃ y, R c y := by
    apply a
  obtain ⟨e, f⟩ := d
  have g : ∀ (y : β), R c y → S c := by
    apply b
  have h : R c e → S c := by
    apply g
  apply h
  exact f
--------------------------------------------------------------------------------
-- 演習問題 119：¬(P↔Q) の中身（古典パズル）
-- 「同値ではない」↔「片方だけ真」（XOR）
-- ヒント:
--   classical; by_cases p : P; by_cases q : Q; で4分岐して詰めるのが定石
example (P Q : Prop) :
    ¬ (P ↔ Q) ↔ (P ∧ ¬ Q) ∨ (Q ∧ ¬ P) := by
    by_cases a : P
    have b : (P ↔ Q) ↔ Q := by
      constructor
      intro b1
      rw [←b1]
      exact a
      intro b2
      constructor
      intro b3
      exact b2
      intro b4
      exact a
    have c : (P ∧ ¬Q) ↔ ¬Q := by
      constructor
      intro c1
      exact c1.right
      intro c2
      constructor
      exact a
      exact c2
    have d : (Q ∧ ¬P) ↔ False := by
      constructor
      intro d1
      apply d1.right
      exact a
      intro d2
      contradiction
    have e : (¬Q ∨ False ) ↔ ¬Q := by
      constructor
      intro e1
      cases e1 with
      | inl e2 =>
        exact e2
      | inr e3 =>
        contradiction
      intro e4
      left
      exact e4
    have f : (P ∧ ¬Q ∨ Q ∧ ¬P) ↔ ¬Q := by
      rw [c]
      rw [d]
      rw [e]
    rw [b]
    rw [f]
    have g : (P ↔ Q) ↔ ¬Q := by
      constructor
      intro g1
      rw [←g1]
      exact a
      intro g2
      constructor
      intro g3
      apply Classical.byContradiction
      intro g4
      apply a
      exact g3
      intro g5
      apply Classical.byContradiction
      intro g6
      apply g2
      exact g5
    have h : (P ∧ ¬Q) ↔ False := by
      constructor
      intro h1
      apply h1.right
      have i : False := by
        apply a
        exact h1.left
      contradiction
      intro h2
      contradiction
    have i : (Q ∧ ¬P) ↔ Q := by
      constructor
      intro i1
      exact i1.left
      intro i2
      constructor
      exact i2
      apply Classical.byContradiction
      intro i3
      apply a
      apply Classical.byContradiction
      intro i4
      apply i3
      exact i4
    rw [g]
    rw [h]
    rw [i]
    constructor
    intro j
    by_cases k : Q
    right
    exact k
    left
    apply j
    exact k
    intro l
    intro m
    apply m
    cases l with
    | inl n =>
      contradiction
    | inr o =>
      exact o
--------------------------------------------------------------------------------
-- 演習問題 120： (∃x, P x) → Q の別表現（古典）
-- 「Pな人がいるならQ」↔「Pで、かつ ¬Q な人はいない」
-- ヒント:
--   (→) は直観主義でOK：∃x (P x ∧ ¬Q) を仮定して矛盾
--   (←) は古典：Q を背理法で出す（¬Q を仮定すると ∃x(Px∧¬Q) を作れて矛盾）
example (P : α → Prop) (Q : Prop) :
    ((∃ x, P x) → Q) ↔ ¬ (∃ x, P x ∧ ¬ Q) := by
  constructor
  intro a
  intro b
  obtain ⟨c, d⟩ := b
  have e : P c := by
    exact d.left
  have f : ¬ Q := by
    exact d.right
  apply f
  apply a
  exists c
  intro g
  intro h
  obtain ⟨i, j⟩ := h
  apply Classical.byContradiction
  intro k
  apply g
  have l : P i ∧ ¬Q := by
    constructor
    exact j
    exact k
  exists i
--------------------------------------------------------------------------------
-- Nat の rw パズル（少し濃く）
--------------------------------------------------------------------------------
variable (a b c d : Nat)
--------------------------------------------------------------------------------
-- 演習問題 121：右分配を2回（3項まとめて）
-- (a+b+c)*d を a*d + b*d + c*d に
-- ヒント: rw [Nat.right_distrib] を2回（必要なら add_assoc で整形）
example : (a + b + c) * d = a * d + b * d + c * d := by
  rw [Nat.right_distrib]
  rw [Nat.right_distrib]
--------------------------------------------------------------------------------
-- 演習問題 122：因数分解（掛け算の交換も混ぜる）
-- a*b + c*a = a*(b+c)
-- ヒント:
--   1) rw [Nat.mul_comm c a] で c*a を a*c に
--   2) rw [← Nat.left_distrib] でくくる
example : a * b + c * a = a * (b + c) := by
  rw [Nat.left_distrib]
  rw [Nat.mul_comm c a]
--------------------------------------------------------------------------------
-- 関数（funext の “↔ 版”）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 123：関数の等しさ ↔ 点ごとの等しさ
-- f=g ↔ ∀x, f x = g x
-- ヒント:
--   (→) intro h x; rw [h]
--   (←) intro h; funext x; exact h x
example (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  constructor
  intro a
  intro b
  rw [a]
  intro c
  funext d
  have e : f d = g d := by
    apply c
  exact e
--------------------------------------------------------------------------------
-- List（帰納法）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 124：map の合成（帰納法）
-- map f (map g xs) = map (fun x => f (g x)) xs
-- ヒント:
--   induction xs with
--   | nil => rfl
--   | cons x xs ih =>
--       -- 左右とも cons になるので ih で中身をそろえる
--       simp [List.map, ih]
example (f : β → γ) (g : α → β) (xs : List α) :
    List.map f (List.map g xs) = List.map (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, ih]
--------------------------------------------------------------------------------
-- 演習問題 125：append の結合則（帰納法）
-- (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
-- ヒント:
--   induction xs with
--   | nil => rfl
--   | cons x xs ih =>
--       simp [List.append, ih]
example (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [ih]
--------------------------------------------------------------------------------
-- 演習問題 126：∃ と ¬∀¬（古典）
-- 「Pな人がいる」↔「全員が ¬P ではない」
-- ヒント:
--   (→) は直観主義でOK（あなたの108）
--   (←) は古典（あなたの102相当）
example (P : α → Prop) : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  constructor
  intro a
  intro b
  obtain ⟨c, d⟩ := a
  have e : ¬ P c := by
    apply b
  apply e
  exact d
  intro f
  apply Classical.byContradiction
  intro g
  apply f
  intro h
  intro i
  apply g
  exists h
------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 127〜136（10問）
-- 量化子×否定（18・84系）を“ひねる” + Natのrwパズル + funext(2引数) + List/Option/Prod
-- ※ import Mathlib なし想定（Lean4標準）で証明できる命題だけです。
--------------------------------------------------------------------------------
variable {α β γ : Type}
--------------------------------------------------------------------------------
-- 演習問題 127：∃ と ¬ の応用（直観主義OK）
-- 「P∧Q∧R な人がいない」↔「任意のxで、PとQならRは成り立たない」
-- ヒント:
--   (→) intro x hp hq hr; apply h; exists x; constructor; exact hp; ...
--   (←) obtain ⟨x, hx⟩ := hex; で取り出して矛盾
example (P Q R : α → Prop) :
    ¬ (∃ x, P x ∧ Q x ∧ R x) ↔ ∀ x, P x → Q x → ¬ R x := by
  constructor
  intro a
  intro b
  intro c
  intro d
  intro e
  apply a
  exists b
  intro f
  intro g
  obtain ⟨h, i⟩ := g
  have j  : P h → Q h → ¬R h := by
    apply f
  have k : P h := by
    exact i.left
  have l : Q h := by
    exact i.right.left
  have m : R h := by
    exact i.right.right
  have n : ¬R h := by
    apply j
    exact k
    exact l
  apply n
  exact m
--------------------------------------------------------------------------------
-- 演習問題 128：∀ と ∧ の否定の分配（古典）
-- ¬(∀x, P x ∧ Q x) ↔ ¬(∀x, P x) ∨ ¬(∀x, Q x)
-- ヒント:
--   classical
--   (→) を示すときは byContradiction で「両方∀が成り立つ」と仮定して矛盾
--   (←) は直観主義でOK
example (P Q : α → Prop) :
    ¬ (∀ x, P x ∧ Q x) ↔ ¬ (∀ x, P x) ∨ ¬ (∀ x, Q x) := by
  constructor
  intro a
  have b: ∃ (x : α), ¬P x ∨ ¬Q x := by
    apply Classical.byContradiction
    intro b1
    apply a
    intro b2
    apply Classical.byContradiction
    intro b3
    apply b1
    exists b2
    apply Classical.byContradiction
    intro b4
    apply b3
    constructor
    apply Classical.byContradiction
    intro b5
    apply b4
    left
    exact b5
    apply Classical.byContradiction
    intro b6
    apply b4
    right
    exact b6
  obtain ⟨c, d⟩ := b
  cases d with
  | inl e =>
    left
    intro f
    apply e
    apply f
  | inr g =>
    right
    intro h
    apply g
    apply h
  intro i
  intro j
  cases i with
  | inl k =>
    apply k
    intro l
    have m : P l ∧ Q l := by
      apply j
    exact m.left
  | inr n =>
    apply n
    intro o
    have p : P o ∧ Q o := by
      apply j
    exact p.right
--------------------------------------------------------------------------------
-- 演習問題 129：¬∃ と ∃ を合成（直観主義OK）
-- 「Pな人はいない」かつ「Qな人はいる」なら「Qかつ¬Pな人がいる」
-- ヒント:
--   obtain ⟨x, hxQ⟩ := hexQ
--   refine ⟨x, ?_, ?_⟩
--   ¬P x は intro hp; apply hnot; exact ⟨x, hp⟩
example (P Q : α → Prop) :
    ¬ (∃ x, P x) → (∃ x, Q x) → ∃ x, Q x ∧ ¬ P x := by
  intro a
  have b: ∀x , ¬P x := by
    intro b1
    intro b2
    apply a
    exists b1
  intro c
  obtain ⟨d, e⟩ := c
  have f : ¬P d := by
    apply b
  have g : Q d ∧ ¬P d := by
    constructor
    exact e
    exact f
  exists d
--------------------------------------------------------------------------------
-- Nat の rw パズル
--------------------------------------------------------------------------------
variable (a b c d : Nat)
--------------------------------------------------------------------------------
-- 演習問題 130：足し算の並べ替えパズル（assoc + comm）
-- ヒント: add_assoc でカッコを動かし、add_comm b c を奥に当てる
example : (a + b) + (c + d) = a + c + (b + d) := by
  rw [← Nat.add_assoc]
  rw [Nat.add_assoc a b c]
  rw [Nat.add_comm b c]
  rw [← Nat.add_assoc a c b]
  rw [Nat.add_assoc (a + c) b d]
--------------------------------------------------------------------------------
-- 演習問題 131：因数分解（交換も混ぜる）
-- a*b + a*c + d*a = a*(b+c+d)
-- ヒント:
--   1) rw [Nat.mul_comm d a] で d*a を a*d に
--   2) ← Nat.left_distrib を2回（必要なら add_assoc で形を整える）
example : a * b + a * c + d * a = a * (b + c + d) := by
  rw [Nat.left_distrib]
  rw [Nat.left_distrib]
  rw [Nat.mul_comm d a]
--------------------------------------------------------------------------------
-- 関数（funext を2回：2引数関数の外延性）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 132：2引数関数の外延性
-- ヒント: intro h; funext x; funext y; exact h x y
example (f g : α → β → γ) :
    (∀ x y, f x y = g x y) → f = g := by
  intro a
  funext x
  funext y
  apply a

--------------------------------------------------------------------------------
-- List（帰納法）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 133：map と append の分配（帰納法）
-- map f (xs ++ ys) = map f xs ++ map f ys
-- ヒント:
--   induction xs with
--   | nil => rfl
--   | cons x xs ih => simp [List.map, List.append, ih]
example (f : α → β) (xs ys : List α) :
    List.map f (xs ++ ys) = List.map f xs ++ List.map f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, ih]

--------------------------------------------------------------------------------
-- Option（場合分け）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 134：Option.map の合成（cases 一発）
-- ヒント: cases o <;> rfl
example (f : β → γ) (g : α → β) (o : Option α) :
    Option.map f (Option.map g o) = Option.map (fun x => f (g x)) o := by
  cases o <;> rfl

--------------------------------------------------------------------------------
-- Prod（ペア）の等式：成分ごとの等式と同値
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 135：ペアの等しさ ↔ 成分の等しさ
-- ヒント:
--   (→) intro h; cases h; constructor <;> rfl
--   (←) intro h; cases h with | intro ha hb => ...（rwで揃えて rfl）
example (a1 a2 : α) (b1 b2 : β) :
    (a1, b1) = (a2, b2) ↔ a1 = a2 ∧ b1 = b2 := by
  constructor
  intro a
  cases a
  constructor
  rfl
  rfl
  intro b
  cases b with
  | intro ha hb =>
    rw [ha]
    rw [hb]

--------------------------------------------------------------------------------
-- 演習問題 136：∃ の排中（古典）
-- 「Pな人がいる」か「全員Pではない」か（∃に対する排中）
-- ヒント:
--   classical
--   by_cases h : ∃ x, P x
--   · left; exact h
--   · right; intro x; intro hp; apply h; exact ⟨x, hp⟩
example (P : α → Prop) : (∃ x, P x) ∨ (∀ x, ¬ P x) := by
  by_cases a : (∃ x, P x)
  left
  exact a
  right
  intro b
  intro c
  apply a
  exists b
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 137〜146（10問 / Nat と List は無し）
-- 量化子×否定（18・84系） + 関数（funext） + Sum/Prod/Option の“型の論理”
-- ※ import Mathlib なし（Lean4標準）で証明できる命題だけです。
--------------------------------------------------------------------------------
variable {α β γ δ : Type}
--------------------------------------------------------------------------------
-- 演習問題 137：∃ と ∀ の連携（直観主義OK）
-- 「Pな人がいる」かつ「PならQ」なら Q
-- ヒント: obtain ⟨x,hpx⟩ := hex; apply hall x hpx
example (P : α → Prop) (Q : Prop) :
    (∃ x, P x) → (∀ x, P x → Q) → Q := by
  intro a
  intro b
  obtain ⟨c, d⟩ := a
  have e : P c → Q := by
    apply b
  apply e
  exact d

--------------------------------------------------------------------------------
-- 演習問題 138：∃ を写す（直観主義OK）
-- 「PならQ」が全員について成り立ち、Pな人がいるなら、Qな人もいる
-- ヒント: obtain ⟨x,hpx⟩ := hex; exists x; exact (h x hpx)
example (P Q : α → Prop) :
    (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) := by
  intro a
  intro b
  obtain ⟨c, d⟩ := b
  have e : P c → Q c := by
    apply a
  have f : Q c := by
    apply e
    exact d
  exists c

--------------------------------------------------------------------------------
-- 演習問題 139：量化子つき対偶（直観主義OK）
-- 「(∃x,Px) なら Q」かつ「¬Q」なら「全員 ¬P」
-- ヒント:
--   intro x hp; apply hnotQ; apply himp; exact ⟨x, hp⟩
example (P : α → Prop) (Q : Prop) :
    ((∃ x, P x) → Q) → ¬ Q → ∀ x, ¬ P x := by
  intro a
  intro b
  intro c
  intro d
  apply b
  apply a
  exists c

--------------------------------------------------------------------------------
-- 演習問題 140：¬∀(→定数) の中身（古典）
-- ¬(∀x, P x → Q) ↔ (∃x, P x) ∧ ¬Q
-- ヒント:
--   classical
--   (→) は by_cases q : Q で分岐すると作りやすい
example (P : α → Prop) (Q : Prop) :
    ¬ (∀ x, P x → Q) ↔ (∃ x, P x) ∧ ¬ Q := by
  constructor
  intro a
  constructor
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  intro d
  apply Classical.byContradiction
  intro e
  apply b
  exists c
  intro f
  apply a
  intro g
  intro h
  exact f
  intro i
  intro j
  obtain ⟨k, l⟩ := i
  obtain ⟨m, n⟩ := k
  apply l
  have o : P m → Q := by
    apply j
  apply o
  exact n

--------------------------------------------------------------------------------
-- 演習問題 141：選択公理（Skolem化）（古典）
-- ∀x∃y Rxy から、関数 f を作って ∀x R x (f x)
-- ヒント:
--   classical
--   let f : α → β := fun x => Classical.choose (h x)
--   have hf : ∀ x, R x (f x) := fun x => Classical.choose_spec (h x)
example (R : α → β → Prop) :
    (∀ x, ∃ y, R x y) → ∃ f : α → β, ∀ x, R x (f x) := by
  intro a
  let b : α → β := fun x => Classical.choose (a x)
  exists b
  intro c
  exact Classical.choose_spec (a c)

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 142〜146（作り直し版）
-- ※ あなたの環境では Equiv / ≃ が使えないので、
--   「相互変換（to/from）が存在して、往復すると元に戻る」形式で出題します。
-- ※ Nat / List の問題は入れていません。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 142：Sum（Either）の万能性（相互変換版）
-- (Sum α β → γ) と (α→γ)×(β→γ) が「同じ情報」を持つことを示す。
--
-- 目標：
--   toPair と fromPair を作り、
--   fromPair (toPair h) = h  と  toPair (fromPair fg) = fg  を証明する。
--
-- ヒント：
--   - 関数の等式は funext
--   - Sum の場合分けは cases s with | inl a => ... | inr b => ...
example :
  ∃ toPair : (Sum α β → γ) → (α → γ) × (β → γ),
  ∃ fromPair : ((α → γ) × (β → γ)) → (Sum α β → γ),
    (∀ h : Sum α β → γ, fromPair (toPair h) = h) ∧
    (∀ fg : (α → γ) × (β → γ), toPair (fromPair fg) = fg) := by
  refine ⟨?toPair, ?fromPair, ?hLeft, ?hRight⟩

  -- toPair
  intro e
  refine ⟨?f, ?g⟩
  intro f
  apply e
  exact Sum.inl f
  intro h
  apply e
  exact Sum.inr h

  -- fromPair
  intro i
  intro j
  obtain ⟨k, l⟩ := i
  cases j with
  | inl m =>
    apply k
    exact m
  | inr n =>
    apply l
    exact n

  -- hLeft
  intro p
  funext q
  cases q with
  | inl r =>
    dsimp
  | inr s =>
    dsimp

  -- hRight
  intro t
  obtain ⟨u, v⟩ := t
  apply Prod.ext
  funext w
  dsimp
  funext x
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 143：Prod のカリー化（相互変換版）
-- ((α×β)→γ) と (α→β→γ) の間の相互変換を作って、往復が恒等になることを示す。
--
-- ヒント：
--   curry f := fun a b => f (a,b)
--   uncurry g := fun p => g p.1 p.2
--   関数の等式は funext（2回使うこともある）
example :
  ∃ curry : ((α × β) → γ) → (α → β → γ),
  ∃ uncurry : (α → β → γ) → ((α × β) → γ),
    (∀ f : (α × β) → γ, uncurry (curry f) = f) ∧
    (∀ g : α → β → γ, curry (uncurry g) = g) := by
  refine ⟨?curry, ?uncurry, ?hLeft, ?hRight⟩
  -- curry
  intro e
  intro f
  intro g
  apply e
  exact (f, g)

  -- uncurry
  intro h
  intro i
  obtain ⟨j, k⟩ := i
  apply h
  exact j
  exact k

  -- hLeft
  intro l
  funext m
  obtain ⟨n, o⟩ := m
  dsimp

  -- hRight
  intro p
  funext q
  funext r
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 144：Option の万能性（相互変換版）
-- (Option α → β) と (β × (α → β)) の相互変換を作って、往復が恒等になることを示す。
--
-- ヒント：
--   toPair h := (h none, fun a => h (some a))
--   fromPair (b0, f) := fun o => match o with | none => b0 | some a => f a

example :
  ∃ toPair : (Option α → β) → β × (α → β),
  ∃ fromPair : (β × (α → β)) → (Option α → β),
    (∀ h : Option α → β, fromPair (toPair h) = h) ∧
    (∀ fg : β × (α → β), toPair (fromPair fg) = fg) := by

  refine ⟨?toPair, ?fromPair, ?hLeft, ?hRight⟩

  -- toPair
  intro e
  refine (?pNone, ?pSome)

  -- none の場合
  apply e
  exact none

  -- some a の場合
  intro f
  apply e
  exact some f

  -- fromPair
  intro g
  intro h
  obtain ⟨i, j⟩ := g
  cases h with
  | none =>
    exact i
  | some k =>
    apply j
    exact k

  -- hLeft
  intro l
  funext m
  dsimp
  cases m with
  | none =>
    dsimp
  | some n =>
    dsimp

  -- hRight
  intro n
  obtain ⟨o, p⟩ := n
  constructor

--------------------------------------------------------------------------------
-- 演習問題 145：関数外延性の形（↔ は Prop 同士なのでOK）
-- f=g ↔ ∀x, f x = g x
--
-- ヒント：
--   (→) intro h x; rw [h]
--   (←) intro h; funext x; exact h x
example (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  constructor
  intro a
  intro b
  rw [a]
  intro c
  funext d
  apply c

--------------------------------------------------------------------------------
-- 演習問題 146：量化子の合体（直観主義OK）
-- 「全員P」かつ「Qな人がいる」なら、「PかつQな人がいる」
--
-- ヒント：
--   obtain ⟨x, hxQ⟩ := hQ
--   have hxP : P x := hP x
--   exists x; constructor; exact hxP; exact hxQ
example (P Q : α → Prop) :
    (∀ x, P x) → (∃ x, Q x) → ∃ x, P x ∧ Q x := by
    intro a
    intro b
    obtain ⟨c, d⟩ := b
    have e : P c := by
      apply a
    have f : P c ∧ Q c := by
      constructor
      exact e
      exact d
    exists c

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 147〜150（Nat / List なし）
-- 量化子×否定 + Option/Sum の casesOn + funext（関数の等しさ）
-- ※ import Mathlib なしで解けます
--------------------------------------------------------------------------------

variable {α β γ : Type}

--------------------------------------------------------------------------------
-- 演習問題 147：¬∃ を “使って” 全称否定を作る（直観主義OK）
-- 「Pな人が存在しない」かつ「QならP（全員について）」なら、全員 ¬Q
--
-- ヒント:
--   intro hno hex; intro x hxQ
--   have hxP : P x := hex x hxQ
--   apply hno; exact ⟨x, hxP⟩
example (P Q : α → Prop) :
    ¬ (∃ x, P x) → (∀ x, Q x → P x) → ∀ x, ¬ Q x := by

  intro a b c d
  apply a
  have e : Q c → P c := by
    apply b
  exists c
  apply e
  exact d

--------------------------------------------------------------------------------
-- 演習問題 148：Option.casesOn を理解する（funext + cases）
-- 「casesOn で分解して作った関数」は元の関数と等しい
--
-- ヒント:
--   funext o
--   cases o <;> rfl
example (h : Option α → β) :
    (fun o => Option.casesOn o (h none) (fun a => h (some a))) = h := by

  funext a
  cases a with
  | none =>
    rfl
  | some b =>
    rfl


--------------------------------------------------------------------------------
-- 演習問題 149：引数の入れ替え（flip）と funext（2回）
-- 自作 flip を2回かけると元に戻る
--
-- ヒント:
--   funext a; funext b; rfl
def myFlip (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

example (f : α → β → γ) :
    myFlip (myFlip f) = f := by

  funext a
  funext b
  dsimp [myFlip]

--------------------------------------------------------------------------------
-- 演習問題 150：¬∀(→定数) の中身（古典）☆☆☆
-- ¬(∀x, P x → Q) ↔ (∃x, P x) ∧ ¬Q
--
-- ヒント:
--   constructor
--   · intro hnot
--     -- まず ¬Q を作る：Q を仮定すると ∀x, (P x → Q) が作れて矛盾
--     -- 次に ∃x, P x を作る：背理法で「¬∃x,Px」を仮定し、
--     --   そこから ∀x, (P x → Q) を“爆発”で作れて矛盾
--   · rintro ⟨hexP, hnQ⟩ hall
--     obtain ⟨x, hxP⟩ := hexP
--     apply hnQ
--     exact hall x hxP
example (P : α → Prop) (Q : Prop) :
    ¬ (∀ x, P x → Q) ↔ (∃ x, P x) ∧ ¬ Q := by

  refine ⟨?toLeft, ?toRight⟩

  -- toLeft
  intro a

  refine ⟨?case1, ?case2⟩

  -- case1
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  intro d
  apply Classical.byContradiction
  intro e
  apply b
  exists c

  -- case2
  intro f
  apply a
  intro g
  intro h
  exact f

  -- toRight
  intro i
  intro j
  obtain ⟨k, l⟩ := i.left
  apply i.right
  have m : P k → Q := by
    apply j
  apply m
  exact l

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
