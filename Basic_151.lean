------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 151〜160（難易度アップ / Nat・Listなし）
-- 量化子×否定（18・84系の強化） + Sum/Option/Prod の「同型（相互変換）」 + 関数の等式
-- ※ import Mathlib なし / Equiv なしでも解ける形式
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 演習問題 151：否定の押し込み（3段量化子・古典）★★★★★
-- ¬(∀x, ∃y, ∀z, R x y z) から
--   ∃x, ∀y, ∃z, ¬ R x y z
--
-- ヒント：
--   classical
--   1) ¬∀x ... から ∃x ¬(...) を作る（84系）
--   2) ¬(∃y ...) を ∀y ¬... に（18系）
--   3) ¬(∀z ...) を ∃z ¬... に（ここが古典）
example (R : α → β → γ → Prop) :
    ¬ (∀ x, ∃ y, ∀ z, R x y z) → ∃ x, ∀ y, ∃ z, ¬ R x y z := by
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
  have f : ¬∀ (y : β), ∃ z, ¬R c y z := by
    intro f1
    apply b
    exists c
  have g : ¬∀ (z : γ), R c e z := by
    intro g1
    apply d
    exists e
  apply Classical.byContradiction
  intro h
  apply g
  intro i
  apply Classical.byContradiction
  intro j
  apply h
  exists i

--------------------------------------------------------------------------------
-- 演習問題 152：否定の押し込み（∃∀∃ の否定・古典）★★★★★
-- ¬(∃x, ∀y, ∃z, R x y z) ↔ ∀x, ∃y, ∀z, ¬ R x y z
--
-- ヒント：
--   classical
--   (→) は 84系→18系→84系 の順で押し込むと見通しが良い
--   (←) は取り出して直接矛盾
example (R : α → β → γ → Prop) :
    ¬ (∃ x, ∀ y, ∃ z, R x y z) ↔ ∀ x, ∃ y, ∀ z, ¬ R x y z := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a b
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
  apply e
  exists f

  -- hRight
  intro a b
  obtain ⟨b1, b2⟩ := b
  have c: ∃ y, ∀ (z : γ), ¬R b1 y z := by
    apply a
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := b2 c1
  have e : ¬R b1 c1 d1 := c2 d1
  apply e
  exact d2

--------------------------------------------------------------------------------
-- 演習問題 153：Option と Sum Unit の対応（相互変換版）★★★★
-- Option α と Sum Unit α は「同じ情報」を持つ（none ↔ inl (), some a ↔ inr a）
--
-- 目標：to/from を作り、往復が恒等になることを証明
-- ヒント：
--   - Option は cases o with | none => ... | some a => ...
--   - Sum は cases s with | inl u => ... | inr a => ...
example :
  ∃ toSum : Option α → Sum Unit α,
  ∃ fromSum : Sum Unit α → Option α,
    (∀ o : Option α, fromSum (toSum o) = o) ∧
    (∀ s : Sum Unit α, toSum (fromSum s) = s) := by

  refine ⟨?toSum, ?fromSum, ?hLeft, ?hRight⟩

  -- toSum
  intro a
  cases a with
  | none =>
    exact Sum.inl ()
  | some a1 =>
    exact Sum.inr a1

  -- fromSum
  intro b
  cases b with
  | inl b1 =>
    exact none
  | inr b2 =>
    exact some b2

  -- hLeft
  intro c
  cases c with
  | none =>
    dsimp
  | some c1 =>
    dsimp

  -- hRight
  intro d
  cases d with
  | inl d1 =>
    dsimp
  | inr d2 =>
    dsimp

--------------------------------------------------------------------------------
-- 演習問題 154：Sum の結合（相互変換版）★★★★
-- Sum (Sum α β) γ  と  Sum α (Sum β γ) の間の相互変換
--
-- ヒント：
--   - cases を2段階で
--   - 往復は funext 不要（データなので cases して rfl が多い）
example :
  ∃ assocL : Sum (Sum α β) γ → Sum α (Sum β γ),
  ∃ assocR : Sum α (Sum β γ) → Sum (Sum α β) γ,
    (∀ s : Sum (Sum α β) γ, assocR (assocL s) = s) ∧
    (∀ t : Sum α (Sum β γ), assocL (assocR t) = t) := by

  refine ⟨?assocL, ?assocR, ?hLeft, ?hRight⟩

  -- assocL
  intro a
  cases a with
  | inl a1 =>
    cases a1 with
    | inl a2 =>
      exact Sum.inl a2
    | inr a3 =>
      exact Sum.inr (Sum.inl a3)
  | inr a4 =>
    exact Sum.inr (Sum.inr a4)

  -- assocR
  intro b
  cases b with
  | inl b1 =>
    exact Sum.inl (Sum.inl b1)
  | inr b2 =>
    cases b2 with
    | inl b3 =>
      exact Sum.inl (Sum.inr b3)
    | inr b4 =>
      exact Sum.inr b4

  -- hLeft
  intro c
  cases c with
  | inl c1 =>
    cases c1 with
    | inl c2 =>
      dsimp
    | inr c3 =>
      dsimp
  | inr c4 =>
    dsimp

  -- hRight
  intro d
  cases d with
  | inl d1 =>
    dsimp
  | inr d2 =>
    cases d2 with
    | inl d3 =>
      dsimp
    | inr d4 =>
      dsimp

--------------------------------------------------------------------------------
-- 演習問題 155：Prod の結合（相互変換版）★★★☆
-- (α×β)×γ  と  α×(β×γ) の間の相互変換
--
-- ヒント：
--   - obtain ⟨ab, c⟩ := p; obtain ⟨a,b⟩ := ab
--   - 往復は Prod を分解して rfl が多い
example :
  ∃ assocL : (α × β) × γ → α × (β × γ),
  ∃ assocR : α × (β × γ) → (α × β) × γ,
    (∀ p : (α × β) × γ, assocR (assocL p) = p) ∧
    (∀ q : α × (β × γ), assocL (assocR q) = q) := by

  refine ⟨?assocL, ?assocR, ?hLeft, ?hRight⟩

  -- assocL
  intro a
  obtain ⟨a1, a2⟩ := a
  obtain ⟨a3, a4⟩ := a1
  exact (a3, (a4, a2))

  -- assocR
  intro b
  obtain ⟨b1, b2⟩ := b
  obtain ⟨b3, b4⟩ := b2
  exact ((b1, b3), b4)

  -- hLeft
  intro c
  obtain ⟨⟨c1, c2⟩, c3⟩ := c
  dsimp

  -- hRight
  intro d
  obtain ⟨d1, ⟨d2, d3⟩⟩ := d
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 156：量化子つき「ならば」の古典分解 ★★★★
-- (∀x, P x) → Q  は  (∃x, ¬P x) ∨ Q  と同じ（古典）
--
-- ヒント：
--   classical
--   1) (A → Q) ↔ (¬A ∨ Q) を使う発想
--   2) ¬(∀x,Px) ↔ ∃x, ¬P x（古典）
example (P : α → Prop) (Q : Prop) :
    ((∀ x, P x) → Q) ↔ (∃ x, ¬ P x) ∨ Q := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a

  suffices b : (∃ x, ¬P x) ∨ ∀ (x : α), P x from by
    cases b with
    | inl b1 =>
      exact Or.inl b1
    | inr b2 =>
      apply Or.inr
      apply a
      exact b2

  by_cases c : ∀ (x : α), P x
  right
  exact c
  left
  apply Classical.byContradiction
  intro d
  apply c
  intro e
  apply Classical.byContradiction
  intro f
  apply d
  exists e

  -- hRight
  intro a
  intro b
  cases a with
  | inl a1 =>
    obtain ⟨a2, a3⟩ := a1
    apply Classical.byContradiction
    intro c
    apply a3
    apply b
  | inr a4 =>
    exact a4

--------------------------------------------------------------------------------
-- 演習問題 157：Option 関数の外延性（分解版）★★★☆
-- f none と f (some a) の値が全部一致すれば f=g
--
-- ヒント：
--   funext o; cases o with | none => ... | some a => ...
example (f g : Option α → β) :
    f none = g none →
    (∀ a, f (some a) = g (some a)) →
    f = g := by

  intro a b
  funext c
  cases c with
  | none =>
    exact a
  | some c1 =>
    apply b

--------------------------------------------------------------------------------
-- 演習問題 158：Sum 関数の外延性（分解版）★★★☆
-- inl と inr の場合で一致すれば関数として一致
--
-- ヒント：
--   funext s; cases s with | inl a => ... | inr b => ...
example (f g : Sum α β → γ) :
    (∀ a, f (Sum.inl a) = g (Sum.inl a)) →
    (∀ b, f (Sum.inr b) = g (Sum.inr b)) →
    f = g := by

  intro a b
  funext c
  cases c with
  | inl c1 =>
    apply a
  | inr c2 =>
    apply b

--------------------------------------------------------------------------------
-- 演習問題 159：∃ と ∀ を合成して “中身付き∃” を作る ★★★☆
-- (∃x, P x) と (∀x, P x → Q x) から ∃x, P x ∧ Q x
--
-- ヒント：
--   obtain ⟨x, hxP⟩ := hex
--   have hxQ : Q x := h x hxP
--   exact ⟨x, ⟨hxP, hxQ⟩⟩
example (P Q : α → Prop) :
    (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, P x ∧ Q x := by

  intro a b
  obtain ⟨a1, a2⟩ := a
  have a3 : Q a1 := b a1 a2
  exact ⟨a1, ⟨a2, a3⟩⟩

--------------------------------------------------------------------------------
-- 演習問題 160：存在つき含意の否定（Inhabited 必須・古典）★★★★★
-- 「あるxで(Px→Q)が成り立つ」ことが不可能なら：
--   全員 Px が成り立ち、かつ Q は偽
--
-- ※ α が空型だと壊れるので [Inhabited α] を付けています（解けない命題を避けるため）
--
-- ヒント：
--   classical
--   (→) で
--     - ¬Q：Q を仮定すると default を witness にして (P default → Q) を作れて矛盾
--     - ∀x, P x：任意の x で ¬P x を仮定すると (P x → Q) が作れて矛盾
--   (←) は、⟨∀x Px, ¬Q⟩ から ∃x(Px→Q) を仮定して矛盾
example (P : α → Prop) (Q : Prop) [Inhabited α] :
    ¬ (∃ x, P x → Q) ↔ (∀ x, P x) ∧ ¬ Q := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  refine ⟨?hForall, ?hNotQ⟩

  -- hForall
  intro b
  apply Classical.byContradiction
  intro c
  apply a
  exists b
  intro d
  apply Classical.byContradiction
  intro e
  apply c
  exact d

  -- hNotQ
  intro e
  apply a
  exists Inhabited.default
  intro f
  exact e

  -- hRight
  intro a b
  obtain ⟨b1, b2⟩ := b
  obtain ⟨a1, a2⟩ := a
  apply a2
  apply b2
  apply a1

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 161〜165（難易度アップ / Nat・Listなし）
-- 量化子×否定（18・84系の応用） + Sum/Prod/関数の外延性
-- ※ import Mathlib なし / Equiv なしでも解ける形式
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 演習問題 161：¬∀(P ∨ Q) の“中身”（古典）★★★★★
-- ¬(∀x, P x ∨ Q) ↔ (∃x, ¬P x) ∧ ¬Q
--
-- ヒント（→）：
--   1) ¬Q：Q を仮定すると ∀x, P x ∨ Q が作れて矛盾
--   2) ∃x, ¬P x：背理法で「∃x, ¬P x が無い」を仮定し、
--      各 x で P x を背理法で出して ∀x, P x ∨ Q を作って矛盾
-- ヒント（←）：
--   ⟨x, ¬P x⟩ を取り出して、その x の (P x ∨ Q) を cases で潰す
example (P : α → Prop) (Q : Prop) :
    ¬ (∀ x, P x ∨ Q) ↔ (∃ x, ¬ P x) ∧ ¬ Q := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  refine ⟨?hExist, ?hNotQ⟩

  -- hExist
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  have d : ∀ (x : α), P x := by
    intro d1
    apply Classical.byContradiction
    intro d2
    apply b
    exists d1
  have e : P c := by
    apply d
  left
  exact e

  -- hNotQ
  intro b
  apply a
  intro c
  right
  exact b

  -- hRight
  intro a b
  obtain ⟨a1, a2⟩ := a
  apply a2
  obtain ⟨a3, a4⟩ := a1
  have b : P a3 ∨ Q := by
    apply b
  cases b with
  | inl b1 =>
    apply Classical.byContradiction
    intro b2
    apply a4
    exact b1
  | inr b2 =>
    exact b2

--------------------------------------------------------------------------------
-- 演習問題 162：∃の“弱い復元”（直観主義でOK）★★★★
-- ¬(∀x, ¬P x) ↔ ¬¬(∃x, P x)
--
-- ヒント（→）：
--   intro hnotall; intro hnotex; apply hnotall; intro x hp; apply hnotex; exact ⟨x,hp⟩
-- ヒント（←）：
--   intro hnnex; intro hallnot; apply hnnex; intro hex; obtain ⟨x,hp⟩ := hex; exact hallnot x hp
example (P : α → Prop) :
    ¬ (∀ x, ¬ P x) ↔ ¬¬ (∃ x, P x) := by
  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a b
  apply a
  intro c
  intro d
  apply b
  exists c

  -- hRight
  intro a b
  apply a
  intro c
  obtain ⟨c1, c2⟩ := c
  apply a
  intro d
  have e : ¬P c1 := by
    apply b
  apply e
  exact c2

--------------------------------------------------------------------------------
-- 演習問題 163：分配（Sum×）の同型（相互変換＋往復恒等）★★★★☆
-- (Sum α β) × γ  と  Sum (α×γ) (β×γ) の相互変換を作って往復が恒等になることを示す
--
-- ヒント：
--   dist : (s,c) を受けて、s が inl なら inl (a,c)、inr なら inr (b,c)
--   factor : inl (a,c) ↦ (inl a, c),  inr (b,c) ↦ (inr b, c)
--   往復は cases して rfl が多い
example :
  ∃ dist : (Sum α β) × γ → Sum (α × γ) (β × γ),
  ∃ factor : Sum (α × γ) (β × γ) → (Sum α β) × γ,
    (∀ p : (Sum α β) × γ, factor (dist p) = p) ∧
    (∀ s : Sum (α × γ) (β × γ), dist (factor s) = s) := by

  refine ⟨?dist, ?factor, ?hLeft, ?hRight⟩

  -- dist
  intro a
  obtain ⟨a1, a2⟩ := a
  cases a1 with
  | inl a3 =>
    exact Sum.inl (a3, a2)
  | inr a4 =>
    exact Sum.inr (a4, a2)

  -- factor
  intro b
  cases b with
  | inl b1 =>
    obtain ⟨b2, b3⟩ := b1
    exact (Sum.inl b2, b3)
  | inr b4 =>
    obtain ⟨b5, b6⟩ := b4
    exact (Sum.inr b5, b6)

  -- hLeft
  intro c
  obtain ⟨c1, c2⟩ := c
  cases c1 with
  | inl c3 =>
    dsimp
  | inr c4 =>
    dsimp

  -- hRight
  intro d
  cases d with
  | inl d1 =>
    obtain ⟨d2, d3⟩ := d1
    dsimp
  | inr d4 =>
    obtain ⟨d5, d6⟩ := d4
    dsimp

--------------------------------------------------------------------------------
-- 演習問題 164：関数→積 の同型（相互変換＋往復恒等）★★★★☆
-- (α → β×γ)  と  (α→β)×(α→γ)
--
-- ヒント：
--   toPair h := ⟨fun x => (h x).1, fun x => (h x).2⟩
--   fromPair ⟨f,g⟩ := fun x => (f x, g x)
--
-- 逆向きの証明のコツ：
--   - 関数の等式は funext
--   - (h x) : β×γ を cases すると (mk _ _) になって rfl が効きやすい
--   - ペアの等式は Prod.ext か、cases fg して rfl
example :
  ∃ toPair : (α → β × γ) → (α → β) × (α → γ),
  ∃ fromPair : ((α → β) × (α → γ)) → (α → β × γ),
    (∀ h : α → β × γ, fromPair (toPair h) = h) ∧
    (∀ fg : (α → β) × (α → γ), toPair (fromPair fg) = fg) := by

  refine ⟨?toPair, ?fromPair, ?hLeft, ?hRight⟩

  -- toPair
  intro a
  refine ⟨?first, ?second⟩

  -- first
  intro a1
  exact (a a1).1

  -- second
  intro a2
  exact (a a2).2

  -- fromPair
  intro b
  obtain ⟨b1, b2⟩ := b
  intro c
  exact (b1 c, b2 c)

  -- hLeft
  intro d
  funext e
  dsimp

  -- hRight
  intro f
  obtain ⟨f1, f2⟩ := f
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 165：¬∃(P ∨ Q) の“中身”（Inhabited を使う）★★★★★
-- ¬(∃x, P x ∨ Q) ↔ (∀x, ¬P x) ∧ ¬Q
--
-- ※ ¬Q を出すのに witness が必要なので [Inhabited α] を付ける
--
-- ヒント（→）：
--   - ∀x, ¬P x：任意の x と hp:P x から ⟨x, Or.inl hp⟩ を作って矛盾
--   - ¬Q：Q を仮定すると default を使って ⟨default, Or.inr hQ⟩ を作って矛盾
-- ヒント（←）：
--   obtain ⟨x, hx⟩ := hex
--   cases hx with | inl hp => ... | inr hQ => ...
example (P : α → Prop) (Q : Prop) [Inhabited α] :
    ¬ (∃ x, P x ∨ Q) ↔ (∀ x, ¬ P x) ∧ ¬ Q := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  refine ⟨?hForall, ?hNotQ⟩

  -- hForall
  intro b c
  apply a
  exists b
  left
  exact c

  -- hNotQ
  intro b
  apply a
  exists Inhabited.default
  right
  exact b

  -- hRight
  intro a b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  apply a2
  have c : ¬P b1 := by
    apply a1
  cases b2 with
  | inl b3 =>
    apply Classical.byContradiction
    intro d
    apply c
    exact b3
  | inr b4 =>
    exact b4

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 166〜170（さらに難しめ / Nat・Listなし）
-- 量化子×否定（84/18/12系の合成） + 相互変換（≃の代替形式） + funext(2回) + Subtype/Nonempty
-- ※ import Mathlib なし / Equiv なしでOK
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 演習問題 166：否定の押し込み（∀→∀ の否定を “反例つき” に）★★★★★
-- ¬(∀x, P x → ∀y, R x y) ↔ ∃x, P x ∧ ∃y, ¬R x y
--
-- ヒント：
--   classical
--   (→) 84で「∃x, ¬(P x → ∀y, R x y)」へ
--       12で「P x ∧ ¬(∀y, R x y)」へ
--       84で「∃y, ¬R x y」へ
--   (←) は取り出して矛盾（直観主義でOK）
example (P : α → Prop) (R : α → β → Prop) :
    ¬ (∀ x, P x → ∀ y, R x y) ↔ ∃ x, P x ∧ ∃ y, ¬ R x y := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  intro d e
  apply Classical.byContradiction
  intro f
  apply b
  exists c
  refine ⟨d, ?hExist⟩
  exists e

  -- hRight
  intro a b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨a3, a4⟩ := a2
  obtain ⟨a5, a6⟩ := a4
  apply a6
  have d : P a1 → ∀ (y : β), R a1 y := by
    apply b
  have e : ∀ (y : β), R a1 y := by
    apply d
    exact a3
  apply e

--------------------------------------------------------------------------------
-- 演習問題 167：否定の押し込み（「万能な証人がいない」→「各候補に反例」）★★★★★
-- ¬(∃x, P x ∧ ∀y, R x y) ↔ ∀x, P x → ∃y, ¬R x y
--
-- ヒント：
--   classical
--   (→) 任意のxで P x を仮定 → 「¬(∀y, R x y)」を作る → 84で ∃y, ¬R x y
--   (←) 反例yを取って、∀y と衝突させる
example (P : α → Prop) (R : α → β → Prop) :
    ¬ (∃ x, P x ∧ ∀ y, R x y) ↔ ∀ x, P x → ∃ y, ¬ R x y := by

  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro a b c
  apply Classical.byContradiction
  intro d
  apply a
  exists b
  refine ⟨c, ?hForall⟩
  intro e
  apply Classical.byContradiction
  intro f
  apply d
  exists e

  -- hRight
  intro a b
  obtain ⟨b1, b2⟩ := b
  obtain ⟨b3, b4⟩ := b2
  have c: P b1 → ∃ y, ¬R b1 y := by
    apply a
  have d : ∃ y, ¬R b1 y := by
    apply c
    exact b3
  obtain ⟨d1, d2⟩ := d
  apply d2
  apply b4

--------------------------------------------------------------------------------
-- 演習問題 168：2引数関数 → 積 の分解（相互変換＋往復恒等）★★★★☆
-- (α → β → (γ×δ)) と (α→β→γ)×(α→β→δ) の間の相互変換を作り、
-- 往復すると元に戻ることを示す（164 の “2引数版”）
--
-- ヒント：
--   toPair h := ⟨fun a b => (h a b).1, fun a b => (h a b).2⟩
--   fromPair ⟨f,g⟩ := fun a b => (f a b, g a b)
--   左右の恒等は funext を2回（a,b）使う
example :
  ∃ toPair : (α → β → (γ × δ)) → (α → β → γ) × (α → β → δ),
  ∃ fromPair : ((α → β → γ) × (α → β → δ)) → (α → β → (γ × δ)),
    (∀ h : α → β → (γ × δ), fromPair (toPair h) = h) ∧
    (∀ fg : (α → β → γ) × (α → β → δ), toPair (fromPair fg) = fg) := by

  refine ⟨?toPair, ?fromPair, ?hLeft, ?hRight⟩

  -- toPair
  intro a
  refine ⟨?first, ?second⟩

  -- first
  intro b c
  exact (a b c).1

  -- second
  intro d e
  exact (a d e).2

  -- fromPair
  intro f g h
  exact (f.1 g h, f.2 g h)

  -- hLeft
  intro i
  funext j k
  dsimp

  -- hRight
  intro l
  obtain ⟨l1, l2⟩ := l
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 169：Subtype と ∃ の対応（新系統：Nonempty を使う）★★★★
-- Nonempty {x // P x} ↔ ∃x, P x
--
-- ヒント：
--   (→) obtain ⟨s⟩ := h;  s : {x // P x} から ⟨s.1, s.2⟩
--   (←) obtain ⟨x, hx⟩ := hex; exact ⟨⟨x, hx⟩⟩
example (P : α → Prop) :
    Nonempty { x : α // P x } ↔ ∃ x, P x := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  obtain ⟨s⟩ := a
  exact ⟨s.1, s.2⟩

  -- hRight
  intro a
  obtain ⟨a1, a2⟩ := a
  exact ⟨⟨a1, a2⟩⟩

--------------------------------------------------------------------------------
-- 演習問題 170：全称含意の“or 形”への変形（古典）★★★★☆
-- (∀x, P x → Q) ↔ (¬(∃x, P x) ∨ Q)
--
-- ヒント：
--   classical
--   (→) は by_cases q : Q で分岐（qなら右、¬qなら ¬∃xPx を作る）
--   (←) は cases (¬∃xPx ∨ Q) で分岐（¬∃なら hp から False を作って Q、Qなら即）
example (P : α → Prop) (Q : Prop) :
    (∀ x, P x → Q) ↔ (¬ (∃ x, P x) ∨ Q) := by

  refine ⟨?hLeft, ?hRight⟩
  -- hLeft
  intro a

  by_cases b : Q
  right
  exact b
  left
  intro c
  obtain ⟨c1, c2⟩ := c
  apply b
  have d : P c1 → Q := by
    apply a
  apply d
  exact c2

  -- hRight
  intro a b c
  by_cases d: Q
  exact d
  have e : (¬∃ x, P x) := by
    intro e1
    obtain ⟨e2, e3⟩ := e1
    cases a with
    | inl a1 =>
      apply a1
      exists e2
    | inr a2 =>
      apply d
      exact a2
  apply Classical.byContradiction
  intro f
  apply e
  exists b

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 演習問題 171〜175（難易度アップ / Nat・Listなし / Equivなし）
-- 量化子×否定（84/18/12系） + 「相互変換＋往復恒等」 + funext 多段 + 4分岐の Sum パズル
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 演習問題 171：¬∀(P∨Q) の “x依存版”（古典）★★★★★
-- ¬(∀x, P x ∨ Q x) ↔ ∃x, ¬P x ∧ ¬Q x
--
-- ヒント：
--   classical
--   (→) 84系で ∃x, ¬(P x ∨ Q x) を作る → ¬(∨) から ∧ を作る
--   (←) obtain ⟨x, hnp, hnq⟩ := ...; intro hall; have := hall x; cases ... で矛盾
example (P Q : α → Prop) :
    ¬ (∀ x, P x ∨ Q x) ↔ ∃ x, ¬ P x ∧ ¬ Q x := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  apply Classical.byContradiction
  intro b
  apply a
  intro c
  apply Classical.byContradiction
  intro d
  apply b
  exists c
  constructor
  intro e
  apply d
  left
  exact e
  intro f
  apply d
  right
  exact f

  -- hRight
  intro a b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨a3, a4⟩ := a2
  have c : P a1 ∨ Q a1 := by
    apply b
  cases c with
  | inl c1 =>
    apply a3
    exact c1
  | inr c2 =>
    apply a4
    exact c2

--------------------------------------------------------------------------------
-- 演習問題 172：含意＋“or(定数)” の否定を分解（古典）★★★★★
-- ¬(∀x, P x → (Q x ∨ A)) ↔ (∃x, P x ∧ ¬Q x) ∧ ¬A
--
-- ヒント：
--   (→)
--     1) ¬A は直観主義で出せる：A を仮定すると ∀x, P x → (Q x ∨ A) が作れる
--     2) ∃x, P x ∧ ¬Q x は古典で：
--        84系で ∃x, ¬(P x → (Q x ∨ A)) を作り、
--        12系で P x ∧ ¬(Q x ∨ A) を作り、そこから ¬Q x を取り出す
--   (←)
--     obtain ⟨x, hp, hnq⟩ := ...
--     intro hall; have := hall x hp; cases ... で A or Q を潰す
example (P Q : α → Prop) (A : Prop) :
    ¬ (∀ x, P x → (Q x ∨ A)) ↔ (∃ x, P x ∧ ¬ Q x) ∧ ¬ A := by

  refine ⟨?hLeft, ?hRight⟩

  -- hLeft
  intro a
  refine ⟨?hExist, ?hNotA⟩

  -- hExist
  apply Classical.byContradiction
  intro b
  apply a
  intro c d
  have e : ¬(P c ∧ ¬Q c) := by
    intro e1
    apply b
    exists c
  apply Classical.byContradiction
  intro f
  apply e
  constructor
  exact d
  intro g
  apply f
  left
  exact g

  -- hNotA
  intro b
  apply a
  intro c d
  right
  exact b

  -- hRight
  intro a b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨a3, a4⟩ := a1
  obtain ⟨a5, a6⟩ := a4
  apply a2
  have d : P a3 → Q a3 ∨ A := by
    apply b
  have e : Q a3 ∨ A := by
    apply d
    exact a5
  cases e with
  | inl e1 =>
    apply Classical.byContradiction
    intro e2
    apply a6
    exact e1
  | inr e3 =>
    exact e3

--------------------------------------------------------------------------------
-- 演習問題 173：4分岐の分配（Sum×Sum → 4ケースの Sum）（相互変換＋往復恒等）★★★★☆
-- (Sum α β) × (Sum γ δ)  は 4通りに場合分けできる
-- それを「ネストした Sum」で表現して、to/from を作り往復が恒等になることを示せ
--
-- 右側の型：
--   Sum (α×γ) (Sum (α×δ) (Sum (β×γ) (β×δ)))
--
-- ヒント：
--   - dist: p.1 と p.2 を cases して 4ケースで inl/inr を組み立てる
--   - factor: 右側を cases して元の (Sum α β, Sum γ δ) に戻す
--   - 往復は cases して rfl が基本
example :
  ∃ dist :
      (Sum α β × Sum γ δ) →
        Sum (α × γ) (Sum (α × δ) (Sum (β × γ) (β × δ))),
  ∃ factor :
      Sum (α × γ) (Sum (α × δ) (Sum (β × γ) (β × δ))) →
        (Sum α β × Sum γ δ),
    (∀ p,
        factor (dist p) = p) ∧
    (∀ s,
        dist (factor s) = s) := by

  refine ⟨?dist, ?factor, ?hLeft, ?hRight⟩

  -- dist
  intro a
  obtain ⟨a1, a2⟩ := a
  cases a1 with
  | inl a3 =>
    cases a2 with
    | inl a4 =>
      exact Sum.inl (a3, a4)
    | inr a5 =>
      exact Sum.inr (Sum.inl (a3, a5))
  | inr a6 =>
    cases a2 with
    | inl a4 =>
      exact Sum.inr (Sum.inr (Sum.inl (a6, a4)))
    | inr a5 =>
      exact Sum.inr (Sum.inr (Sum.inr (a6, a5)))

  -- factor
  intro b
  cases b with
  | inl b1 =>
    obtain ⟨b2, b3⟩ := b1
    exact (Sum.inl b2, Sum.inl b3)
  | inr b4 =>
    cases b4 with
    | inl b5 =>
      obtain ⟨b6, b7⟩ := b5
      exact (Sum.inl b6, Sum.inr b7)
    | inr b8 =>
      cases b8 with
      | inl b9 =>
        obtain ⟨b10, b11⟩ := b9
        exact (Sum.inr b10, Sum.inl b11)
      | inr b12 =>
        obtain ⟨b13, b14⟩ := b12
        exact (Sum.inr b13, Sum.inr b14)

  -- hLeft
  intro c
  obtain ⟨c1, c2⟩ := c
  cases c1 with
  | inl c3 =>
    cases c2 with
    | inl c4 =>
      dsimp
    | inr c5 =>
      dsimp
  | inr c6 =>
    cases c2 with
    | inl c4 =>
      dsimp
    | inr c5 =>
      dsimp

  -- hRight
  intro d
  cases d with
  | inl d1 =>
    obtain ⟨d2, d3⟩ := d1
    dsimp
  | inr d4 =>
    cases d4 with
    | inl d5 =>
      obtain ⟨d6, d7⟩ := d5
      dsimp
    | inr d8 =>
      cases d8 with
      | inl d9 =>
        obtain ⟨d10, d11⟩ := d9
        dsimp
      | inr d12 =>
        obtain ⟨d13, d14⟩ := d12
        dsimp

--------------------------------------------------------------------------------
-- 演習問題 174：Sum を入力に、Prod を返す関数の分解（相互変換＋往復恒等）★★★★★
-- (Sum α β → γ×δ) から「4本の関数」に分解せよ（142 と 164 の合体版）
--
-- 右側の型：
--   ((α→γ)×(β→γ)) × ((α→δ)×(β→δ))
--
-- ヒント：
--   - toBig: h (inl a) の .1/.2 と、h (inr b) の .1/.2 を集める
--   - fromBig: s を cases して、対応する関数を呼んでペアを作る
--   - (fromBig (toBig h) = h) は funext s; cases s <;> rfl が定石
--   - (toBig (fromBig fg) = fg) は Prod.ext を何回か + funext
example :
  ∃ toBig :
      (Sum α β → (γ × δ)) →
        ((α → γ) × (β → γ)) × ((α → δ) × (β → δ)),
  ∃ fromBig :
      (((α → γ) × (β → γ)) × ((α → δ) × (β → δ))) →
        (Sum α β → (γ × δ)),
    (∀ h, fromBig (toBig h) = h) ∧
    (∀ fg, toBig (fromBig fg) = fg) := by

  refine ⟨?toBig, ?fromBig, ?hLeft, ?hRight⟩

  -- toBig
  intro a
  refine ⟨?first, ?second⟩
  -- first
  refine ⟨?f1, ?f2⟩
  -- f1
  intro b
  exact (a (Sum.inl b)).1
  -- f2
  intro c
  exact (a (Sum.inr c)).1
  -- second
  refine ⟨?g1, ?g2⟩
  -- g1
  intro d
  exact (a (Sum.inl d)).2
  -- g2
  intro e
  exact (a (Sum.inr e)).2

  -- fromBig
  intro f
  obtain ⟨f1, f2⟩ := f
  obtain ⟨f11, f12⟩ := f1
  obtain ⟨f21, f22⟩ := f2
  intro g
  cases g with
  | inl g1 =>
    exact (f11 g1, f21 g1)
  | inr g2 =>
    exact (f12 g2, f22 g2)

  -- hLeft
  intro h
  funext i
  cases i with
  | inl i1 =>
    dsimp
  | inr i2 =>
    dsimp

  -- hRight
  intro j
  obtain ⟨j1, j2⟩ := j
  obtain ⟨j11, j12⟩ := j1
  obtain ⟨j21, j22⟩ := j2
  dsimp

--------------------------------------------------------------------------------
-- 演習問題 175：∀(P∨Q) から “∀P か ∃Q” を引き出す（古典）★★★★★
-- (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∃x, Q x)
--
-- ヒント：
--   classical
--   by_cases hq : ∃ x, Q x
--   · right; exact hq
--   · left; intro x; have hx := hall x; cases hx with
--       | inl hp => exact hp
--       | inr hqx => exfalso; apply hq; exact ⟨x, hqx⟩
example (P Q : α → Prop) :
    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∃ x, Q x) := by

  intro a
  by_cases b : ∃ x, Q x
  right
  exact b
  left
  intro c
  have d : P c ∨ Q c := by
    apply a
  cases d with
  | inl d1 =>
    exact d1
  | inr d2 =>
    apply Classical.byContradiction
    intro e
    apply b
    exists c

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 176〜180（観点チェンジ：関数の合成 / 単射・全射 / 左逆・右逆）
-- ※ import Mathlib なし / Nat・Listなし
--------------------------------------------------------------------------------

variable {α β γ δ : Type}

--------------------------------------------------------------------------------
-- 演習問題 176：関数合成の結合法則（funext 練習）★★★☆
-- 自作 comp が結合的であることを示せ
--
-- ヒント：
--   funext x; rfl
def myComp (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

example (f : α → β) (g : β → γ) (h : γ → δ) :
    myComp h (myComp g f) = myComp (myComp h g) f := by

  funext a
  dsimp [myComp]

--------------------------------------------------------------------------------
-- 演習問題 177：左逆があれば単射（Injective）★★★☆
-- g が f の左逆：∀x, g(f x)=x なら f は単射
--
-- ヒント：
--   intro x y hxy
--   have : g (f x) = g (f y) := by rw [hxy]
--   calc
--     x = g (f x) := (hleft x).symm
--     _ = g (f y) := this
--     _ = y := hleft y
def Injective (f : α → β) : Prop :=
  ∀ ⦃x y : α⦄, f x = f y → x = y

def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x : α, g (f x) = x

example (f : α → β) (g : β → α) :
    LeftInverse g f → Injective f := by
  dsimp [LeftInverse]
  dsimp [Injective]
  intro a b c d
  have e : g (f b) = g (f c) := by
    rw [d]
  have h : g (f b) = b := by
    apply a
  have i : g (f c) = c := by
    apply a
  rw [←h]
  rw [←i]
  exact e

--------------------------------------------------------------------------------
-- 演習問題 178：右逆があれば全射（Surjective）★★★
-- g が f の右逆：∀y, f(g y)=y なら f は全射
--
-- ヒント：
--   intro y; refine ⟨g y, ?_⟩; exact (hright y)
def Surjective (f : α → β) : Prop :=
  ∀ y : β, ∃ x : α, f x = y

def RightInverse (g : β → α) (f : α → β) : Prop :=
  ∀ y : β, f (g y) = y

example (f : α → β) (g : β → α) :
    RightInverse g f → Surjective f := by
  dsimp [Surjective, RightInverse]
  intro a b
  have c : α := by
    apply g
    exact b
  have d : f (g b) = b := by
    apply a
  exists (g b)

--------------------------------------------------------------------------------
-- 演習問題 179：Prod の swap は 2回で元に戻る（cases 練習）★★★
--
-- ヒント：
--   cases p with | mk a b => rfl
def swap (p : α × β) : β × α :=
  (p.2, p.1)

example (p : α × β) : swap (swap p) = p := by
  dsimp [swap]

--------------------------------------------------------------------------------
-- 演習問題 180：全射なら「右からの打ち消し」ができる（funext + obtain）★★★★☆
-- f が全射で、g∘f と h∘f が点ごとに一致するなら、g=h
--
-- 直感：
--   任意の y:β に対し、全射性で y = f x となる x を取れる。
--   すると g y = g (f x) = h (f x) = h y。
--
-- ヒント（短い解法）：
--   intro hsurj hcomp
--   funext y
--   obtain ⟨x, rfl⟩ := hsurj y
--   exact hcomp x
example (f : α → β) (g h : β → γ) :
    Surjective f →
    (∀ x : α, g (f x) = h (f x)) →
    g = h := by
  dsimp [Surjective]
  intro a b
  funext c
  have d: ∃ x, f x = c := by
    apply a
  obtain ⟨d1, d2⟩ := d
  have e : g (f d1) = h (f d1) := by
    apply b
  rw [←d2]
  exact e

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 181〜185（関数・逆・単射/全射：少し難しめ）
-- ※ 前回定義した myComp / Injective / Surjective / LeftInverse / RightInverse を使います
--------------------------------------------------------------------------------
variable {α β γ : Type}
--------------------------------------------------------------------------------
-- 演習問題 181：単射なら「左からの打ち消し」ができる ★★★★
-- Injective f と、∀x, f (g x) = f (h x) から g = h
--
-- ヒント:
--   intro hinj hcomp
--   funext x
--   apply hinj
--   exact hcomp x
example (f : α → β) (g h : γ → α) :
    Injective f → (∀ x : γ, f (g x) = f (h x)) → g = h := by
  dsimp [Injective]
  intro a b
  funext c
  have d : f (g c) = f (h c) := by
    apply b
  have e :  f (g c) = f (h c) → g c = h c := by
    apply a
  apply e
  exact d

--------------------------------------------------------------------------------
-- 演習問題 182：Bijective（単射∧全射）の合成 ★★★★☆
-- Bijective f と Bijective g から Bijective (g∘f)
--
-- ヒント:
--   Injective 部分：g(f x)=g(f y) → f x=f y → x=y
--   Surjective 部分：z:γ に対して g の全射で y:β を取り、f の全射で x:α を取る
def Bijective (f : α → β) : Prop :=
  Injective f ∧ Surjective f

example (f : α → β) (g : β → γ) :
    Bijective f → Bijective g → Bijective (myComp g f) := by
  dsimp [Bijective, Injective, Surjective, myComp]
  intro a b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b

  refine ⟨?one, ?two⟩

  -- one
  intro c d e
  have h : (f c) = (f d) → c = d := by
    apply a1
  have i : g (f c) = g (f d) → c = d := by
    intro g1
    apply h
    apply b1
    exact g1
  apply i
  exact e

  -- two
  intro c
  have d : ∃ x, g x = c := by
    apply b2
  obtain ⟨d1, d2⟩ := d
  have e : ∃ x, f x = d1 := by
    apply a2
  obtain ⟨e1, e2⟩ := e
  exists e1
  rw [e2]
  rw [d2]

--------------------------------------------------------------------------------
-- 演習問題 183：全射から「右逆」を作れる（Choice を使う）★★★★★
-- Surjective f → ∃ g, RightInverse g f
--
-- 新ネタ：Classical.choose / Classical.choose_spec を使う練習
-- ヒント:
--   classical
--   intro hsurj
--   refine ⟨fun y => Classical.choose (hsurj y), ?_⟩
--   intro y
--   exact Classical.choose_spec (hsurj y)
example (f : α → β) :
    Surjective f → ∃ g : β → α, RightInverse g f := by

  classical

  dsimp [Surjective, RightInverse]
  intro a
  refine ⟨?one,?two⟩

  -- one
  intro b
  exact Classical.choose (a b)

  -- two
  intro c
  exact Classical.choose_spec (a c)

--------------------------------------------------------------------------------
-- 演習問題 184：右逆 + 単射 ⇒ 左逆 ★★★★☆
-- Injective f と RightInverse g f があれば LeftInverse g f が出る
--
-- 直感:
--   y := f x とおくと、RightInverse で f (g (f x)) = f x
--   Injective で g (f x) = x
--
-- ヒント:
--   intro hinj hright x
--   apply hinj
--   exact hright (f x)
example (f : α → β) (g : β → α) :
    Injective f → RightInverse g f → LeftInverse g f := by
  dsimp [Injective, RightInverse, LeftInverse]
  intro a b c
  have d :f (g (f c)) = f c → g (f c) = c := by
    apply a
  apply d
  apply b

--------------------------------------------------------------------------------
-- 演習問題 185：左逆 + 全射 ⇒ 右逆 ★★★★☆
-- Surjective f と LeftInverse g f があれば RightInverse g f が出る
--
-- 直感:
--   y:β を任意に取る
--   全射で y = f x となる x を取る
--   左逆で g (f x) = x
--   よって f (g y) = y
--
-- ヒント:
--   intro hsurj hleft y
--   obtain ⟨x, hx⟩ := hsurj y
--   rw [← hx]
--   have : g (f x) = x := hleft x
--   rw [this]
--   rfl
example (f : α → β) (g : β → α) :
    Surjective f → LeftInverse g f → RightInverse g f := by
  dsimp [Surjective, LeftInverse, RightInverse]
  intro a b c
  have d: ∃ x, f x = c := by
    apply a
  obtain ⟨d1, d2⟩ := d
  have e: g (f d1) = d1 := by
    apply b
  rw [←d2]
  rw [e]

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 演習問題 186〜190（関数・合成・単射全射・逆：少し濃く）
-- ※ Nat / List なし, import Mathlib なし
--------------------------------------------------------------------------------

variable {α β γ : Type}

-- 前提：あなたのファイルに以下が既にある想定（なければ貼ってください）
-- def myComp (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
-- def Injective (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y
-- def Surjective (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y
-- def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x : α, g (f x) = x
-- def RightInverse (g : β → α) (f : α → β) : Prop := ∀ y : β, f (g y) = y
-- def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

--------------------------------------------------------------------------------
-- 演習問題 186：合成の単位元（funext 練習）★★★
-- myComp id f = f と myComp g id = g
--
-- ヒント：funext x; rfl
example (f : α → β) : myComp (fun y : β => y) f = f := by
  -- TODO
  sorry

example (g : β → γ) : myComp g (fun x : β => x) = g := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 187：単射の合成（直観主義OK）★★★☆
-- Injective f と Injective g なら Injective (g∘f)
--
-- ヒント：
--   intro x y h
--   apply hf
--   apply hg
--   exact h
example (f : α → β) (g : β → γ) :
    Injective f → Injective g → Injective (myComp g f) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 188：全射の合成（直観主義OK）★★★☆
-- Surjective f と Surjective g なら Surjective (g∘f)
--
-- ヒント：
--   intro z
--   obtain ⟨y, hy⟩ := hgs z
--   obtain ⟨x, hx⟩ := hfs y
--   refine ⟨x, ?_⟩
--   dsimp [myComp]; rw [hx]; exact hy
example (f : α → β) (g : β → γ) :
    Surjective f → Surjective g → Surjective (myComp g f) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 189：全単射なら「両側逆」が取れる（Choiceあり・古典）★★★★★
-- Bijective f → ∃ g, LeftInverse g f ∧ RightInverse g f
--
-- ヒント：
--   classical
--   obtain ⟨hinj, hsurj⟩ := hbij
--   let g : β → α := fun y => Classical.choose (hsurj y)
--   have hright : RightInverse g f := by
--     intro y; exact Classical.choose_spec (hsurj y)
--   have hleft : LeftInverse g f := by
--     intro x
--     -- hinj を使って f (g (f x)) = f x から g (f x) = x を出す
--     apply hinj
--     -- 右逆を (f x) に適用
--     exact hright (f x)
--   exact ⟨g, hleft, hright⟩
example (f : α → β) :
    Bijective f → ∃ g : β → α, LeftInverse g f ∧ RightInverse g f := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 演習問題 190：右逆の一意性（Injective があると一意）★★★★☆
-- Injective f かつ RightInverse g f かつ RightInverse h f → g = h
--
-- ヒント：
--   funext y
--   apply hinj
--   -- f (g y) = y と f (h y) = y をつないで同値にする
--   calc
--     f (g y) = y := hrg y
--     _ = f (h y) := (hrh y).symm
example (f : α → β) (g h : β → α) :
    Injective f → RightInverse g f → RightInverse h f → g = h := by
  -- TODO
  sorry

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
