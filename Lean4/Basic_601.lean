--------------------------------------------------------------------------------
-- Basic_601.lean
-- 演習問題 601〜650（support/boolean化/keys付き縮約/残余による安全設計）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 551〜600 は Basic_551 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_551

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（support / keys 付き Rel 合成）
--------------------------------------------------------------------------------

-- WRel を「正の場所だけ True」にして Rel に落とす（support / boolean化）

-- 空/全の Rel（便利）

-- keys : List β を witness の候補として固定した Rel の合成
-- 「∃ b, b ∈ keys ∧ R a b ∧ S b c」
def relCompList {α β γ : Type} (keys : List β) (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, b ∈ keys ∧ R a b ∧ S b c

-- keys 制約（b ∈ keys）を Rel として切り出す（mask 的に使う）
def relInKeys {α β : Type} (keys : List β) : Rel α β :=
  fun _ b => b ∈ keys

--------------------------------------------------------------------------------
-- 601〜610：wsum の補題（存在⇔正、0⇔全0 など）
--------------------------------------------------------------------------------

-- 601：wsum の ext（リスト中の点ごとの一致で和が一致）
theorem ex601 {X : Type} (xs : List X) (f g : X → Nat) :
    (∀ x, x ∈ xs → f x = g x) → wsum xs f = wsum xs g := by

  intro h1
  induction xs with
  | nil =>
    dsimp [wsum]
  | cons y ys ih =>
    dsimp [wsum]
    obtain h2 : f y = g y := by
      apply h1
      apply List.mem_cons_self
    rw [h2]
    rw [Nat.add_right_inj]
    apply ih
    intro x hmem
    apply h1
    apply List.mem_cons_of_mem
    exact hmem

-- 602：wsum の定数和（k を length 回足す）
theorem ex602 {X : Type} (xs : List X) (k : Nat) :
    wsum xs (fun _ => k) = k * xs.length := by

  induction xs with
  | nil =>
    dsimp [wsum]
  | cons y ys ih =>
    dsimp [wsum]
    rw [ih]
    rw [Nat.mul_succ]
    rw [Nat.add_comm]

-- 603：map との交換
theorem ex603 {X Y : Type} (xs : List X) (g : X → Y) (f : Y → Nat) :
    wsum (xs.map g) f = wsum xs (fun x => f (g x)) := by

  induction xs with
  | nil =>
    dsimp [wsum, List.map]
  | cons y ys ih =>
    dsimp [wsum, List.map]
    rw [Nat.add_right_inj]
    exact ih

-- 604：∃ (mem かつ正) なら wsum は正
theorem ex604 {X : Type} (xs : List X) (f : X → Nat) :
    (∃ x, x ∈ xs ∧ f x > 0) → wsum xs f > 0 := by

  intro h
  obtain ⟨x, hmem, hpos⟩ := h
  induction xs with
  | nil =>
    dsimp [wsum]
    contradiction
  | cons y ys ih =>
    dsimp [wsum]
    by_cases hxy : x = y

    -- pos
    rw [←hxy]
    apply Nat.add_pos_left
    exact hpos

    -- neg
    obtain h2 :=
      List.mem_of_ne_of_mem hxy hmem

    obtain h3 :=
      ih h2

    apply Nat.add_pos_right

    exact h3

-- 605：wsum が正なら ∃ (mem かつ正)
theorem ex605 {X : Type} (xs : List X) (f : X → Nat) :
    wsum xs f > 0 → (∃ x, x ∈ xs ∧ f x > 0) := by

  intro h
  induction xs with
  | nil =>
    dsimp [wsum] at h
    contradiction
  | cons y ys ih =>
    dsimp [wsum] at h
    by_cases hy : f y > 0

    -- pos
    exists y
    constructor
    apply List.mem_cons_self
    exact hy

    -- neg
    obtain hZero :=
      Nat.eq_zero_of_not_pos hy

    rw [hZero] at h
    rw [Nat.zero_add] at h

    obtain ih2 := ih h
    obtain ⟨x1, hmem, hpos⟩ := ih2

    exists x1

    constructor
    apply List.mem_cons_of_mem
    exact hmem
    exact hpos

-- 606：まとめ：wsum xs f > 0 ↔ ∃x∈xs, f x > 0
theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
    (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by

  refine ⟨ex605 xs f, ex604 xs f⟩

-- 607：wsum xs f = 0 ↔ ∀x∈xs, f x = 0
theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
    wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by

  constructor

  -- (→)
  intro hWsum x1 hContains
  induction xs with
  | nil =>
    dsimp [wsum] at hWsum
    contradiction
  | cons y ys ih =>
    dsimp [wsum] at hWsum
    rw [Nat.add_eq_zero_iff] at hWsum
    obtain ⟨hFy, hWsumYs⟩ := hWsum
    by_cases hxy : x1 = y
    -- x1 = y
    rw [hxy]
    exact hFy
    -- x1 ≠ y
    obtain hMemYs :=
      List.mem_of_ne_of_mem hxy hContains
    obtain ih2 := ih hWsumYs hMemYs
    exact ih2

  -- (←)
  intro hForall
  induction xs with
  | nil =>
    dsimp [wsum]
  | cons y ys ih =>
    dsimp [wsum]
    by_cases hy : f y = 0

    -- f y = 0
    rw [hy]
    rw [Nat.zero_add]
    apply ih
    intro x1 hContains
    apply hForall
    apply List.mem_cons_of_mem
    exact hContains

    -- f y ≠ 0
    rw [Nat.add_eq_zero_iff]
    constructor
    apply hForall
    apply List.mem_cons_self
    apply ih
    intro x2 hContains
    apply hForall
    apply List.mem_cons_of_mem
    exact hContains

-- 608：Nat の積の正（積>0 ↔ 両方>0）
theorem ex608 (m n : Nat) :
    (m * n > 0) ↔ (m > 0 ∧ n > 0) := by

  constructor

  -- (→)
  intro h
  obtain h1 :=  Nat.pos_of_mul_pos_left h
  obtain h2 :=  Nat.pos_of_mul_pos_right h
  constructor
  exact h2
  exact h1

  -- (←)
  intro h
  obtain ⟨hM, hN⟩ := h
  apply Nat.mul_pos
  exact hM
  exact hN

-- 609：Nat の和の正（和>0 ↔ どちらか>0）
theorem ex609 (m n : Nat) :
    (m + n > 0) ↔ (m > 0 ∨ n > 0) := by

  constructor

  -- (→)
  intro h
  by_cases hm : m > 0
  -- m > 0
  left
  exact hm
  -- m = 0
  have hZero : m = 0 :=
    Nat.eq_zero_of_not_pos hm
  rw [hZero] at h
  rw [Nat.zero_add] at h
  right
  exact h

  -- (←)
  intro h
  by_cases hm : m > 0
  -- m > 0
  apply Nat.add_pos_left
  exact hm
  -- ¬ m > 0
  have hZero : m = 0 :=
    Nat.eq_zero_of_not_pos hm
  rw [hZero]
  rw [Nat.zero_add]
  obtain h2 | h3 := h
  contradiction
  exact h3

-- 610：Nat の積が 0（m*n=0 ↔ m=0 ∨ n=0）
theorem ex610 (m n : Nat) :
    (m * n = 0) ↔ (m = 0 ∨ n = 0) := by

  constructor

  -- (→)
  intro h
  rw [Nat.mul_eq_zero] at h
  exact h

  -- (←)
  intro h
  obtain h1 | h2 := h

  -- m = 0
  rw [h1]
  rw [Nat.zero_mul]

  -- n = 0
  rw [h2]
  rw [Nat.mul_zero]

--------------------------------------------------------------------------------
-- 611〜620：WRel を Rel に落とす（support）と、keys 合成（relCompList）
--------------------------------------------------------------------------------

-- 611：support(0) は空関係
theorem ex611 :
    wSupp (wZero α β) = (relBot α β) := by

  funext a1 b1
  dsimp [wSupp, wZero, relBot]

  apply propext
  constructor

  intro h
  contradiction

  intro h
  contradiction

-- 612：support(R+S) は「support R ∨ support S」
theorem ex612 (R S : WRel α β) :
    wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S) := by

  funext a1 b1
  dsimp [wSupp, wAdd, relAdd]
  apply propext
  constructor

  -- (→)
  intro h
  by_cases hR : R a1 b1 > 0
  -- R a1 b1 > 0
  left
  exact hR
  -- ¬ R a1 b1 > 0
  obtain hZeroR  :=
    Nat.eq_zero_of_not_pos hR
  rw [hZeroR, Nat.zero_add] at h
  right
  exact h

  -- (←)
  intro h
  obtain h1 | h2 := h

  -- R a1 b1 > 0
  apply Nat.add_pos_left
  exact h1

  -- S a1 b1 > 0
  apply Nat.add_pos_right
  exact h2

-- 613：support(maskW M) は M そのもの
theorem ex613 (M : Rel α β) :
    wSupp (maskW M) = M := by
  -- ヒント：by classical; funext a b; by_cases h : M a b <;> simp [maskW, wSupp, h]
  apply ex582

-- 614：support(wMask R M) は「support R ∧ M」
theorem ex614 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) = relMul (wSupp R) M := by
  -- ヒント：by classical; funext a b; by_cases h : M a b <;> simp [wMask, maskW, wSupp, h]
  apply ex583

-- 615：WLe なら support は包含（R≤S ⇒ supp R ⊆ supp S）
theorem ex615 (R S : WRel α β) :
    WLe R S → (wSupp R ⊆ wSupp S) := by
  -- ヒント：dsimp [WLe, RelLe, wSupp]; intro h a b hpos; exact Nat.lt_of_lt_of_le hpos (h a b)
  apply ex584

-- 616：relCompList は普通の relComp に含まれる（keys 制約を捨てる）
theorem ex616 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList keys R S ⊆ relComp R S := by

  dsimp [relCompList, relComp, RelLe]
  intro a1 c1 hExists
  obtain ⟨b1, hMem, hR, hS⟩ := hExists
  exists b1

-- 617：wCompList が正なら、どこかの b∈keys で項が正
theorem ex617 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys R S) a c →
        (∃ b, b ∈ keys ∧ (R a b * S b c) > 0) := by
  -- ヒント：dsimp [wSupp, wCompList] at *; ex605 を f := (fun b => R a b * S b c) に適用

  intro a c hSupp

  -- theorem ex605 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f > 0 → (∃ x, x ∈ xs ∧ f x > 0)
                      --  ∃ b, b ∈ keys ∧ R a b * S b c > 0

  obtain ⟨b1, h1, h2⟩ :=
    ex605 keys (fun b => R a b * S b c) hSupp

  exists b1

-- 618：項が正なら両因子も正（R a b * S b c > 0 ⇒ R a b>0 ∧ S b c>0）
theorem ex618 (R : WRel α β) (S : WRel β γ) :
    ∀ a b c, (R a b * S b c > 0) → (R a b > 0 ∧ S b c > 0) := by
  -- ヒント：ex608 を使う

  -- theorem ex608 (m n : Nat) :
  --     (m * n > 0) ↔ (m > 0 ∧ n > 0) := by

  intro a b c hPos

  obtain h :=
    ex608 (R a b) (S b c)

  rw [←h]

  exact hPos

-- 619：support(wCompList) ⊆ relCompList(support R)(support S)
theorem ex619 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys R S) ⊆ relCompList keys (wSupp R) (wSupp S) := by
  -- ヒント：a c を取り、ex617→ex618 で ∃b∈keys ∧ suppR ∧ suppS を作る

  intro a1 c1 hwSupp

  -- theorem ex617 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     ∀ a c,
  --       wSupp (wCompList keys R S) a c →
  --         (∃ b, b ∈ keys ∧ (R a b * S b c) > 0)

  obtain ⟨b1, hContains, hRS⟩ :=
    ex617 keys R S a1 c1 hwSupp

  -- theorem ex618 (R : WRel α β) (S : WRel β γ) :
  --     ∀ a b c, (R a b * S b c > 0) → (R a b > 0 ∧ S b c > 0)

  obtain hEx618 :=
    ex618 R S a1 b1 c1 hRS

  exists b1

-- 620：逆向き：relCompList(suppR)(suppS) ⊆ support(wCompList)
theorem ex620 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    relCompList keys (wSupp R) (wSupp S) ⊆ wSupp (wCompList keys R S) := by
  -- ヒント：∃b∈keys から、(R a b * S b c)>0 を作って ex604 へ

  dsimp [RelLe, relCompList, wSupp, wCompList]

  intro a1 c1 hExists

  obtain ⟨b1, hMem, hR, hS⟩ := hExists

  -- theorem ex604 {X : Type} (xs : List X) (f : X → Nat) :
  --     (∃ x, x ∈ xs ∧ f x > 0) → wsum xs f > 0 := by

  obtain hEx604 :=
    ex604 keys (fun b => R a1 b * S b c1)

  apply hEx604
  exists b1
  constructor
  exact hMem
  apply Nat.mul_pos
  exact hR
  exact hS

--------------------------------------------------------------------------------
-- 621〜630：Attention（wCompList）を support で Rel 的に見る／安全仕様
--------------------------------------------------------------------------------

-- 621：support(attnWRel) の具体形（relCompList になる）
theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by
  -- ヒント：attnWRel は wCompList の別名。ex619/ex620 を両方向で

  funext a c
  apply propext
  constructor

  -- (→)
  -- theorem ex619 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     wSupp (wCompList keys R S) ⊆ relCompList keys (wSupp R) (wSupp S) := by
  apply ex619 keys QK KV

  -- (←)
  -- theorem ex620 (keys : List β) (R : WRel α β) (S : WRel β γ) :
  --     relCompList keys (wSupp R) (wSupp S) ⊆ wSupp (wCompList keys R S) := by
  apply ex620 keys QK KV

-- 622：仕様 T に対する安全条件（support(QK) ⊆ (supp(KV) ▷ T) ⇒ support(attn) ⊆ T）
theorem ex622 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ rRes (wSupp KV) T) →
    (wSupp (attnWRel keys QK KV) ⊆ T) := by
  -- ヒント：ex621 で support(attn) を relCompList にし、witness b で rRes を叩く

  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by

  obtain hEx621 := ex621 keys QK KV
  rw [hEx621]
  intro hRelLe a1 g1 hExists
  obtain ⟨b1, hMem, hQK, hKV⟩ := hExists
  obtain hRRes := hRelLe a1 b1 hQK
  apply hRRes
  exact hKV

-- 623：mask すると support は必ず M に入る（supp(wMask R M) ⊆ M）
theorem ex623 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) ⊆ M := by
  -- ヒント：ex614 で supp(wMask) = suppR ∧ M にして右射影

  dsimp [RelLe, wSupp, wMask, maskW]
  intro a1 b1 hSupp
  by_cases hM : M a1 b1

  -- M a1 b1 = True
  exact hM

  -- M a1 b1 = False
  rw [if_neg hM] at hSupp
  rw [Nat.mul_zero] at hSupp
  contradiction

-- 624：残余で作った安全マスク：QKsafe := wMask QK (KV ▷ T)
--      ⇒ support(attn QKsafe KV) ⊆ T
theorem ex624 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex623 で supp(QKsafe) ⊆ rRes(...); それを ex622 へ

  intro a c
  rw [wSupp]
  rw [attnWRel]
  rw [wCompList]
  intro hSupp

  induction keys with
  | nil =>
    dsimp [wsum] at hSupp
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum] at hSupp

    by_cases h1 : (wsum bs fun b => wMask QK (rRes (wSupp KV) T) a b * KV b c) > 0

    -- pos
    apply ih
    exact h1

    -- neg
    have h2 : 0 = (wsum bs fun b => wMask QK (rRes (wSupp KV) T) a b * KV b c) := by
      obtain h2_1 :=
        Nat.eq_zero_of_not_pos h1
      exact h2_1.symm

    rw [←h2] at hSupp
    rw [Nat.add_zero] at hSupp
    dsimp  [wMask, maskW, rRes, wSupp] at hSupp
    obtain hSupp1 :=
      Nat.pos_of_mul_pos_left hSupp
    obtain hSupp2 :=
      Nat.pos_of_mul_pos_right hSupp
    obtain hSupp3 :=
      Nat.pos_of_mul_pos_left hSupp2
    have hSupp5 : ∀ (c : γ), KV b1 c > 0 → T a c := by
      by_cases hCond : ∀ (c : γ), KV b1 c > 0 → T a c
      exact hCond
      rw [if_neg hCond] at hSupp3
      contradiction
    apply hSupp5
    exact hSupp1

-- 625：仕様を強めると安全マスクは単調（T ⊆ T' ⇒ (KV▷T) ⊆ (KV▷T')）
theorem ex625 (KV : WRel β γ) (T T' : Rel α γ) :
    (T ⊆ T') → (rRes (wSupp KV) T ⊆ rRes (wSupp KV) T') := by
  -- ヒント：Basic_451 の ex483 を使う（S := wSupp KV）

  intro hRelLe a1 b1 hRRes g1 hwSupp
  apply hRelLe
  apply hRRes
  exact hwSupp

-- 626：KV 側を強める（到達先が増える）と安全マスクは厳しくなる（反単調）
theorem ex626 (KV KV' : WRel β γ) (T : Rel α γ) :
    (wSupp KV ⊆ wSupp KV') → (rRes (wSupp KV') T ⊆ rRes (wSupp KV) T) := by
  -- ヒント：Basic_451 の ex484 を使う

  intro hRelLe a1 b1 hRRes g1 hwSupp
  apply hRRes
  apply hRelLe
  exact hwSupp

-- 627：WLe(QK,QK') なら support(QK) ⊆ support(QK')
theorem ex627 (QK QK' : WRel α β) :
    WLe QK QK' → (wSupp QK ⊆ wSupp QK') := by
  -- ヒント：ex615
  apply ex615

-- 628：WLe の両側単調性で attnWRel も単調（重みそのもの）
theorem ex628 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
    WLe QK QK' → WLe KV KV' → WLe (attnWRel keys QK KV) (attnWRel keys QK' KV') := by
  -- ヒント：Basic_501 側の “wCompList は両側単調”（ex548 相当）を使う

  -- theorem ex548 (keys : List β) (R R' : WRel α β) (S S' : WRel β γ) :
  --     WLe R R' → WLe S S' → WLe (wCompList keys R S) (wCompList keys R' S') := by
  apply ex548

-- 629：重みの単調性から support でも単調（attn の到達先が増える）
theorem ex629 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
    WLe QK QK' → WLe KV KV' →
    (wSupp (attnWRel keys QK KV) ⊆ wSupp (attnWRel keys QK' KV')) := by
  -- ヒント：ex628 → ex615

  intro hWle1 hWle2
  intro a1 g1 hSupp

  -- theorem ex615 (R S : WRel α β) :
  --     WLe R S → (wSupp R ⊆ wSupp S)
  obtain hEx615 :=
    ex615 QK QK' hWle1 a1

  -- theorem ex628 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
  --     WLe QK QK' → WLe KV KV' → WLe (attnWRel keys QK KV) (attnWRel keys QK' KV')
  obtain hEx628 :=
    ex628 keys QK QK' KV KV' hWle1 hWle2 a1 g1

  obtain h2 :=
    Nat.lt_of_lt_of_le hSupp hEx628

  exact h2

-- 630：keys を増やす（append）と support は増える（下から単調）
theorem ex630 (keys more : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys R S) ⊆ wSupp (wCompList (keys ++ more) R S) := by
  -- ヒント：a c を固定し、ex604/ex605 を使って “同じ witness b” を append 側へ持ち上げる（mem_append）

  dsimp [RelLe, wSupp, wCompList]
  intro a1 g1 hSupp

  -- theorem ex604 {X : Type} (xs : List X) (f : X → Nat) :
  --     (∃ x, x ∈ xs ∧ f x > 0) → wsum xs f > 0 := by
  obtain hEx604 :=
    ex604 (keys ++ more) (fun b => R a1 b * S b g1)

  apply hEx604

  -- theorem ex605 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f > 0 → (∃ x, x ∈ xs ∧ f x > 0) := by
  obtain ⟨b1, hMem, hPos⟩ :=
    ex605 keys (fun b => R a1 b * S b g1) hSupp

  exists b1
  constructor
  apply List.mem_append_left
  exact hMem
  exact hPos

--------------------------------------------------------------------------------
-- 631〜640：mask と縮約の相互作用（設計向け：≤ や「keys 上でだけ True」など）
--------------------------------------------------------------------------------

-- 631：右側をマスクしても合成結果は増えない（右版 ex549）
theorem ex631 (keys : List β) (R : WRel α β) (S : WRel β γ) (N : Rel β γ) :
    WLe (wCompList keys R (wMask S N)) (wCompList keys R S) := by
  -- ヒント：wsum の単調性（ex503）＋ 1項ずつ “マスクしても増えない”（ex524/ex533 相当）

  intro a1 g1
  dsimp [wCompList]

  -- theorem ex503 {X : Type} (xs : List X) (f g : X → Nat) :
  --     (∀ x, f x ≤ g x) → wsum xs f ≤ wsum xs g := by
  obtain hEx503 :=
    ex503 keys (fun b => R a1 b * wMask S N b g1) (fun b => R a1 b * S b g1)

  apply hEx503

  intro b1

  dsimp [wMask, maskW]
  by_cases hN : N b1 g1

  -- N b1 g1 = True
  rw [if_pos hN, Nat.mul_one]
  apply Nat.le_refl

  -- N b1 g1 = False
  rw [if_neg hN, Nat.mul_zero, Nat.mul_zero]
  apply Nat.zero_le

-- 632：両側マスクでも増えない
theorem ex632 (keys : List β)
    (R : WRel α β) (M : Rel α β) (S : WRel β γ) (N : Rel β γ) :
    WLe (wCompList keys (wMask R M) (wMask S N)) (wCompList keys R S) := by
  -- ヒント：ex549 と ex631 を WLe の推移で合成

  intro a1 g1

  -- theorem ex631 (keys : List β) (R : WRel α β) (S : WRel β γ) (N : Rel β γ) :
  --     WLe (wCompList keys R (wMask S N)) (wCompList keys R S) := by
  obtain hEx631 :=
    ex631 keys R S N a1 g1

  -- theorem ex549 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
  --     WLe (wCompList keys (wMask R M) S) (wCompList keys R S) := by
  obtain hEx549 :=
    ex549 keys R M (wMask S N) a1 g1

  obtain hTrans :=
    Nat.le_trans hEx549 hEx631

  exact hTrans

-- 633：keys 上では常に True なマスクは（その keys の縮約に限って）消せる
theorem ex633 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
    (∀ a b, b ∈ keys → M a b) →
    wCompList keys (wMask R M) S = wCompList keys R S := by
  -- ヒント：各項で if_pos を使って maskW=1 を示し、wsum を ext（ex601）で押す

  intro h1
  funext a1 g1
  induction keys with
  | nil =>
    dsimp [wCompList, wMask, maskW, wsum]
  | cons b1 bs ih =>
    dsimp [wCompList, wMask, maskW, wsum]
    have h2 : M a1 b1 := by
      apply h1
      apply List.mem_cons_self
    rw [if_pos h2]
    rw [Nat.mul_one]
    rw [Nat.add_left_cancel_iff]
    apply ih
    intro a2 b2 hMem
    apply h1
    apply List.mem_cons_of_mem
    exact hMem

-- 634：keys 制約（relInKeys）でマスクしても wCompList は変わらない
theorem ex634 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wMask R (relInKeys (α:=α) keys)) S = wCompList keys R S := by
  -- ヒント：ex633 を M := relInKeys keys に適用（a は捨てられる）

  -- theorem ex633 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
  --     (∀ a b, b ∈ keys → M a b) →
  --     wCompList keys (wMask R M) S = wCompList keys R S := by
  obtain hEx633 :=
    ex633 keys R (relInKeys keys) S
  apply hEx633
  intro a1 b1 hMem
  dsimp [relInKeys]
  exact hMem

-- 635：Rel 側でも同様：relCompList keys R S = relComp (R ∧ inKeys) S
theorem ex635 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList keys R S = relComp (relMul R (relInKeys (α:=α) keys)) S := by

  funext a1 g1
  dsimp [relCompList, relComp, relMul, relInKeys]
  apply propext
  constructor

  intro hExists
  obtain ⟨b1, hMem, hR, hS⟩ := hExists
  exists b1

  intro hExists
  obtain ⟨b1, ⟨hR, hMem⟩, hS⟩ := hExists
  exists b1

-- 636：keys-residuation（片方向）
-- (relCompList keys R S ⊆ T) → (relMul R (inKeys keys) ⊆ (S ▷ T))
theorem ex636 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relCompList keys R S ⊆ T) →
    (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) := by
  -- ヒント：a b ⟨hR, hmem⟩ を取り、c と hS から relCompList の witness を作って仮定へ

  intro hRelLe a1 b1 hMul g1 hS
  obtain ⟨hR, hRelInKeys⟩ := hMul
  obtain hRelLe2 := hRelLe a1 g1
  apply hRelLe2
  exists b1

-- 637：keys-residuation（逆方向）
-- (relMul R (inKeys keys) ⊆ (S ▷ T)) → (relCompList keys R S ⊆ T)
theorem ex637 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) →
    (relCompList keys R S ⊆ T) := by
  -- ヒント：witness b を取り、仮定を b に適用

  intro hRelMul a1 g1 hRelCompList
  obtain ⟨b1, hMem, hR, hS⟩ := hRelCompList
  obtain hRelMul2 :=
    hRelMul a1 b1 ⟨hR, hMem⟩ g1 hS
  exact hRelMul2

-- 638：keys-residuation（同値）
theorem ex638 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relCompList keys R S ⊆ T) ↔
      (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) := by

  --dsimp [RelLe, relCompList, relMul, relInKeys, rRes]
  constructor
  -- (→)
  intro hRelCompList a1 b1 hRelMul g1 hS
  obtain ⟨hR, hRelInKeys⟩ := hRelMul
  obtain hRelLe2 := hRelCompList a1 g1
  apply hRelLe2
  exists b1
  -- (←)
  intro hRelMul a1 g1 hRelCompList
  obtain ⟨b1, hMem, hR, hS⟩ := hRelCompList
  obtain hRelMul2 :=
    hRelMul a1 b1 ⟨hR, hMem⟩ g1 hS
  exact hRelMul2

-- 639：WRel 側の「安全設計」を keys-residuation で読む（support 版）
theorem ex639 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (attnWRel keys QK KV) ⊆ T) ↔
      (relMul (wSupp QK) (relInKeys (α:=α) keys) ⊆ rRes (wSupp KV) T) := by
  -- ヒント：ex621 で supp(attn) を relCompList へ、ex638 を適用

  -- theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
  --     wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV)
  obtain hEx621 := ex621 keys QK KV
  rw [hEx621]

  -- theorem ex638 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
  --     (relCompList keys R S ⊆ T) ↔
  --       (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T)
  obtain hEx638 :=
    ex638 keys (wSupp QK) (wSupp KV) T
  rw [hEx638]

-- 640：spec を満たす “最大の（keys 制約つき）QK-support” を書く
-- QKmax := (inKeys keys) ∧ (KV ▷ T) とすると relCompList keys QKmax (supp KV) ⊆ T
theorem ex640 (keys : List β) (KV : WRel β γ) (T : Rel α γ) :
    relCompList keys (relMul (relInKeys (α:=α) keys) (rRes (wSupp KV) T)) (wSupp KV) ⊆ T := by
  -- ヒント：ex637 を R := (relInKeys keys) ∧ (rRes (supp KV) T) に適用（右射影で rRes を得る）

  -- theorem ex637 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
  --     (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) →
  --     (relCompList keys R S ⊆ T) := by
  obtain hEx637 :=
    ex637 keys (relMul (relInKeys keys) (rRes (wSupp KV) T)) (wSupp KV) T
  apply hEx637
  intro a1 b1 hMul g1 hSuppKV
  obtain ⟨hRelMul, hRelInKeys1⟩ := hMul
  obtain ⟨hRelInKeys2, hRres⟩ := hRelMul
  apply hRres
  exact hSuppKV

--------------------------------------------------------------------------------
-- 641〜650：まとめ（support/keys/残余/マスク）を “Attention をテンソル論理で表す” 方向へ
--------------------------------------------------------------------------------

-- 641：QKsafe := wMask QK ((supp KV) ▷ T) は「keys-residuation」視点で最小限の修正
theorem ex641 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    relMul (wSupp (wMask QK (rRes (wSupp KV) T))) (relInKeys (α:=α) keys)
      ⊆ rRes (wSupp KV) T := by
  -- ヒント：ex623（supp(wMask) ⊆ mask条件）＋ ∧ の右射影

  dsimp [RelLe, wSupp, wMask, maskW, relMul, relInKeys, rRes]
  intro a1 b1 hRelMul g1 hSuppKV
  obtain ⟨hSuppMask, hRelInKeys⟩ := hRelMul

  obtain hSupp2 :=
    Nat.pos_of_mul_pos_left hSuppMask

  have hSupp3 : ∀ (c : γ), KV b1 c > 0 → T a1 c := by
    by_cases hCond : ∀ (c : γ), KV b1 c > 0 → T a1 c
    exact hCond
    rw [if_neg hCond] at hSupp2
    contradiction

  apply hSupp3
  exact hSuppKV

-- 642：ex641 を使って、attn の仕様を一行で示せる形
theorem ex642 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex639 の (→) か (←) をうまく使う（どちらでも可）

  -- theorem ex639 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
  --     (wSupp (attnWRel keys QK KV) ⊆ T) ↔
  --       (relMul (wSupp QK) (relInKeys (α:=α) keys) ⊆ rRes (wSupp KV) T)
  --      wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T

  obtain hEx639 :=
    ex639 keys (wMask QK (rRes (wSupp KV) T)) KV T
  rw [hEx639]
  dsimp [RelLe, relMul, relInKeys, rRes, wSupp, wMask, maskW]
  intro a1 b1 hRelMul g1 fwSuppKV
  obtain ⟨hSuppMask, hRelInKeys⟩ := hRelMul
  obtain hSupp2 :=
    Nat.pos_of_mul_pos_left hSuppMask
  obtain hSupp3 :=
    Nat.pos_of_mul_pos_right hSuppMask
  have hSupp5 : ∀ (c : γ), KV b1 c > 0 → T a1 c := by
    by_cases hCond : ∀ (c : γ), KV b1 c > 0 → T a1 c
    exact hCond
    rw [if_neg hCond] at hSupp2
    contradiction
  apply hSupp5
  exact fwSuppKV

-- 643：mask の合成（AND 化）：wMask (wMask R M1) M2 = wMask R (M1 ∧ M2)
theorem ex643 (R : WRel α β) (M1 M2 : Rel α β) :
    wMask (wMask R M1) M2 = wMask R (fun a b => M1 a b ∧ M2 a b) := by
  -- ヒント：Basic_501 の ex543 相当を再利用してOK
  apply ex543

-- 644：安全マスクの “重ね掛け” は 1 回に潰せる（設計の簡約）
theorem ex644 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T1 T2 : Rel α γ) :
    attnWRel keys
      (wMask (wMask QK (rRes (wSupp KV) T1)) (rRes (wSupp KV) T2))
      KV
    =
    attnWRel keys
      (wMask QK (fun a b => rRes (wSupp KV) T1 a b ∧ rRes (wSupp KV) T2 a b))
      KV := by
  -- ヒント：ex643 で QK 側を整理

  -- theorem ex543 (R : WRel α β) (M1 M2 : Rel α β) :
  --     wMask (wMask R  M1) M2 = wMask R (fun a b => M1 a b ∧ M2 a b) := by
  obtain hEx543 :=
    ex543 QK (rRes (wSupp KV) T1) (rRes (wSupp KV) T2)

  rw [hEx543]

-- 645：仕様も AND でまとめられる（T := T1 ∧ T2）
theorem ex645 (KV : WRel β γ) (T1 T2 : Rel α γ) :
    rRes (wSupp KV) (fun a c => T1 a c ∧ T2 a c)
      =
    relMul (rRes (wSupp KV) T1) (rRes (wSupp KV) T2) := by
  -- ヒント：Basic_401 の rRes の定義展開で一直線（∀c の中の ∧）

  funext a1 b1
  dsimp [rRes, relMul, wSupp]
  apply propext
  constructor
  -- (→)
  intro hRRes
  constructor
  intro g1 hSuppKV
  obtain ⟨hRRes2, hRRes3⟩ :=
    hRRes g1 hSuppKV
  exact hRRes2
  intro g1 hSuppKV
  obtain ⟨hRRes2, hRRes3⟩ :=
    hRRes g1 hSuppKV
  exact hRRes3
  -- (←)
  intro hRelMul g1 hsSuppKV
  obtain ⟨hRRes1, hRRes2⟩ := hRelMul
  constructor
  apply hRRes1
  exact hsSuppKV
  apply hRRes2
  exact hsSuppKV

-- 646：上の 2 つを合わせて “複数仕様” の安全設計を 1 本化（見通し）
theorem ex646 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T1 T2 : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) (fun a c => T1 a c ∧ T2 a c))) KV)
      ⊆ (fun a c => T1 a c ∧ T2 a c) := by
  -- ヒント：ex642 を T := (T1 ∧ T2) で適用
  obtain hEx642 :=
    ex642 keys QK KV (fun a c => T1 a c ∧ T2 a c)

  apply hEx642

-- 647：keys を 2 ブロックに分けた attn の support は OR になる（Rel 視点）
theorem ex647 (keys1 keys2 : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (attnWRel (keys1 ++ keys2) QK KV)
      =
    relAdd (wSupp (attnWRel keys1 QK KV)) (wSupp (attnWRel keys2 QK KV)) := by
  -- ヒント：ex621 で relCompList へ、append は mem_append で OR になる

  obtain hEx621 :=
    ex621 (keys1 ++ keys2) QK KV

  rw [hEx621]

  funext a1 g1
  --dsimp [relAdd, wSupp, attnWRel, wCompList, relCompList]
  apply propext
  constructor
  -- (→)
  intro hExists
  obtain ⟨b1, hMem, hQK, hKV⟩ := hExists
  by_cases hIn1 : b1 ∈ keys1
  -- b1 ∈ keys1
  left
  obtain hEx587 :=
    ex587 keys1 QK KV a1 g1
  apply hEx587
  exists b1
  right
  have hMem1 : b1 ∈ keys2 := by
    rw [List.mem_append] at hMem
    obtain hMemLeft | hMemRight := hMem
    contradiction
    exact hMemRight
  obtain hEx587 :=
    ex587 keys2 QK KV a1 g1
  apply hEx587
  exists b1
  intro hRelAdd
  obtain hLeft | hRight := hRelAdd

  rw [←hEx621]

  rw [wSupp, attnWRel, wCompList] at *
  obtain hEx604 :=
    ex604 (keys1 ++ keys2) (fun b => QK a1 b * KV b g1)
  apply hEx604

  sorry





















-- 648：keys 分割の spec 検証：両ブロックが T を満たせば全体も T
theorem ex648 (keys1 keys2 : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (attnWRel keys1 QK KV) ⊆ T) →
    (wSupp (attnWRel keys2 QK KV) ⊆ T) →
    (wSupp (attnWRel (keys1 ++ keys2) QK KV) ⊆ T) := by
  -- ヒント：ex647 で OR に分解し、cases で流す
  -- TODO
  sorry

-- 649：最終チェック：support 視点の “multi-head + residual safety” の基本形
-- 2-head の QK を足し、残余で安全化しても spec を満たす
theorem ex649 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask (wAdd QK1 QK2) (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex642 を QK := (QK1+QK2) で適用
  -- TODO
  sorry

-- 650：まとめ：このファイルの “設計式” を 1 行で言う（文章の代わりの定理）
-- 「support(attn) ⊆ T を保証したいなら、QK を (supp KV ▷ T) でマスクせよ」
theorem ex650 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex642 そのもの（exact ex642 _ _ _ _ でもOK）
  -- TODO
  sorry

end TL
