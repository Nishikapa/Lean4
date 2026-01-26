--------------------------------------------------------------------------------
-- Basic_701.lean
-- 演習問題 701〜750（row/col-sum / transpose・scale・Hadamard の拡張代数 /
--                   WSpec の計算規則 / graph と keys の重みレベル）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 651〜700 は Basic_651 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_651

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（row/col-sum）
--------------------------------------------------------------------------------

-- 行方向の有限和：列候補 keys 上で R a b を足す
def wRowSum (keys : List β) (R : WRel α β) (a : α) : Nat :=
  wsum keys (fun b => R a b)

-- 列方向の有限和：行候補 keys 上で R a b を足す
def wColSum (keys : List α) (R : WRel α β) (b : β) : Nat :=
  wsum keys (fun a => R a b)

--------------------------------------------------------------------------------
-- 701〜710：wRowSum / wColSum の基本
--------------------------------------------------------------------------------

-- 701：空 keys の rowSum は 0
theorem ex701 (R : WRel α β) (a : α) :
    wRowSum ([] : List β) R a = 0 := by
  dsimp [wRowSum, wsum]

-- 702：cons 展開（rowSum）
theorem ex702 (b : β) (keys : List β) (R : WRel α β) (a : α) :
    wRowSum (b :: keys) R a = R a b + wRowSum keys R a := by
  dsimp [wRowSum, wsum]

-- 703：rowSum の ext（keys 上で点ごと一致なら rowSum も一致）
theorem ex703 (keys : List β) (R S : WRel α β) (a : α) :
    (∀ b, b ∈ keys → R a b = S a b) →
      wRowSum keys R a = wRowSum keys S a := by
  dsimp [wRowSum, wsum]
  intro hEq
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum]

    have h2 : (wsum bs fun b => R a b) = wsum bs fun b => S a b := by
      apply ih
      intro b1 hContins
      apply hEq
      apply List.mem_cons_of_mem
      exact hContins
    rw [h2]
    rw [Nat.add_right_cancel_iff]
    apply hEq
    apply List.mem_cons_self

-- 704：rowSum は wAdd に関して線形（点ごと）
theorem ex704 (keys : List β) (R S : WRel α β) (a : α) :
    wRowSum keys (wAdd R S) a = wRowSum keys R a + wRowSum keys S a := by
  dsimp [wRowSum, wsum, wAdd]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wAdd]
    rw [ih]
    rw [←Nat.add_assoc]
    rw [Nat.add_assoc (R a b) (S a b) (wsum bs fun b => R a b)]
    rw [Nat.add_comm (S a b) (wsum bs fun b => R a b)]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc]

-- 705：rowSum とスカラー倍（wScale）
theorem ex705 (keys : List β) (t : Nat) (R : WRel α β) (a : α) :
    wRowSum keys (wScale t R) a = t * wRowSum keys R a := by
  dsimp [wRowSum, wsum, wScale]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]

-- 706：空 keys の colSum は 0
theorem ex706 (R : WRel α β) (b : β) :
    wColSum ([] : List α) R b = 0 := by
  dsimp [wColSum]
  dsimp [wsum]

-- 707：cons 展開（colSum）
theorem ex707 (a : α) (keys : List α) (R : WRel α β) (b : β) :
    wColSum (a :: keys) R b = R a b + wColSum keys R b := by
  dsimp [wColSum]
  dsimp [wsum]

-- 708：transpose は row/col を入れ替える（rowSum）
theorem ex708 (keys : List α) (R : WRel α β) (b : β) :
    wRowSum keys (wTrans R) b = wColSum keys R b := by
  dsimp [wRowSum]
  dsimp [wColSum]
  dsimp [wTrans]

-- 709：transpose は row/col を入れ替える（colSum）
theorem ex709 (keys : List β) (R : WRel α β) (a : α) :
    wColSum keys (wTrans R) a = wRowSum keys R a := by
  dsimp [wColSum]
  dsimp [wRowSum]
  dsimp [wTrans]

-- 710：rowSum > 0 ↔ ∃ b∈keys, R a b > 0
theorem ex710 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a > 0 ↔ ∃ b, b ∈ keys ∧ R a b > 0 := by
  dsimp [wRowSum]
  obtain hEx606 :=
    ex606 keys (fun b => R a b)
  rw [hEx606]

--------------------------------------------------------------------------------
-- 711〜720：row/col の “0⇔全0” と maskW
--------------------------------------------------------------------------------

-- 711：rowSum = 0 ↔ ∀ b∈keys, R a b = 0
theorem ex711 (keys : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a = 0 ↔ (∀ b, b ∈ keys → R a b = 0) := by
  dsimp [wRowSum]
  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0)
  obtain hEx607 :=
    ex607 keys (R a)
  rw [hEx607]

-- 712：colSum > 0 ↔ ∃ a∈keys, R a b > 0
theorem ex712 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys R b > 0 ↔ ∃ a, a ∈ keys ∧ R a b > 0 := by
  -- theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
  --   (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  dsimp [wColSum]
  obtain hEx606 :=
    ex606 keys (fun a => R a b)
  rw [hEx606]

-- 713：colSum = 0 ↔ ∀ a∈keys, R a b = 0
theorem ex713 (keys : List α) (R : WRel α β) (b : β) :
    wColSum keys R b = 0 ↔ (∀ a, a ∈ keys → R a b = 0) := by

  dsimp [wColSum]
  -- theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
  --     wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
  obtain hEx607 :=
    ex607 keys (fun a => R a b)
  rw [hEx607]

-- 714：singleton rowSum（正）↔ 成分（正）
theorem ex714 (a : α) (b : β) (R : WRel α β) :
    wRowSum [b] R a > 0 ↔ R a b > 0 := by
  dsimp [wRowSum]
  dsimp [wsum]
  rfl

-- 715：b∈keys かつ R a b>0 なら rowSum>0
theorem ex715 (keys : List β) (R : WRel α β) (a : α) (b : β) :
    b ∈ keys → R a b > 0 → wRowSum keys R a > 0 := by
  dsimp [wRowSum]
  intro hIn hRab
  obtain hEx606 :=
    ex606 keys (fun b => R a b)
  rw [hEx606]
  exists b

-- 716：append 分解（rowSum）
theorem ex716 (keys more : List β) (R : WRel α β) (a : α) :
    wRowSum (keys ++ more) R a = wRowSum keys R a + wRowSum more R a := by
  dsimp [wRowSum]
  -- theorem ex536 {X : Type} (xs ys : List X) (f : X → Nat) :
  --     wsum (xs ++ ys) f = wsum xs f + wsum ys f := by
  obtain hEx536 :=
    ex536 keys more (R a)
  rw [hEx536]

-- 717：append 分解（colSum）
theorem ex717 (keys more : List α) (R : WRel α β) (b : β) :
    wColSum (keys ++ more) R b = wColSum keys R b + wColSum more R b := by
  dsimp [wColSum]
  obtain hEx536 :=
    ex536 keys more (fun a => R a b)
  rw [hEx536]

-- 718：rowSum>0 は append で保たれる
theorem ex718 (keys more : List β) (R : WRel α β) (a : α) :
    wRowSum keys R a > 0 → wRowSum (keys ++ more) R a > 0 := by
  -- TODO（ヒント：ex716 と Nat.add_pos_left / Nat.add_pos_right）

  -- theorem ex716 (keys more : List β) (R : WRel α β) (a : α) :
  --     wRowSum (keys ++ more) R a = wRowSum keys R a + wRowSum more R a
  rw [ex716 keys more R a]
  dsimp [wRowSum]
  intro h1
  apply Nat.add_pos_left
  exact h1

-- 719：wZero の rowSum は常に 0
theorem ex719 (keys : List β) (a : α) :
    wRowSum keys (wZero α β) a = 0 := by
  dsimp [wRowSum]
  dsimp [wZero]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum]
    rw [Nat.zero_add]
    exact ih

-- 720：maskW の rowSum>0 ↔ ∃ b∈keys, M a b
theorem ex720 (keys : List β) (M : Rel α β) (a : α) :
    wRowSum keys (maskW M) a > 0 ↔ ∃ b, b ∈ keys ∧ M a b := by

  dsimp [wRowSum, maskW]
  constructor
  intro hwRowSum1
  induction keys with
  | nil =>
    dsimp [wsum] at hwRowSum1
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum] at hwRowSum1
    --obtain hwRowSum2 : 0 < ((if M a b1 then 1 else 0) + wsum bs fun b => if M a b then 1 else 0) := hwRowSum1

    rw [gt_iff_lt] at hwRowSum1
    rw [Nat.add_pos_iff_pos_or_pos] at hwRowSum1
    cases hwRowSum1 with
    | inl hMab1 =>
      by_cases hM : M a b1
      rw [if_pos hM] at hMab1
      exists b1
      constructor
      apply List.mem_cons_self
      exact hM
      rw [if_neg hM] at hMab1
      contradiction
    | inr hWsumBs =>
      obtain h2 := ih hWsumBs
      obtain ⟨b2, hContains, hMab2⟩ := h2
      exists b2
      constructor
      apply List.mem_cons_of_mem
      exact hContains
      exact hMab2

  intro hExists
  obtain ⟨b, hIn, hMab⟩ := hExists
  induction keys with
  | nil =>
    dsimp [wsum]
    contradiction
  | cons b1 bs ih =>
    dsimp [wsum]
    rw [gt_iff_lt]
    rw [Nat.add_pos_iff_pos_or_pos]
    by_cases hEq : b = b1
    rw [←hEq]
    left
    rw [if_pos hMab]
    exact Nat.zero_lt_one
    right
    obtain hInc := List.mem_of_ne_of_mem hEq hIn
    obtain hWsumBs := ih hInc
    exact hWsumBs

--------------------------------------------------------------------------------
-- 721〜730：wCompList / wMask / wGraph（重みレベル）
--------------------------------------------------------------------------------

-- 721：空 keys の wCompList は wZero
theorem ex721 (R : WRel α β) (S : WRel β γ) :
    wCompList ([] : List β) R S = wZero α γ := by
  funext a c
  dsimp [wCompList, wZero, wsum]

-- 722：singleton keys の wCompList（1 項だけ）
theorem ex722 (b : β) (R : WRel α β) (S : WRel β γ) :
    wCompList [b] R S = (fun a c => R a b * S b c) := by
  funext a c
  dsimp [wCompList, wsum]

-- 723：右をスカラー倍すると結果もスカラー倍（右線形性）
theorem ex723 (keys : List β) (t : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys R (wScale t S) = wScale t (wCompList keys R S) := by
  funext a c
  dsimp [wCompList, wScale, wsum]
  induction keys with
  | nil =>
    rfl
  | cons b bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]
    rw [←Nat.mul_assoc (R a b) t (S b c)]
    rw [←Nat.mul_comm t (R a b)]
    rw [←Nat.mul_assoc t (R a b) (S b c)]

-- 724：両側をスカラー倍すると係数は積になる
theorem ex724 (keys : List β) (t u : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wScale t R) (wScale u S) = wScale (t * u) (wCompList keys R S) := by
  funext a c
  dsimp [wCompList, wScale, wsum]
  induction keys with
  | nil =>
    rfl
  | cons b1 bs ih =>
    dsimp [wsum, wScale]
    rw [ih]
    rw [Nat.mul_add]
    rw [←Nat.mul_assoc (t * R a b1) u (S b1 c)]
    rw [Nat.mul_assoc t (R a b1) u]
    rw [Nat.mul_comm (R a b1) u]
    rw [←Nat.mul_assoc t u (R a b1)]
    rw [←Nat.mul_assoc (t * u) (R a b1) (S b1 c)]

-- 725：wMask は Hadamard（wMul）で “maskW を掛ける” のと同じ
theorem ex725 (R : WRel α β) (M : Rel α β) :
    wMask R M = wMul R (maskW M) := by
  funext a b
  dsimp [wMask, wMul, maskW]

-- 726：Hadamard と mask の交換（mask を外へ寄せる）
theorem ex726 (R S : WRel α β) (M : Rel α β) :
    wMul (wMask R M) S = wMask (wMul R S) M := by
  funext a b
  dsimp [wMask, wMul, maskW]
  by_cases hMab : M a b
  rw [if_pos hMab]
  rw [Nat.mul_one]
  rw [Nat.mul_one]
  rw [if_neg hMab]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]
  rw [Nat.zero_mul]

-- 727：keys.Nodup のとき、graph を左に置いた縮約は “行選択＋mask” になる（重み）
theorem ex727 (keys : List β) (f : α → β) (S : WRel β γ) :
    keys.Nodup →
      wCompList keys (wGraph f) S
        =
      wMask (fun a c => S (f a) c) (fun a _ => f a ∈ keys) := by
  sorry

-- 728：ex727 の “>0” 版（重みが正になる条件）
theorem ex728 (keys : List β) (f : α → β) (S : WRel β γ) :
    keys.Nodup →
    ∀ a c,
      wCompList keys (wGraph f) S a c > 0
        ↔ (f a ∈ keys ∧ S (f a) c > 0) := by
  -- TODO（ヒント：ex727 で書き換えてから場合分け）
  sorry

-- 729：graph-graph の縮約（keys.Nodup のときの “関数合成＋mask”）（重み）
theorem ex729 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
      wCompList keys (wGraph f) (wGraph g)
        =
      wMask (wGraph (fun a => g (f a))) (fun a _ => f a ∈ keys) := by
  -- TODO
  sorry

-- 730：keys が “十分大きい（全包含）” なら mask が消えて graph 合成そのもの（重み）
theorem ex730 (keys : List β) (f : α → β) (g : β → γ) :
    keys.Nodup →
    (∀ b, b ∈ keys) →
      wCompList keys (wGraph f) (wGraph g) = wGraph (fun a => g (f a)) := by
  -- TODO（ヒント：ex729 の RHS で mask 条件が常に True になる）
  sorry

--------------------------------------------------------------------------------
-- 731〜740：transpose / scale / Hadamard の拡張代数（未出の相性）
--------------------------------------------------------------------------------

-- 731：wTrans は wScale と可換
theorem ex731 (t : Nat) (R : WRel α β) :
    wTrans (wScale t R) = wScale t (wTrans R) := by
  -- TODO
  sorry

-- 732：wTrans は wMul と可換（点ごと）
theorem ex732 (R S : WRel α β) :
    wTrans (wMul R S) = wMul (wTrans R) (wTrans S) := by
  -- TODO
  sorry

-- 733：wScale は wAdd に分配
theorem ex733 (t : Nat) (R S : WRel α β) :
    wScale t (wAdd R S) = wAdd (wScale t R) (wScale t S) := by
  -- TODO
  sorry

-- 734：wScale の合成（係数が積になる）
theorem ex734 (t u : Nat) (R : WRel α β) :
    wScale t (wScale u R) = wScale (t * u) R := by
  -- TODO
  sorry

-- 735：wScale 1 は恒等
theorem ex735 (R : WRel α β) :
    wScale 1 R = R := by
  -- TODO
  sorry

-- 736：wMul は右の wAdd に分配（点ごと）
theorem ex736 (R S T : WRel α β) :
    wMul R (wAdd S T) = wAdd (wMul R S) (wMul R T) := by
  -- TODO（ヒント：Nat.mul_add）
  sorry

-- 737：wScale は wMul から外に出せる（左側係数）
theorem ex737 (t : Nat) (R S : WRel α β) :
    wMul (wScale t R) S = wScale t (wMul R S) := by
  -- TODO
  sorry

-- 738：WLe は wScale で保たれる（単調性）
theorem ex738 (t : Nat) (R S : WRel α β) :
    WLe R S → WLe (wScale t R) (wScale t S) := by
  -- TODO
  sorry

-- 739：WLe は wMul（右固定）で保たれる
theorem ex739 (R S T : WRel α β) :
    WLe R S → WLe (wMul R T) (wMul S T) := by
  -- TODO
  sorry

-- 740：WLe は wTrans で保たれる
theorem ex740 (R S : WRel α β) :
    WLe R S → WLe (wTrans R) (wTrans S) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 741〜750：WSpec（「仕様の外は 0」）の計算規則・応用
--------------------------------------------------------------------------------

-- 741：transpose すると spec も transpose する
theorem ex741 (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wTrans R) (relTrans T) := by
  -- TODO
  sorry

-- 742：スカラー倍しても spec は保たれる
theorem ex742 (t : Nat) (R : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec (wScale t R) T := by
  -- TODO
  sorry

-- 743：別々の spec を持つ 2 つを足すと、spec は OR（合併）になる
theorem ex743 (R S : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec S U → WSpec (wAdd R S) (relAdd T U) := by
  -- TODO
  sorry

-- 744：mask すると spec は ∧（交差）へ強化できる
theorem ex744 (R : WRel α β) (T : Rel α β) (M : Rel α β) :
    WSpec R T → WSpec (wMask R M) (relMul T M) := by
  -- TODO
  sorry

-- 745：WSpec は “下に閉じる”（R ≤ S かつ S が spec なら R も spec）
theorem ex745 (R S : WRel α β) (T : Rel α β) :
    WLe R S → WSpec S T → WSpec R T := by
  -- TODO
  sorry

-- 746：縮約（keys つき）での spec：relCompList keys で表せる（ex700 の強化）
theorem ex746 (keys : List β) (R : WRel α β) (S : WRel β γ)
    (T : Rel α β) (U : Rel β γ) :
    WSpec R T → WSpec S U → WSpec (wCompList keys R S) (relCompList keys T U) := by
  -- TODO
  sorry

-- 747：spec の外しか見ない keys なら rowSum は 0
theorem ex747 (keys : List β) (R : WRel α β) (T : Rel α β) (a : α) :
    WSpec R T →
    (∀ b, b ∈ keys → ¬ T a b) →
      wRowSum keys R a = 0 := by
  -- TODO
  sorry

-- 748：spec の外しか見ない keys なら colSum は 0
theorem ex748 (keys : List α) (R : WRel α β) (T : Rel α β) (b : β) :
    WSpec R T →
    (∀ a, a ∈ keys → ¬ T a b) →
      wColSum keys R b = 0 := by
  -- TODO
  sorry

-- 749：graph は自分の graph-spec を満たす
theorem ex749 (f : α → β) :
    WSpec (wGraph f) (relGraph f) := by
  -- TODO
  sorry

-- 750：multi-head（QK を足す）で spec が head ごとに違うなら、合併 spec になる（重みレベル）
theorem ex750 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ)
    (T1 T2 : Rel α γ) :
    WSpec (attnWRel keys QK1 KV) T1 →
    WSpec (attnWRel keys QK2 KV) T2 →
    WSpec (attnWRel keys (wAdd QK1 QK2) KV) (relAdd T1 T2) := by
  -- TODO（ヒント：attnWRel は wCompList の別名。
  --   まず “線形性” で attn(wAdd QK1 QK2) を wAdd(attn QK1)(attn QK2) にしてから ex743 を使う）
  sorry

end TL
