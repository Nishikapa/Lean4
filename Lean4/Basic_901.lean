--------------------------------------------------------------------------------
-- Basic_901.lean
-- Exercise set 901-915 (fast-track 11)
-- Theme: masked hard-attention heads and multi-head aggregation (0/1 semantics).
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_886.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_886

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {A B C D H : Type}

--------------------------------------------------------------------------------
-- 0) New helpers: head / masked-head / multi-head aggregate
--------------------------------------------------------------------------------

noncomputable def wHead (keys : List B) (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  wReachComp keys QK KV

noncomputable def wMaskedHead (keys : List B) (M : Rel A B)
    (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  wHead keys (wMask QK M) KV

noncomputable def wMHA (heads : List H) (F : H -> WRel A C) : WRel A C :=
  wsumW heads F

--------------------------------------------------------------------------------
-- 901-905: Head + masking basics
--------------------------------------------------------------------------------

-- 901: support of head is relCompList on supports.
theorem ex901 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wHead keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by
  -- Hint: unfold wHead, then ex818.
  funext a1 c1
  dsimp [wHead, wReachComp, wSupp, relCompList, maskW]
  by_cases h1 : ∃ b, b ∈ keys ∧ QK a1 b > 0 ∧ KV b c1 > 0
  -- pos
  rw [if_pos h1]
  apply propext
  constructor
  intro h2
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  exists b1
  intro h3
  apply Nat.zero_lt_one
  -- neg
  rw [if_neg h1]
  apply propext
  constructor
  intro h4
  contradiction
  intro h5
  obtain ⟨b2, hb4, hb5, hb6⟩ := h5
  apply False.elim
  apply h1
  exists b2

-- 902: support of masked-head (left mask) is relMul on left support.
theorem ex902 (keys : List B) (M : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wMaskedHead keys M QK KV)
      =
    relCompList keys (relMul (wSupp QK) M) (wSupp KV) := by
  -- Hint: ex901 + ex614.
  funext a1 c1
  dsimp [wMaskedHead, wHead, wReachComp, wSupp, relCompList, relMul, maskW, wMask]
  by_cases h1 : ∃ b, b ∈ keys ∧ (QK a1 b * if M a1 b then 1 else 0) > 0 ∧ KV b c1 > 0

  -- pos
  rw [if_pos h1]
  apply propext
  constructor
  intro h2
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  obtain hb4 : M a1 b1  := by
    by_cases hM_ : M a1 b1
    exact hM_
    rw [if_neg hM_] at hb2
    rw [Nat.mul_zero] at hb2
    contradiction
  obtain hb5 : QK a1 b1 > 0 := by
    by_cases hM_ : QK a1 b1 > 0
    exact hM_
    obtain hM2_ := Nat.eq_zero_of_not_pos hM_
    rw [hM2_] at hb2
    rw [Nat.zero_mul] at hb2
    contradiction
  clear hb2
  exists b1
  obtain ⟨b2, h2, h3, h4⟩:=h1
  intro h5
  apply Nat.zero_lt_one

  -- neg
  rw [if_neg h1]
  apply propext
  constructor
  intro h6
  contradiction
  intro h7
  obtain ⟨b3, hb6, hb7, hb8⟩ := h7
  obtain ⟨hb9, hb10⟩ := hb7
  apply False.elim
  apply h1
  exists b3
  constructor
  exact hb6
  constructor
  apply Nat.mul_pos
  exact hb9
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hb10
  exact hb8

-- 903: masking the left side can only reduce support.
theorem ex903 (keys : List B) (M : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wMaskedHead keys M QK KV) ⊆ wSupp (wHead keys QK KV) := by
  --   * ex902/ex901
  --   * pointwise: (wSupp QK a b ∧ M a b) -> wSupp QK a b
  dsimp [RelLe, wSupp, wMaskedHead, wHead, wReachComp, maskW, relCompList, wMask]
  intro a1 c1 h1
  have h2 : ∃ b, b ∈ keys ∧ (QK a1 b * if M a1 b then 1 else 0) > 0 ∧ KV b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ (QK a1 b * if M a1 b then 1 else 0) > 0 ∧ KV b c1 > 0
    exact h_
    rw [if_neg h_] at h1
    contradiction
  clear h1
  obtain ⟨b1, hb1, hb2, hb3⟩ := h2
  obtain hb2_1 := Nat.pos_of_mul_pos_left hb2
  obtain hb2_2 := Nat.pos_of_mul_pos_right hb2
  clear hb2
  have hb2_3 : M a1 b1 := by
    by_cases hM_ : M a1 b1
    exact hM_
    rw [if_neg hM_] at hb2_1
    contradiction
  clear hb2_1
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1

-- 904: key-membership mask on left is redundant for head.
theorem ex904 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (relInKeys (α:=A) keys) QK KV
      =
    wHead keys QK KV := by
  -- Hint:
  --   * ∈ relCompList, witness b already satisfies b ∈ keys
  --   * so extra left mask by relInKeys is redundant
  funext a1 c1
  dsimp [wMaskedHead, wHead, wReachComp, maskW, relCompList, wSupp, wMask, relInKeys]
  by_cases h1 :
    ∃ b, b ∈ keys ∧ (QK a1 b * if b ∈ keys then 1 else 0) > 0 ∧ KV b c1 > 0
  -- pos
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  obtain hb2_1 := Nat.pos_of_mul_pos_left hb2
  obtain hb2_2 := Nat.pos_of_mul_pos_right hb2
  clear hb2
  have hb2_3 : b1 ∈ keys := by
    by_cases hM_ : b1 ∈ keys
    exact hM_
    rw [if_neg hM_] at hb2_1
    contradiction
  clear hb2_1
  rw [if_pos]
  rw [if_pos]
  exists b1
  exists b1
  constructor
  exact hb1
  constructor
  rw [if_pos]
  rw [Nat.mul_one]
  exact hb2_2
  exact hb1
  exact hb3
  -- neg
  rw [if_neg]
  rw [if_neg]
  intro h2
  apply h1
  obtain ⟨b2, hb4, hb5, hb6⟩ := h2
  exists b2
  constructor
  exact hb4
  constructor
  apply Nat.mul_pos
  exact hb5
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hb4
  exact hb6
  intro h3
  apply h1
  obtain ⟨b3, hb7, hb8, hb9⟩ := h3
  obtain hb8_2 := Nat.pos_of_mul_pos_right hb8
  clear hb8
  exists b3
  constructor
  exact hb7
  constructor
  apply Nat.mul_pos
  exact hb8_2
  rw [if_pos]
  apply Nat.zero_lt_one
  exact hb7
  exact hb9

-- 905: singleton head formula.
theorem ex905 (b : B) (R : WRel A B) (S : WRel B C) :
    wHead [b] R S
      =
    maskW (fun a c => wSupp R a b ∧ wSupp S b c) := by
  -- Hint: unfold wHead; use ex867.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, wSupp, relCompList]
  by_cases h1 : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ S b_1 c1 > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  rw [if_pos]
  rw [List.mem_singleton] at hb1
  rw [←hb1]
  constructor
  exact hb2
  exact hb3
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  obtain ⟨h2_1, h2_2⟩ := h2
  apply h1
  exists b
  constructor
  rw [List.mem_singleton]
  constructor
  exact h2_1
  exact h2_2

--------------------------------------------------------------------------------
-- 906-910: Graph-style head formulas
--------------------------------------------------------------------------------

-- 906: graph on the left gives pullback-with-key-gate mask form.
theorem ex906 (keys : List B) (f : A -> B) (S : WRel B C) :
    wHead keys (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys) := by
  -- Hint: unfold wHead; use ex848.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wGraph, relGraph, wMask, wBool]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ S b c1 > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  have hb2_1 : f a1 = b1 := by
    by_cases hF_ : f a1 = b1
    exact hF_
    rw [if_neg hF_] at hb2
    contradiction
  clear hb2
  rw [hb2_1]
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  exact hb1
  exact hb3
  -- neg
  rw [if_neg h1]
  symm
  rw [Nat.mul_eq_zero]
  by_cases h2 : ( S (f a1) c1 > 0 ) ∧ (f a1 ∈ keys )
  obtain ⟨h2_1, h2_2⟩ := h2
  apply False.elim
  apply h1
  exists (f a1)
  constructor
  exact h2_2
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  exact h2_1
  have h3 : (¬ ( S (f a1) c1 > 0 )) ∨ ¬ (f a1 ∈ keys) := by
    by_cases h1_ : S (f a1) c1 > 0
    by_cases h2_ : f a1 ∈ keys
    obtain h3_ := And.intro h1_ h2_
    contradiction
    right
    exact h2_
    left
    exact h1_
  clear h2
  obtain h3_1 | h3_2 := h3
  rw [if_neg h3_1]
  left
  rfl
  rw [if_neg h3_2]
  right
  rfl

-- 907: if every f a is ∈ keys, graph-left head drops the gate.
theorem ex907 (keys : List B) (f : A -> B) (S : WRel B C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) S
        =
      (fun a c => wBool S (f a) c) := by
  -- Hint: unfold wHead; use ex850.
  intro h0
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wGraph, relGraph, wBool]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ S b c1 > 0
  rw [if_pos h1]
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  have hb2_1 : f a1 = b1 := by
    by_cases hF_ : f a1 = b1
    exact hF_
    rw [if_neg hF_] at hb2
    contradiction
  clear hb2
  rw [hb2_1]
  rw [if_pos]
  exact hb3
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  apply h1
  obtain h0_1 := h0 a1
  exists (f a1)
  constructor
  exact h0_1
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  exact h2

-- 908: graph-graph head as one mask.
theorem ex908 (keys : List B) (f : A -> B) (g : B -> C) :
    wHead keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  funext a1 c1
  -- Hint: unfold wHead; use ex849.
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wGraph, relGraph]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ (if g b = c1 then 1 else 0) > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨b1, hb1, hb2, hb3⟩ := h1
  have hb2_1 : f a1 = b1 := by
    by_cases hF_ : f a1 = b1
    exact hF_
    rw [if_neg hF_] at hb2
    contradiction
  clear hb2
  have hb3_1 : g b1 = c1 := by
    by_cases hG_ : g b1 = c1
    exact hG_
    rw [if_neg hG_] at hb3
    contradiction
  clear hb3
  rw [hb2_1]
  rw [hb3_1]
  rw [if_pos]
  constructor
  exact hb1
  rfl
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  obtain ⟨h2_1, h2_2⟩ := h2
  apply h1
  exists (f a1)
  constructor
  exact h2_1
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h2_2

-- 909: graph-graph head under key coverage becomes composed graph.
theorem ex909 (keys : List B) (f : A -> B) (g : B -> C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) (wGraph g)
        =
      wGraph (fun a => g (f a)) := by
  -- Hint: unfold wHead; use ex836 (or ex870).
  intro h1
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wGraph, wSupp, relGraph]
  by_cases h2 : ∃ b, b ∈ keys ∧ (if f a1 = b then 1 else 0) > 0 ∧ (if g b = c1 then 1 else 0) > 0
  -- pos
  rw [if_pos h2]
  obtain ⟨b1, hb1, hb2, hb3⟩ := h2
  have hb2_1 : f a1 = b1 := by
    by_cases hF_ : f a1 = b1
    exact hF_
    rw [if_neg hF_] at hb2
    contradiction
  clear hb2
  have hb3_1 : g b1 = c1 := by
    by_cases hG_ : g b1 = c1
    exact hG_
    rw [if_neg hG_] at hb3
    contradiction
  clear hb3
  rw [hb2_1]
  rw [hb3_1]
  rw [if_pos]
  rfl
  -- neg
  rw [if_neg h2]
  rw [if_neg]
  intro h3
  apply h2
  exists (f a1)
  obtain h1_1 := h1 a1
  constructor
  exact h1_1
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rfl
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h3

-- 910: singleton multi-head aggregate is just bool of that head.
theorem ex910 (h0 : H) (F : H -> WRel A C) :
    wMHA [h0] F = wBool (F h0) := by
  -- Hint:
  --   * unfold wMHA / wsumW on singleton
  --   * or use ex842 + ex841
  funext a1 c1
  dsimp [wMHA, wsumW, wBool, maskW, wSupp]
  conv =>
    lhs
    arg 1
    rw [ex606]
  by_cases h1 : F h0 a1 c1 > 0
  rw [if_pos]
  rw [if_pos]
  exact h1
  exists h0
  constructor
  rw [List.mem_singleton]
  exact h1
  rw [if_neg]
  rw [if_neg]
  exact h1
  intro h2
  apply h1
  obtain ⟨h2_1, h2_2, h2_3⟩ := h2
  rw [List.mem_singleton] at h2_2
  rw [←h2_2]
  exact h2_3

--------------------------------------------------------------------------------
-- 911-915: Multi-head algebra and interaction with head
--------------------------------------------------------------------------------

-- 911: append of head list becomes OR (wOr).
theorem ex911 (heads1 heads2 : List H) (F : H -> WRel A C) :
    wMHA (heads1 ++ heads2) F
      =
    wOr (wMHA heads1 F) (wMHA heads2 F) := by
  -- Hint: unfold wMHA; ex852 + definition of wOr.
  funext a1 c1
  dsimp [wMHA, wsumW, wOr, maskW, wSupp, wBool, wAdd]
  conv =>
    conv =>
      lhs
      arg 1
      rw [ex606]
    conv =>
      rhs
      arg 1
      arg 1
      conv =>
        arg 1
        arg 1
        rw [ex606]
      conv =>
        arg 2
        arg 1
        rw [ex606]

  by_cases h1 : ∃ x, x ∈ heads1 ++ heads2 ∧ F x a1 c1 > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨x1, hx1, hx2⟩ := h1
  rw [List.mem_append] at hx1
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain hx1_1 | hx1_2 := hx1
  left
  rw [if_pos]
  apply Nat.zero_lt_one
  exists x1
  right
  rw [if_pos]
  apply Nat.zero_lt_one
  exists x1
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  apply h1
  rw [gt_iff_lt] at h2
  rw [Nat.add_pos_iff_pos_or_pos] at h2
  obtain h2_1 | h2_2 := h2
  have h3 : ∃ x, x ∈ heads1 ∧ F x a1 c1 > 0 := by
    by_cases h_ : ∃ x, x ∈ heads1 ∧ F x a1 c1 > 0
    exact h_
    rw [if_neg h_] at h2_1
    contradiction
  clear h2_1
  obtain ⟨x2, hx3, hx4⟩ := h3
  exists x2
  constructor
  rw [List.mem_append]
  left
  exact hx3
  exact hx4
  have h4 : ∃ x, x ∈ heads2 ∧ F x a1 c1 > 0 := by
    by_cases h_ : ∃ x, x ∈ heads2 ∧ F x a1 c1 > 0
    exact h_
    rw [if_neg h_] at h2_2
    contradiction
  clear h2_2
  obtain ⟨x3, hx5, hx6⟩ := h4
  exists x3
  constructor
  rw [List.mem_append]
  right
  exact hx5
  exact hx6

-- 912: each selected head is below the aggregate.
theorem ex912 (heads : List H) (F : H -> WRel A C) (h : H) :
    h ∈ heads ->
      WLe (wBool (F h)) (wMHA heads F) := by
  -- Hint: unfold wMHA; ex857.
  intro h1
  dsimp [WLe]
  intro a1 c1
  dsimp [wBool, maskW, wSupp, wMHA, wsumW]
  conv =>
    rhs
    arg 1
    rw [ex606]
  by_cases h2 : F h a1 c1 > 0
  -- pos
  rw [if_pos h2]
  rw [if_pos]
  apply Nat.le_refl
  exists h
  rw [if_neg h2]
  apply Nat.zero_le

-- 913: monotonicity ∈ head-list inclusion.
theorem ex913 (heads heads' : List H) (F : H -> WRel A C) :
    (∀ h, h ∈ heads -> h ∈ heads') ->
      WLe (wMHA heads F) (wMHA heads' F) := by
  -- Hint: unfold wMHA; ex858.
  intro h1
  dsimp [WLe]
  intro a1 c1
  dsimp [wMHA, wsumW, wBool, maskW, wSupp]
  conv =>
    conv =>
      lhs
      arg 1
      rw [ex606]
    conv =>
      rhs
      arg 1
      rw [ex606]
  by_cases h2 : ∃ x, x ∈ heads ∧ F x a1 c1 > 0
  obtain ⟨x1, hx1, hx2⟩ := h2
  obtain hx1_1 := h1 x1 hx1
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  exists x1
  exists x1
  rw [if_neg]
  apply Nat.zero_le
  intro h3
  apply h2
  obtain ⟨x2, hx3, hx4⟩ := h3
  exists x2

-- 914: head distributes over multi-head aggregate on the right.
theorem ex914 (keys : List B) (R : WRel A B) (heads : List H) (F : H -> WRel B C) :
    wHead keys R (wMHA heads F)
      =
    wMHA heads (fun h => wHead keys R (F h)) := by
  -- Hint: unfold wHead/wMHA; ex863.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wMHA, wsumW, wBool]
  conv =>
    conv =>
      lhs
      arg 1
      arg 1
      intro b1
      rhs
      rhs
      arg 1
      arg 1
      rw [ex606]
    conv =>
      rhs
      arg 1
      rw [ex606]
  by_cases h1 : ∃ b1, b1 ∈ keys ∧ R a1 b1 > 0 ∧ (if ∃ x, x ∈ heads ∧ F x b1 c1 > 0 then 1 else 0) > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨b2, hb1, hb2, hb3⟩ := h1
  have hb3_1 : ∃ x, x ∈ heads ∧ F x b2 c1 > 0 := by
    by_cases hF_ : ∃ x, x ∈ heads ∧ F x b2 c1 > 0
    exact hF_
    rw [if_neg hF_] at hb3
    contradiction
  clear hb3
  obtain ⟨x1, hx1, hx2⟩ := hb3_1
  rw [if_pos]
  exists x1
  constructor
  exact hx1
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b2
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  apply h1
  obtain ⟨b3, hb4, hb5⟩ := h2
  have hb5_1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ F b3 b c1 > 0 := by
    by_cases hF_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ F b3 b c1 > 0
    exact hF_
    rw [if_neg hF_] at hb5
    contradiction
  clear hb5
  obtain ⟨b4, hb6, hb7, hb8⟩ := hb5_1
  exists b4
  constructor
  exact hb6
  constructor
  exact hb7
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b3

-- 915: head distributes over multi-head aggregate on the left.
theorem ex915 (keys : List B) (heads : List H) (F : H -> WRel A B) (S : WRel B C) :
    wHead keys (wMHA heads F) S
      =
    wMHA heads (fun h => wHead keys (F h) S) := by
  -- Hint: unfold wHead/wMHA; ex864.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wMHA, wsumW, wBool]
  conv =>
    conv =>
      lhs
      arg 1
      arg 1
      intro b1
      rhs
      arg 1
      arg 1
      arg 1
      rw [ex606]
    conv =>
      rhs
      arg 1
      rw [ex606]
  by_cases h1 : ∃ b1, b1 ∈ keys ∧ (if ∃ x, x ∈ heads ∧ F x a1 b1 > 0 then 1 else 0) > 0 ∧ S b1 c1 > 0
  -- pos
  rw [if_pos h1]
  obtain ⟨b2, hb1, hb2, hb3⟩ := h1
  have hb2_1 : ∃ x, x ∈ heads ∧ F x a1 b2 > 0 := by
    by_cases hF_ : ∃ x, x ∈ heads ∧ F x a1 b2 > 0
    exact hF_
    rw [if_neg hF_] at hb2
    contradiction
  clear hb2
  obtain ⟨x1, hx1, hx2⟩ := hb2_1
  rw [if_pos]
  exists x1
  constructor
  exact hx1
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b2
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  apply h1
  obtain ⟨b3, hb4, hb5⟩ := h2
  have hb5_1 : ∃ b, b ∈ keys ∧ F b3 a1 b > 0 ∧ S b c1 > 0 := by
    by_cases hF_ : ∃ b, b ∈ keys ∧ F b3 a1 b > 0 ∧ S b c1 > 0
    exact hF_
    rw [if_neg hF_] at hb5
    contradiction
  clear hb5
  obtain ⟨b4, hb6, hb7, hb8⟩ := hb5_1
  exists b4
  constructor
  exact hb6
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b3
  exact hb8

end TL
