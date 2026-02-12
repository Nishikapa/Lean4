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
  -- TODO
  -- Hint: unfold wHead; use ex867.
  sorry

--------------------------------------------------------------------------------
-- 906-910: Graph-style head formulas
--------------------------------------------------------------------------------

-- 906: graph on the left gives pullback-with-key-gate mask form.
theorem ex906 (keys : List B) (f : A -> B) (S : WRel B C) :
    wHead keys (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys) := by
  -- TODO
  -- Hint: unfold wHead; use ex848.
  sorry

-- 907: if every f a is ∈ keys, graph-left head drops the gate.
theorem ex907 (keys : List B) (f : A -> B) (S : WRel B C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) S
        =
      (fun a c => wBool S (f a) c) := by
  -- TODO
  -- Hint: unfold wHead; use ex850.
  sorry

-- 908: graph-graph head as one mask.
theorem ex908 (keys : List B) (f : A -> B) (g : B -> C) :
    wHead keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  -- Hint: unfold wHead; use ex849.
  sorry

-- 909: graph-graph head under key coverage becomes composed graph.
theorem ex909 (keys : List B) (f : A -> B) (g : B -> C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) (wGraph g)
        =
      wGraph (fun a => g (f a)) := by
  -- TODO
  -- Hint: unfold wHead; use ex836 (or ex870).
  sorry

-- 910: singleton multi-head aggregate is just bool of that head.
theorem ex910 (h0 : H) (F : H -> WRel A C) :
    wMHA [h0] F = wBool (F h0) := by
  -- TODO
  -- Hint:
  --   * unfold wMHA / wsumW on singleton
  --   * or use ex842 + ex841
  sorry

--------------------------------------------------------------------------------
-- 911-915: Multi-head algebra and interaction with head
--------------------------------------------------------------------------------

-- 911: append of head list becomes OR (wOr).
theorem ex911 (heads1 heads2 : List H) (F : H -> WRel A C) :
    wMHA (heads1 ++ heads2) F
      =
    wOr (wMHA heads1 F) (wMHA heads2 F) := by
  -- TODO
  -- Hint: unfold wMHA; ex852 + definition of wOr.
  sorry

-- 912: each selected head is below the aggregate.
theorem ex912 (heads : List H) (F : H -> WRel A C) (h : H) :
    h ∈ heads ->
      WLe (wBool (F h)) (wMHA heads F) := by
  -- TODO
  -- Hint: unfold wMHA; ex857.
  sorry

-- 913: monotonicity ∈ head-list inclusion.
theorem ex913 (heads heads' : List H) (F : H -> WRel A C) :
    (∀ h, h ∈ heads -> h ∈ heads') ->
      WLe (wMHA heads F) (wMHA heads' F) := by
  -- TODO
  -- Hint: unfold wMHA; ex858.
  sorry

-- 914: head distributes over multi-head aggregate on the right.
theorem ex914 (keys : List B) (R : WRel A B) (heads : List H) (F : H -> WRel B C) :
    wHead keys R (wMHA heads F)
      =
    wMHA heads (fun h => wHead keys R (F h)) := by
  -- TODO
  -- Hint: unfold wHead/wMHA; ex863.
  sorry

-- 915: head distributes over multi-head aggregate on the left.
theorem ex915 (keys : List B) (heads : List H) (F : H -> WRel A B) (S : WRel B C) :
    wHead keys (wMHA heads F) S
      =
    wMHA heads (fun h => wHead keys (F h) S) := by
  -- TODO
  -- Hint: unfold wHead/wMHA; ex864.
  sorry

end TL
