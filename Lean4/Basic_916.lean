--------------------------------------------------------------------------------
-- Basic_916.lean
-- Exercise set 916-930 (fast-track 12)
-- Theme: head algebra, mask laws, and two-hop head blocks.
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_901.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_901

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {A B C D H : Type}

--------------------------------------------------------------------------------
-- 0) New helper: two-hop head block
--------------------------------------------------------------------------------

noncomputable def wTwoHop (keysB : List B) (keysC : List C)
    (R : WRel A B) (S : WRel B C) (T : WRel C D) : WRel A D :=
  wHead keysC (wHead keysB R S) T

--------------------------------------------------------------------------------
-- 916-920: Algebra of wHead (OR / zero / bool)
--------------------------------------------------------------------------------

-- 916: left OR distribution for head.
theorem ex916 (keys : List B) (R R' : WRel A B) (S : WRel B C) :
    wHead keys (wOr R R') S
      =
    wOr (wHead keys R S) (wHead keys R' S) := by
  -- Hint: unfold wHead and apply ex876.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wOr , wBool, wAdd]
  by_cases h1 : ∃ b, b ∈ keys ∧ (if R a1 b + R' a1 b > 0 then 1 else 0) > 0 ∧ S b c1 > 0
  rw [if_pos]
  obtain ⟨b1, hb1, hRr1, hSc1⟩ := h1
  have h2 : R a1 b1 + R' a1 b1 > 0 := by
    by_cases h_ : R a1 b1 + R' a1 b1 > 0
    exact h_
    rw [if_neg h_] at hRr1
    contradiction
  clear hRr1
  rw [gt_iff_lt] at h2
  rw [Nat.add_pos_iff_pos_or_pos] at h2
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain h2_1 | h2_2 := h2
  left
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  right
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  obtain ⟨b2, hb2, hRr2, hSc2⟩ := h1
  have h3 : R a1 b2 + R' a1 b2 > 0 := by
    by_cases h_ : R a1 b2 + R' a1 b2 > 0
    exact h_
    rw [if_neg h_] at hRr2
    contradiction
  clear hRr2
  exists b2
  constructor
  exact hb2
  constructor
  rw [gt_iff_lt]
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h3
  exact hSc2
  rw [if_neg]
  rw [if_neg]
  intro h3
  apply h1
  rw [gt_iff_lt] at h3
  rw [Nat.add_pos_iff_pos_or_pos] at h3
  obtain h3_1 | h3_2 := h3
  have h4 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h3_1
    contradiction
  clear h3_1
  obtain ⟨b3, hb3, hR3, hSc3⟩ := h4
  exists b3
  constructor
  exact hb3
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact hR3
  exact hSc3
  have h5 : ∃ b, b ∈ keys ∧ R' a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R' a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h3_2
    contradiction
  clear h3_2
  obtain ⟨b4, hb4, hR4, hSc4⟩ := h5
  exists b4
  constructor
  exact hb4
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact hR4
  exact hSc4
  intro h6
  apply h1
  obtain ⟨b5, hb5, hR5, hSc5⟩ := h6
  have h7 : R a1 b5 + R' a1 b5 > 0 := by
    by_cases h_ : R a1 b5 + R' a1 b5 > 0
    exact h_
    rw [if_neg h_] at hR5
    contradiction
  clear hR5
  exists b5
  constructor
  exact hb5
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h7
  exact hSc5

-- 917: right OR distribution for head.
theorem ex917 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    wHead keys R (wOr S S')
      =
    wOr (wHead keys R S) (wHead keys R S') := by
  -- Hint: unfold wHead and apply ex877.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wOr , wBool, wAdd]
  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if S b c1 + S' b c1 > 0 then 1 else 0) > 0
  obtain ⟨b1, hb1, hR1, hSOr1⟩ := h1
  have h2 : S b1 c1 + S' b1 c1 > 0 := by
    by_cases h_ : S b1 c1 + S' b1 c1 > 0
    exact h_
    rw [if_neg h_] at hSOr1
    contradiction
  clear hSOr1
  rw [gt_iff_lt] at h2
  rw [Nat.add_pos_iff_pos_or_pos] at h2
  rw [if_pos]
  rw [if_pos]
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  obtain h2_1 | h2_2 := h2
  left
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  right
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b1
  exists b1
  constructor
  exact hb1
  constructor
  exact hR1
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  exact h2
  rw [if_neg]
  rw [if_neg]
  intro h2
  apply h1
  rw [gt_iff_lt] at h2
  rw [Nat.add_pos_iff_pos_or_pos] at h2
  obtain h2_1 | h2_2 := h2
  have h3 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
    exact h_
    rw [if_neg h_] at h2_1
    contradiction
  clear h2_1
  obtain ⟨b2, hb2, hR2, hS2⟩ := h3
  exists b2
  constructor
  exact hb2
  constructor
  exact hR2
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact hS2
  have h4 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S' b c1 > 0 := by
    by_cases h_ : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S' b c1 > 0
    exact h_
    rw [if_neg h_] at h2_2
    contradiction
  clear h2_2
  obtain ⟨b3, hb3, hR3, hS3⟩ := h4
  exists b3
  constructor
  exact hb3
  constructor
  exact hR3
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  right
  exact hS3
  intro h5
  apply h1
  obtain ⟨b4, hb4, hR4, hS4⟩ := h5
  have h6 : S b4 c1 + S' b4 c1 > 0 := by
    by_cases h_ : S b4 c1 + S' b4 c1 > 0
    exact h_
    rw [if_neg h_] at hS4
    contradiction
  clear hS4
  exists b4
  constructor
  exact hb4
  constructor
  exact hR4
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h6

-- 918: zero on the left gives zero.
theorem ex918 (keys : List B) (S : WRel B C) :
    wHead keys (wZero A B) S = wZero A C := by
  -- Hint: unfold wHead and apply ex878.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wOr , wBool, wAdd, wZero]
  rw [if_neg]
  intro h1
  obtain ⟨b1, hb1, hR1, hS1⟩ := h1
  contradiction

-- 919: zero on the right gives zero.
theorem ex919 (keys : List B) (R : WRel A B) :
    wHead keys R (wZero B C) = wZero A C := by
  -- Hint: unfold wHead and apply ex879.
  funext a1 c1
  dsimp [wHead, wReachComp, maskW, relCompList, wSupp, wZero]
  rw [if_neg]
  intro h1
  obtain ⟨b1, hb1, hR1, hS1⟩ := h1
  contradiction

-- 920: head is already 0/1-valued.
theorem ex920 (keys : List B) (R : WRel A B) (S : WRel B C) :
    wBool (wHead keys R S) = wHead keys R S := by
  -- Hint: unfold wHead and apply ex880.
  funext a1 c1
  dsimp [wBool, maskW, wSupp, wHead, wReachComp, relCompList]
  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ S b c1 > 0
  rw [if_pos h1]
  obtain ⟨b1, hb1, hR1, hS1⟩ := h1
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  contradiction

--------------------------------------------------------------------------------
-- 921-925: Mask laws for wMaskedHead
--------------------------------------------------------------------------------

-- 921: True-mask does nothing.
theorem ex921 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (fun _ _ => True) QK KV
      =
    wHead keys QK KV := by
  -- Hint: unfold wMaskedHead and use ex516.
  funext a1 c1
  dsimp [wMaskedHead, wHead, wReachComp, maskW, relCompList, wSupp, wMask]
  by_cases h1 : ∃ b, b ∈ keys ∧ (QK a1 b * if True then 1 else 0) > 0 ∧ KV b c1 > 0
  obtain ⟨b1, hb1, hQK1, hKV1⟩ := h1
  rw [gt_iff_lt] at hQK1
  obtain hQK1_1 := Nat.pos_of_mul_pos_left hQK1
  obtain hQK1_2 := Nat.pos_of_mul_pos_right hQK1
  clear hQK1
  rw [if_pos]
  rw [if_pos]
  exists b1
  exists b1
  constructor
  exact hb1
  constructor
  apply Nat.mul_pos
  exact hQK1_2
  rw [if_pos]
  apply Nat.zero_lt_one
  apply True.intro
  exact hKV1
  rw [if_neg]
  rw [if_neg]
  intro h2
  apply h1
  obtain ⟨b2, hb2, hQK2, hKV2⟩ := h2
  exists b2
  constructor
  exact hb2
  constructor
  rw [if_pos]
  rw [Nat.mul_one]
  exact hQK2
  apply True.intro
  exact hKV2
  intro h3
  apply h1
  obtain ⟨b3, hb3, hQK3, hKV3⟩ := h3
  obtain hQK3_1 := Nat.pos_of_mul_pos_left hQK3
  obtain hQK3_2 := Nat.pos_of_mul_pos_right hQK3
  clear hQK3
  exists b3
  constructor
  exact hb3
  constructor
  apply Nat.mul_pos
  exact hQK3_2
  rw [if_pos]
  apply Nat.zero_lt_one
  apply True.intro
  exact hKV3

-- 922: False-mask kills the head.
theorem ex922 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (fun _ _ => False) QK KV
      =
    wZero A C := by
  -- TODO
  -- Hint: unfold wMaskedHead; use ex517 then ex918.
  sorry

-- 923: mask monotonicity on the left relation.
theorem ex923 (keys : List B) (M M' : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    (forall a b, M a b -> M' a b) ->
      WLe (wMaskedHead keys M QK KV)
          (wMaskedHead keys M' QK KV) := by
  -- TODO
  -- Hint:
  --   * compare supports via ex902
  --   * witness for M is also witness for M'.
  sorry

-- 924: adding an explicit key-membership conjunct is redundant.
theorem ex924 (keys : List B) (M : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (fun a b => M a b ∧ b ∈ keys) QK KV
      =
    wMaskedHead keys M QK KV := by
  -- TODO
  -- Hint: in relCompList, witness b already satisfies b ∈ keys.
  sorry

-- 925: masked graph-left head has an explicit gate formula.
theorem ex925 (keys : List B) (M : Rel A B) (f : A -> B) (S : WRel B C) :
    wMaskedHead keys M (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c)
          (fun a _ => f a ∈ keys ∧ M a (f a)) := by
  -- TODO
  -- Hint: combine ex906 with support behavior of wMask / wGraph.
  sorry

--------------------------------------------------------------------------------
-- 926-930: Two-hop head blocks and graph collapse
--------------------------------------------------------------------------------

-- 926: reassociation of two-hop head block.
theorem ex926 (keysB : List B) (keysC : List C)
    (R : WRel A B) (S : WRel B C) (T : WRel C D) :
    wTwoHop keysB keysC R S T
      =
    wHead keysB R (wHead keysC S T) := by
  -- TODO
  -- Hint: unfold wTwoHop/wHead and use ex830.
  sorry

-- 927: two-hop block with left zero is zero.
theorem ex927 (keysB : List B) (keysC : List C)
    (S : WRel B C) (T : WRel C D) :
    wTwoHop keysB keysC (wZero A B) S T = wZero A D := by
  -- TODO
  -- Hint: ex926 + ex918.
  sorry

-- 928: two-hop block with middle zero is zero.
theorem ex928 (keysB : List B) (keysC : List C)
    (R : WRel A B) (T : WRel C D) :
    wTwoHop keysB keysC R (wZero B C) T = wZero A D := by
  -- TODO
  -- Hint: unfold wTwoHop; first kill inner head by ex919, then ex918.
  sorry

-- 929: two-hop block with right zero is zero.
theorem ex929 (keysB : List B) (keysC : List C)
    (R : WRel A B) (S : WRel B C) :
    wTwoHop keysB keysC R S (wZero C D) = wZero A D := by
  -- TODO
  -- Hint: unfold wTwoHop and use ex919.
  sorry

-- 930: graph-graph-graph two-hop collapse to composed graph under key coverage.
theorem ex930 (keysB : List B) (keysC : List C)
    (f : A -> B) (g : B -> C) (h : C -> D) :
    (forall a : A, f a ∈ keysB) ->
    (forall a : A, g (f a) ∈ keysC) ->
      wTwoHop keysB keysC (wGraph f) (wGraph g) (wGraph h)
        =
      wGraph (fun a => h (g (f a))) := by
  -- TODO
  -- Hint:
  --   * ex926 to reassociate
  --   * ex909 on (f,g) and then on (g o f, h).
  sorry

end TL
