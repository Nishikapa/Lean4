--------------------------------------------------------------------------------
-- Basic_886.lean
-- Exercise set 886-900 (fast-track 10)
-- Theme: AND-style 0/1 semantics and interactions with reach/sum/graph.
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_871.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_871

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {A B C D E I : Type}

--------------------------------------------------------------------------------
-- 0) New helper: AND on 0/1 relations
--------------------------------------------------------------------------------

-- AND on support (pointwise meet), lifted to 0/1 via wBool.
noncomputable def wAnd (R S : WRel A B) : WRel A B :=
  wBool (wMul R S)

--------------------------------------------------------------------------------
-- 886-890: Basic laws of wAnd
--------------------------------------------------------------------------------

-- 886: support(wAnd) is conjunction of supports.
theorem ex886 (R S : WRel A B) :
    wSupp (wAnd R S) = relMul (wSupp R) (wSupp S) := by
  -- TODO
  -- Hint:
  --   * unfold wAnd
  --   * ex796: wSupp (wBool X) = wSupp X
  --   * ex667: wSupp (wMul R S) = relMul (wSupp R) (wSupp S)
  sorry

-- 887: wAnd is commutative.
theorem ex887 (R S : WRel A B) :
    wAnd R S = wAnd S R := by
  -- Hint: unfold wAnd, then use ex668 (wMul commutative).
  funext a1 b1
  dsimp [wAnd, wBool, maskW, wSupp, wMul]
  by_cases h1 : R a1 b1 * S a1 b1 > 0

  -- pos
  rw [if_pos h1]
  rw [if_pos]
  rw [Nat.mul_comm]
  exact h1

  -- neg
  rw [if_neg h1]
  rw [if_neg]
  rw [Nat.mul_comm]
  exact h1

-- 888: wAnd is associative.
theorem ex888 (R S T : WRel A B) :
    wAnd (wAnd R S) T = wAnd R (wAnd S T) := by
  -- Hint:
  --   * compare supports via ex886
  --   * use relMul associativity pointwise
  --   * finish with maskW / wBool extensionality
  funext a1 b1
  dsimp [wAnd, wBool, maskW, wSupp, wMul]
  by_cases h1 : (if R a1 b1 * S a1 b1 > 0 then 1 else 0) * T a1 b1 > 0
  -- pos
  rw [gt_iff_lt] at h1
  obtain h1_1 := Nat.pos_of_mul_pos_left h1
  have h1_2 : R a1 b1 * S a1 b1 > 0 := by
    by_cases h_ : R a1 b1 * S a1 b1 > 0
    exact h_
    rw [if_neg h_] at h1
    rw [Nat.zero_mul] at h1
    contradiction
  clear h1
  obtain h1_3 := Nat.pos_of_mul_pos_left h1_2
  obtain h1_4 := Nat.pos_of_mul_pos_right h1_2
  clear h1_2
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [Nat.mul_one]
  exact h1_4
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h1_3
  exact h1_1
  rw [if_pos]
  rw [Nat.one_mul]
  exact h1_1
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h1_4
  exact h1_3

  -- neg
  rw [if_neg]
  rw [if_neg]
  intro h2
  rw [gt_iff_lt] at h2

  --obtain h2_1 := Nat.pos_of_mul_pos_left h2
  have h2_1 := Nat.pos_of_mul_pos_right h2
  have h2_2 : S a1 b1 * T a1 b1 > 0 := by
    by_cases h_ : S a1 b1 * T a1 b1 > 0
    exact h_
    rw [if_neg h_] at h2
    rw [Nat.mul_zero] at h2
    contradiction
  clear h2
  rw [gt_iff_lt] at h2_2
  obtain h2_3 := Nat.pos_of_mul_pos_left h2_2
  obtain h2_4 := Nat.pos_of_mul_pos_right h2_2
  clear h2_2

  apply h1
  rw [gt_iff_lt]
  apply Nat.mul_pos
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h2_1
  exact h2_4
  exact h2_3
  intro h3
  apply h1
  rw [if_pos]
  rw [Nat.one_mul]
  rw [gt_iff_lt] at h3
  obtain h3_1 := Nat.pos_of_mul_pos_left h3
  exact h3_1
  obtain h3_2 := Nat.pos_of_mul_pos_right h3
  have h3_3 : R a1 b1 * S a1 b1 > 0 := by
    by_cases h_ : R a1 b1 * S a1 b1 > 0
    exact h_
    rw [if_neg h_] at h3
    rw [Nat.zero_mul] at h3
    contradiction
  exact h3_3

-- 889: idempotence (AND with itself collapses to bool).
theorem ex889 (R : WRel A B) :
    wAnd R R = wBool R := by
  -- Hint: unfold wAnd and use positivity of x*x.
  funext a1 b1
  dsimp [wAnd, wBool, maskW, wSupp, wMul]
  by_cases h1 : R a1 b1 * R a1 b1 > 0
  -- pos
  rw [if_pos h1]
  rw [if_pos]
  rw [gt_iff_lt] at h1
  obtain h1_1 := Nat.pos_of_mul_pos_left h1
  exact h1_1
  -- neg
  rw [if_neg h1]
  rw [if_neg]
  intro h2
  apply h1
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h2
  exact h2

-- 890: absorption with OR.
theorem ex890 (R S : WRel A B) :
    wAnd R (wOr R S) = wBool R := by
  -- Hint:
  --   * support side is R /\ (R \/ S)
  --   * use ex871 for wOr support
  --   * conclude by extensionality on 0/1 relations
  funext a1 b1
  dsimp [wAnd, wOr, wBool, maskW, wSupp, wMul, wAdd]
  by_cases h1 : (R a1 b1 * if R a1 b1 + S a1 b1 > 0 then 1 else 0) > 0
  -- pos
  rw [gt_iff_lt] at h1
  obtain h1_2 := Nat.pos_of_mul_pos_right h1
  clear h1
  rw [if_pos]
  rw [if_pos]
  exact h1_2
  rw [if_pos]
  rw [Nat.mul_one]
  exact h1_2
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h1_2
  -- neg
  rw [if_neg]
  rw [if_neg]
  intro h2
  apply h1
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h2
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact h2
  intro h3
  apply h1
  rw [gt_iff_lt]
  apply Nat.mul_pos
  rw [gt_iff_lt] at h3
  obtain h3_1 := Nat.pos_of_mul_pos_right h3
  exact h3_1
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  rw [gt_iff_lt] at h3
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  obtain h3_2 := Nat.pos_of_mul_pos_right h3
  exact h3_2

--------------------------------------------------------------------------------
-- 891-895: ReachComp with wAnd (inequalities + singleton equality)
--------------------------------------------------------------------------------

-- 891: AND on the left input can only decrease reach.
theorem ex891 (keys : List B) (R R' : WRel A B) (S : WRel B C) :
    WLe (wReachComp keys (wAnd R R') S)
        (wReachComp keys R S) := by
  -- Hint: unfold WLe; witness for left is also a witness for right.
  dsimp [WLe]
  intro a1 c1
  dsimp [wReachComp, wAnd, wBool, wSupp, wMul, maskW, relCompList]
  by_cases h1 :
    ∃ b, b ∈ keys ∧ (if R a1 b * R' a1 b > 0 then 1 else 0) > 0 ∧ S b c1 > 0

  -- pos
  obtain ⟨b0, hkey, hR_and, hS⟩ := h1
  have hR_and2 : R a1 b0 * R' a1 b0 > 0 := by
    by_cases h_ : R a1 b0 * R' a1 b0 > 0
    exact h_
    rw [if_neg h_] at hR_and
    contradiction
  clear hR_and
  rw [gt_iff_lt] at hR_and2
  obtain hR_1 := Nat.pos_of_mul_pos_left hR_and2
  obtain hR_2 := Nat.pos_of_mul_pos_right hR_and2
  clear hR_and2
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  exists b0
  exists b0
  constructor
  exact hkey
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hR_2
  exact hR_1
  exact hS

  -- neg
  rw [if_neg]
  apply Nat.zero_le
  intro h2
  apply h1
  obtain ⟨b0, hkey, hR_and, hS⟩ := h2
  have hR_and2 : R a1 b0 * R' a1 b0 > 0 := by
    by_cases h_ : R a1 b0 * R' a1 b0 > 0
    exact h_
    rw [if_neg h_] at hR_and
    contradiction
  obtain hR_and3 := Nat.pos_of_mul_pos_left hR_and2
  obtain hR_and4 := Nat.pos_of_mul_pos_right hR_and2
  clear hR_and
  clear hR_and2
  exists b0
  constructor
  exact hkey
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hR_and4
  exact hR_and3
  exact hS

-- 892: AND on the right input can only decrease reach.
theorem ex892 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    WLe (wReachComp keys R (wAnd S S'))
        (wReachComp keys R S) := by
  -- Hint: same witness argument as ex891.
  dsimp [WLe, wReachComp, wAnd, wBool, wSupp, wMul, maskW, relCompList]
  intro a1 c1
  by_cases h1 :
    ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if S b c1 * S' b c1 > 0 then 1 else 0) > 0
  -- pos
  obtain ⟨b0, hkey, hR, hS_and⟩ := h1
  have hS_and2 : S b0 c1 * S' b0 c1 > 0 := by
    by_cases h_ : S b0 c1 * S' b0 c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  exists b0
  exists b0
  constructor
  exact hkey
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3
  -- neg
  rw [if_neg]
  apply Nat.zero_le
  intro h2
  apply h1
  obtain ⟨b0, hkey, hR, hS_and⟩ := h2
  have hS_and2 : S b0 c1 * S' b0 c1 > 0 := by
    by_cases h_ : S b0 c1 * S' b0 c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  exists b0
  constructor
  exact hkey
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3

-- 893: left-AND reach implies AND of the two reaches.
theorem ex893 (keys : List B) (R R' : WRel A B) (S : WRel B C) :
    WLe (wReachComp keys (wAnd R R') S)
        (wAnd (wReachComp keys R S) (wReachComp keys R' S)) := by
  -- Hint: combine ex891 with the symmetric statement for R'.
  dsimp [WLe, wReachComp, wAnd, wBool, wSupp, wMul, maskW, relCompList]
  intro a1 c1
  by_cases h1 : ∃ b, b ∈ keys ∧ (if R a1 b * R' a1 b > 0 then 1 else 0) > 0 ∧ S b c1 > 0
  obtain ⟨b0, hkey, hR_and, hS⟩ := h1
  have hR_and2 : R a1 b0 * R' a1 b0 > 0 := by
    by_cases h_ : R a1 b0 * R' a1 b0 > 0
    exact h_
    rw [if_neg h_] at hR_and
    contradiction
  clear hR_and
  obtain hR_1 := Nat.pos_of_mul_pos_left hR_and2
  obtain hR_2 := Nat.pos_of_mul_pos_right hR_and2
  clear hR_and2
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b0
  exists b0
  exists b0
  constructor
  exact hkey
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hR_2
  exact hR_1
  exact hS
  rw [if_neg]
  apply Nat.zero_le
  intro h2
  apply h1
  obtain ⟨b0, hkey, hR_and, hS⟩ := h2
  have hR_and2 : R a1 b0 * R' a1 b0 > 0 := by
    by_cases h_ : R a1 b0 * R' a1 b0 > 0
    exact h_
    rw [if_neg h_] at hR_and
    contradiction
  clear hR_and
  obtain hR_1 := Nat.pos_of_mul_pos_left hR_and2
  obtain hR_2 := Nat.pos_of_mul_pos_right hR_and2
  clear hR_and2
  exists b0
  constructor
  exact hkey
  constructor
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hR_2
  exact hR_1
  exact hS

-- 894: right-AND reach implies AND of the two reaches.
theorem ex894 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    WLe (wReachComp keys R (wAnd S S'))
        (wAnd (wReachComp keys R S) (wReachComp keys R S')) := by
  -- Hint: same shape as ex893.
  dsimp [WLe, wReachComp, wAnd, wBool, wSupp, wMul, maskW, relCompList]
  intro a1 c1
  by_cases h1 : ∃ b, b ∈ keys ∧ R a1 b > 0 ∧ (if S b c1 * S' b c1 > 0 then 1 else 0) > 0
  obtain ⟨b0, hkey, hR, hS_and⟩ := h1
  -- pos
  have hS_and2 : S b0 c1 * S' b0 c1 > 0 := by
    by_cases h_ : S b0 c1 * S' b0 c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b0
  exists b0
  exists b0
  constructor
  exact hkey
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3
  -- neg
  rw [if_neg]
  apply Nat.zero_le
  intro h2
  apply h1
  obtain ⟨b0, hkey, hR, hS_and⟩ := h2
  have hS_and2 : S b0 c1 * S' b0 c1 > 0 := by
    by_cases h_ : S b0 c1 * S' b0 c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  exists b0
  constructor
  exact hkey
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3

-- 895: singleton keys fixes the witness, so right-AND distributes exactly.
theorem ex895 (b : B) (R : WRel A B) (S S' : WRel B C) :
    wReachComp [b] R (wAnd S S')
      =
    wAnd (wReachComp [b] R S) (wReachComp [b] R S') := by
  -- Hint: use ex867 to rewrite both sides to mask forms with the same b.
  funext a1 c1
  dsimp [wReachComp, wAnd, wBool, wSupp, wMul, maskW, relCompList]
  by_cases h1 : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ (if S b_1 c1 * S' b_1 c1 > 0 then 1 else 0) > 0
  -- pos
  obtain ⟨b0, hkey, hR, hS_and⟩ := h1
  have hS_and2 : S b0 c1 * S' b0 c1 > 0 := by
    by_cases h_ : S b0 c1 * S' b0 c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  rw [if_pos]
  rw [if_pos]
  rw [if_pos]
  rw [Nat.one_mul]
  rw [if_pos]
  apply Nat.zero_lt_one
  exists b0
  exists b0
  exists b0
  constructor
  exact hkey
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3
  -- neg
  rw [if_neg]
  rw [if_neg]
  intro h2
  apply h1
  rw [gt_iff_lt] at h2
  obtain h2_1 := Nat.pos_of_mul_pos_right h2
  obtain h2_2 := Nat.pos_of_mul_pos_left h2
  clear h2
  have h2_3 : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ S b_1 c1 > 0 := by
    by_cases h_ : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ S b_1 c1 > 0
    exact h_
    rw [if_neg] at h2_1
    contradiction
    intro h2_
    apply h_
    obtain ⟨b_1, hkey, hR, hS⟩ := h2_
    exists b_1
  clear h2_1
  obtain ⟨b1,h2_3_1,h2_3_2,h2_3_3⟩ := h2_3
  rw [List.mem_singleton] at h2_3_1
  rw [h2_3_1] at h2_3_2
  rw [h2_3_1] at h2_3_3
  have h2_4 : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ S' b_1 c1 > 0 := by
    by_cases h_ : ∃ b_1, b_1 ∈ [b] ∧ R a1 b_1 > 0 ∧ S' b_1 c1 > 0
    exact h_
    rw [if_neg] at h2_2
    contradiction
    intro h2_
    apply h_
    obtain ⟨b_1, hkey, hR, hS'⟩ := h2_
    exists b_1
  clear h2_2
  obtain ⟨b2,h2_4_1,h2_4_2,h2_4_3⟩ := h2_4
  rw [List.mem_singleton] at h2_4_1
  rw [h2_4_1] at h2_4_2
  rw [h2_4_1] at h2_4_3
  exists b
  constructor
  rw [List.mem_singleton]
  constructor
  exact h2_3_2
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact h2_3_3
  exact h2_4_3
  intro h3
  apply h1
  obtain ⟨b0, hkey, hR, hS_and⟩ := h3
  rw [List.mem_singleton] at hkey
  rw [hkey] at hR
  rw [hkey] at hS_and
  have hS_and2 : S b c1 * S' b c1 > 0 := by
    by_cases h_ : S b c1 * S' b c1 > 0
    exact h_
    rw [if_neg h_] at hS_and
    contradiction
  clear hS_and
  obtain hS_and3 := Nat.pos_of_mul_pos_left hS_and2
  obtain hS_and4 := Nat.pos_of_mul_pos_right hS_and2
  clear hS_and2
  exists b
  constructor
  rw [List.mem_singleton]
  constructor
  exact hR
  rw [if_pos]
  apply Nat.zero_lt_one
  rw [gt_iff_lt]
  apply Nat.mul_pos
  exact hS_and4
  exact hS_and3

--------------------------------------------------------------------------------
-- 896-900: wsumW / graph exercises with wAnd
--------------------------------------------------------------------------------

-- 896: indexwise AND-sum is below AND of the two sums.
theorem ex896 (keys : List I) (F G : I -> WRel A C) :
    WLe (wsumW keys (fun i => wAnd (F i) (G i)))
        (wAnd (wsumW keys F) (wsumW keys G)) := by
  -- TODO
  -- Hint:
  --   * ex845 gives support(WSUM)
  --   * same index i witnesses both sides on the right.
  sorry

-- 897: singleton version of ex896 is equality.
theorem ex897 (i0 : I) (F G : I -> WRel A C) :
    wsumW [i0] (fun i => wAnd (F i) (G i))
      =
    wAnd (wsumW [i0] F) (wsumW [i0] G) := by
  -- TODO
  -- Hint: unfold wsumW on singleton and simplify.
  sorry

-- 898: with left graph, right-AND distributes exactly (unique middle point f a).
theorem ex898 (keys : List B) (f : A -> B) (S S' : WRel B C) :
    wReachComp keys (wGraph f) (wAnd S S')
      =
    wAnd (wReachComp keys (wGraph f) S)
         (wReachComp keys (wGraph f) S') := by
  -- TODO
  -- Hint:
  --   * rewrite each reach by ex848
  --   * only b = f a can witness graph edges
  sorry

-- 899: immediate corollary of ex898 (idempotence on the right factor).
theorem ex899 (keys : List B) (f : A -> B) (S : WRel B C) :
    wReachComp keys (wGraph f) (wAnd S S)
      =
    wReachComp keys (wGraph f) S := by
  -- TODO
  -- Hint: ex898 + ex889 + ex824.
  sorry

-- 900: conjunction of two graph-reach outputs as one mask formula.
theorem ex900 (keys : List B) (f : A -> B) (g h : B -> C) :
    wAnd (wReachComp keys (wGraph f) (wGraph g))
         (wReachComp keys (wGraph f) (wGraph h))
      =
    maskW (fun a c => List.Mem (f a) keys /\ g (f a) = c /\ h (f a) = c) := by
  -- TODO
  -- Hint:
  --   * ex835 rewrites each graph-graph reach to a mask formula
  --   * then simplify conjunction of the two masks pointwise
  sorry

end TL
