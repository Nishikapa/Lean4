--------------------------------------------------------------------------------
-- Basic_931.lean
-- Exercise set 931-945 (fast-track 13)
-- Theme: causal masking, prefix-key algebra, and counterexamples.
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_916.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_916

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {C : Type}

--------------------------------------------------------------------------------
-- 0) New helpers: causal mask and causal head (Nat-indexed)
--------------------------------------------------------------------------------

noncomputable def wCausalQK (QK : WRel Nat Nat) : WRel Nat Nat :=
  wMask QK (fun q k => k <= q)

noncomputable def wCausalHead (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) : WRel Nat C :=
  wHead keys (wCausalQK QK) KV

def causalKeys (q : Nat) (keys : List Nat) : List Nat :=
  keys.filter (fun k => decide (k <= q))

--------------------------------------------------------------------------------
-- 931-935: Causal core + nontriviality checks
--------------------------------------------------------------------------------

-- 931: support of causal-QK is support(QK) intersect (k <= q).
theorem ex931 (QK : WRel Nat Nat) :
    wSupp (wCausalQK QK) = relMul (wSupp QK) (fun q k => k <= q) := by
  -- Hint: unfold wCausalQK and use ex614.
  funext n1 n2
  dsimp [wSupp, wCausalQK, wMask, maskW, relMul]
  by_cases h1 : n2 ≤ n1
  rw [if_pos h1]
  rw [Nat.mul_one]
  apply propext
  constructor
  intro h2
  constructor
  exact h2
  exact h1
  intro h3
  obtain ⟨h4, h5⟩ := h3
  exact h4
  rw [if_neg h1]
  rw [Nat.mul_zero]
  apply propext
  constructor
  intro h5
  contradiction
  intro h6
  obtain ⟨h7, h8⟩ := h6
  contradiction

-- 932: causal head is below unmasked head.
theorem ex932 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) :
    WLe (wCausalHead keys QK KV) (wHead keys QK KV) := by
  -- Hint: unfold wCausalHead; use ex903 with M := (fun q k => k <= q).
  rw [WLe]
  intro n1 c1
  dsimp [wCausalHead, wHead, wMask, maskW, wReachComp, relCompList, wSupp, wCausalQK]
  by_cases h1 : ∃ b, b ∈ keys ∧ (QK n1 b * if b ≤ n1 then 1 else 0) > 0 ∧ KV b c1 > 0
  obtain ⟨b1, h2, h3, h4⟩ := h1
  obtain h3_1 := Nat.pos_of_mul_pos_left h3
  obtain h3_2 := Nat.pos_of_mul_pos_right h3
  clear h3
  have h3_3 : b1 ≤ n1 := by
    by_cases h_ : b1 ≤ n1
    exact h_
    rw [if_neg h_] at h3_1
    contradiction
  clear h3_1
  rw [if_pos]
  rw [if_pos]
  apply Nat.le_refl
  exists b1
  exists b1
  constructor
  exact h2
  constructor
  apply Nat.mul_pos
  exact h3_2
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h3_3
  exact h4
  rw [if_neg]
  apply Nat.zero_le
  intro h5
  obtain ⟨b2, h6, h7, h8⟩ := h5
  obtain h7_1 := Nat.pos_of_mul_pos_left h7
  obtain h7_2 := Nat.pos_of_mul_pos_right h7
  clear h7
  have h7_3 : b2 ≤ n1 := by
    by_cases h_ : b2 ≤ n1
    exact h_
    rw [if_neg h_] at h7_1
    contradiction
  clear h7_1
  apply h1
  exists b2
  constructor
  exact h6
  constructor
  apply Nat.mul_pos
  exact h7_2
  rw [if_pos]
  apply Nat.zero_lt_one
  exact h7_3
  exact h8

-- 933: applying causal mask twice is idempotent.
theorem ex933 (QK : WRel Nat Nat) :
    wCausalQK (wCausalQK QK) = wCausalQK QK := by
  -- Hint: pointwise by_cases on (k <= q).
  funext n1 n2
  dsimp [wCausalQK, wMask, maskW]
  by_cases h1 : n2 ≤ n1
  rw [if_pos h1]
  rw [Nat.mul_one]
  rw [if_neg h1]
  rw [Nat.mul_zero]
  rw [Nat.mul_zero]

-- 934: strict loss can happen (causal head may drop an edge).
theorem ex934 :
    ∃ (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat Nat) (q c : Nat),
      wHead keys QK KV q c = 1 ∧
      wCausalHead keys QK KV q c = 0 := by
  -- Hint: construct one future-only witness key.

  -- noncomputable def maskW {α β : Type} (M : Rel α β) : WRel α β := by
  --   classical
  --   exact fun a b => if M a b then 1 else 0

  -- noncomputable def wMask {α β : Type} (R : WRel α β) (M : Rel α β) : WRel α β :=
  --   fun a b => R a b * maskW M a b

  -- noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   maskW (relCompList keys (wSupp R) (wSupp S))
  -- noncomputable def wReachComp (keys : List β) (R : WRel α β) (S : WRel β γ) : WRel α γ :=
  --   fun a c => if (∃ b, b ∈ keys ∧ (R a b > 0) ∧ (S b c > 0)) then 1 else 0

  -- noncomputable def wHead (keys : List B) (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  --   wReachComp keys QK KV
  -- noncomputable def wHead (keys : List B) (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  --   fun a c => if (∃ b, b ∈ keys ∧ (QK a b > 0) ∧ (KV b c > 0)) then 1 else 0

  -- noncomputable def wCausalQK (QK : WRel Nat Nat) : WRel Nat Nat :=
  --   wMask QK (fun q k => k <= q)
  -- noncomputable def wCausalQK (QK : WRel Nat Nat) : WRel Nat Nat :=
  --   fun a b => QK a b * if b <= a then 1 else 0

  -- noncomputable def wCausalHead (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) : WRel Nat C :=
  --   wHead keys (wCausalQK QK) KV
  -- noncomputable def wCausalHead (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) : WRel Nat C :=
  --   fun a c => if (∃ b, b ∈ keys ∧ ((QK a b * if b <= a then 1 else 0) > 0) ∧ (KV b c > 0)) then 1 else 0

  -- 以下のような条件を満たす、(keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat Nat) (q c : Nat)の組が存在する。
  -- (QK q b > 0) 且つ (KV b c > 0)となるようなbがkey内に存在すること
  -- ((QK q b * if b <= q then 1 else 0) > 0) 且つ (KV b c > 0)となるようなbがkey内に存在しないこと

  exists [1]                                          -- keys
  exists (fun q k => if q = 0 ∧ k = 1 then 1 else 0) -- QK
  exists (fun k c => if k = 1 ∧ c = 0 then 1 else 0) -- KV
  exists 0                                            -- q
  exists 0                                            -- c

  dsimp [wHead, wCausalHead, wCausalQK, wMask, maskW, wReachComp, relCompList, wSupp]

  have h_pos : ∃ b, b ∈ [1] ∧ (if 0 = 0 ∧ b = 1 then 1 else 0) > 0 ∧ (if b = 1 ∧ 0 = 0 then 1 else 0) > 0 := by
    exists 1

  rw [if_pos h_pos]

  constructor
  rfl

  rw [if_neg]
  intro h5
  obtain ⟨b2, h6, h7, h8⟩ := h5
  rw [List.mem_singleton] at h6
  rw [h6] at h7
  rw [h6] at h8
  obtain h7_1 := Nat.pos_of_mul_pos_left h7
  obtain h7_2 := Nat.pos_of_mul_pos_right h7
  clear h7
  have h7_3 : 1 ≤ 0 := by
    by_cases h_ : 1 ≤ 0
    exact h_
    rw [if_neg h_] at h7_1
    contradiction
  clear h7_1
  obtain h7_4 :=
    Nat.not_succ_le_zero 0 h7_3
  exact h7_4

-- 935: causal head is not always equal to ordinary head.
theorem ex935 :
    ¬ (∀ (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat Nat),
      wCausalHead keys QK KV = wHead keys QK KV) := by
  -- Hint: derive from ex934.

  intro h1
  obtain ⟨keys, QK, KV, q, c, hEx934_1, hEx934_2⟩ := ex934

  obtain h1_1 :=
    h1 keys QK

  have h2 : wCausalHead keys QK KV q c = wHead keys QK KV q c := by
    rw [h1_1]

  rw [hEx934_1] at h2
  rw [hEx934_2] at h2
  contradiction

--------------------------------------------------------------------------------
-- 936-941: Algebra of causalKeys (filter-based)
--------------------------------------------------------------------------------

-- 936: members of causalKeys come from keys.
theorem ex936 (q k : Nat) (keys : List Nat) :
    List.Mem k (causalKeys q keys) -> List.Mem k keys := by
  -- TODO
  -- Hint: unfold causalKeys; use List.mem_filter.mp.
  sorry

-- 937: members of causalKeys satisfy k <= q.
theorem ex937 (q k : Nat) (keys : List Nat) :
    List.Mem k (causalKeys q keys) -> k <= q := by
  -- TODO
  -- Hint: unfold causalKeys; use List.mem_filter.mp and decide.
  sorry

-- 938: if k in keys and k <= q, then k in causalKeys q keys.
theorem ex938 (q k : Nat) (keys : List Nat) :
    List.Mem k keys -> k <= q -> List.Mem k (causalKeys q keys) := by
  -- TODO
  -- Hint: unfold causalKeys; use List.mem_filter.mpr.
  sorry

-- 939: causalKeys distributes over append.
theorem ex939 (q : Nat) (keys1 keys2 : List Nat) :
    causalKeys q (keys1 ++ keys2)
      =
    causalKeys q keys1 ++ causalKeys q keys2 := by
  -- TODO
  -- Hint: unfold causalKeys and use filter-append.
  sorry

-- 940: causalKeys is idempotent.
theorem ex940 (q : Nat) (keys : List Nat) :
    causalKeys q (causalKeys q keys) = causalKeys q keys := by
  -- TODO
  -- Hint: filter with the same predicate twice.
  sorry

-- 941: cons expansion for causalKeys.
theorem ex941 (q k : Nat) (keys : List Nat) :
    causalKeys q (k :: keys)
      =
    (if k <= q then k :: causalKeys q keys else causalKeys q keys) := by
  -- TODO
  -- Hint: unfold causalKeys and split on (k <= q).
  sorry

--------------------------------------------------------------------------------
-- 942-945: Causal head rewrites and graph specialization
--------------------------------------------------------------------------------

-- 942: row q of causal head equals ordinary head over causalKeys q.
theorem ex942 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) (q : Nat) :
    forall c, wHead (causalKeys q keys) QK KV q c = wCausalHead keys QK KV q c := by
  -- TODO
  -- Hint: same witness condition at row q.
  sorry

-- 943: causal head over empty keys is zero.
theorem ex943 (QK : WRel Nat Nat) (KV : WRel Nat C) :
    wCausalHead ([] : List Nat) QK KV = wZero Nat C := by
  -- TODO
  -- Hint: unfold wCausalHead; use ex918 (or ex866 via wHead).
  sorry

-- 944: causal head is 0/1-valued.
theorem ex944 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) :
    wBool (wCausalHead keys QK KV) = wCausalHead keys QK KV := by
  -- TODO
  -- Hint: unfold wCausalHead; use ex920.
  sorry

-- 945: graph-left causal head under key coverage collapses to a causal gate.
theorem ex945 (keys : List Nat) (f : Nat -> Nat) (S : WRel Nat C) :
    (forall a : Nat, List.Mem (f a) keys) ->
      wCausalHead keys (wGraph f) S
        =
      wMask (fun a c => wBool S (f a) c) (fun a _ => f a <= a) := by
  -- TODO
  -- Hint: combine ex907 with the remaining causal mask.
  sorry

end TL
