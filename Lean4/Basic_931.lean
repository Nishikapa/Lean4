--------------------------------------------------------------------------------
-- Basic_931.lean
-- Exercise set 931-945 (fast-track 13)
-- Theme: causal masks and prefix-key reasoning for hard attention.
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
-- 931-935: Causal mask basics
--------------------------------------------------------------------------------

-- 931: support of causal-QK is support(QK) intersect (k <= q).
theorem ex931 (QK : WRel Nat Nat) :
    wSupp (wCausalQK QK) = relMul (wSupp QK) (fun q k => k <= q) := by
  -- TODO
  -- Hint: unfold wCausalQK; use ex614.
  sorry

-- 932: causal-QK is pointwise below QK.
theorem ex932 (QK : WRel Nat Nat) :
    WLe (wCausalQK QK) QK := by
  -- TODO
  -- Hint: unfold wCausalQK and use mask monotonicity.
  sorry

-- 933: applying the same causal mask twice is idempotent.
theorem ex933 (QK : WRel Nat Nat) :
    wCausalQK (wCausalQK QK) = wCausalQK QK := by
  -- TODO
  -- Hint: pointwise on (q,k), split by (k <= q).
  sorry

-- 934: causal head is below unmasked head.
theorem ex934 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) :
    WLe (wCausalHead keys QK KV) (wHead keys QK KV) := by
  -- TODO
  -- Hint: unfold wCausalHead and use ex903 with M := (fun q k => k <= q).
  sorry

-- 935: if all keys are <= q, causal mask does nothing on row q.
theorem ex935 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) (q : Nat) :
    (forall k, List.Mem k keys -> k <= q) ->
      forall c, wCausalHead keys QK KV q c = wHead keys QK KV q c := by
  -- TODO
  -- Hint: in row q, every witness key already satisfies the causal predicate.
  sorry

--------------------------------------------------------------------------------
-- 936-941: Properties of causalKeys
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

-- 938: if k is in keys and k <= q then k is in causalKeys q keys.
theorem ex938 (q k : Nat) (keys : List Nat) :
    List.Mem k keys -> k <= q -> List.Mem k (causalKeys q keys) := by
  -- TODO
  -- Hint: unfold causalKeys; use List.mem_filter.mpr.
  sorry

-- 939: causalKeys is monotone in q.
theorem ex939 (q1 q2 : Nat) (keys : List Nat) :
    q1 <= q2 ->
      forall k, List.Mem k (causalKeys q1 keys) -> List.Mem k (causalKeys q2 keys) := by
  -- TODO
  -- Hint: ex937 then transitivity of <=, then ex938.
  sorry

-- 940: causalKeys on empty list is empty.
theorem ex940 (q : Nat) :
    causalKeys q ([] : List Nat) = [] := by
  -- TODO
  -- Hint: unfold causalKeys.
  sorry

-- 941: cons expansion for causalKeys.
theorem ex941 (q k : Nat) (keys : List Nat) :
    causalKeys q (k :: keys)
      =
    (if k <= q then k :: causalKeys q keys else causalKeys q keys) := by
  -- TODO
  -- Hint: unfold causalKeys; split on (k <= q).
  sorry

--------------------------------------------------------------------------------
-- 942-945: Causal head rewrites
--------------------------------------------------------------------------------

-- 942: at row q, causal head equals ordinary head restricted to causalKeys q.
theorem ex942 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) (q : Nat) :
    forall c, wHead (causalKeys q keys) QK KV q c = wCausalHead keys QK KV q c := by
  -- TODO
  -- Hint: both sides encode the same witness condition at row q.
  sorry

-- 943: causal head over empty keys is zero.
theorem ex943 (QK : WRel Nat Nat) (KV : WRel Nat C) :
    wCausalHead ([] : List Nat) QK KV = wZero Nat C := by
  -- TODO
  -- Hint: unfold wCausalHead and use ex918 (or ex866 via wHead).
  sorry

-- 944: causal head is 0/1-valued.
theorem ex944 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat C) :
    wBool (wCausalHead keys QK KV) = wCausalHead keys QK KV := by
  -- TODO
  -- Hint: unfold wCausalHead; use ex920.
  sorry

-- 945: graph-left causal head under key coverage collapses to one gate.
theorem ex945 (keys : List Nat) (f : Nat -> Nat) (S : WRel Nat C) :
    (forall a : Nat, List.Mem (f a) keys) ->
      wCausalHead keys (wGraph f) S
        =
      wMask (fun a c => wBool S (f a) c) (fun a _ => f a <= a) := by
  -- TODO
  -- Hint: ex907 removes key-gate, then remaining mask is exactly causality.
  sorry

end TL