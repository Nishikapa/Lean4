--------------------------------------------------------------------------------
-- Basic_961.lean
-- Exercise set 961-975 (fast-track 15)
-- Theme: self-attention stacks, two-hop collapse, and final mixed goals.
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_946.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_946

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {X H : Type}

--------------------------------------------------------------------------------
-- 0) New helpers in self setting
--------------------------------------------------------------------------------

noncomputable def wSelfHead (keys : List X) (QK KV : WRel X X) : WRel X X :=
  wHead keys QK KV

noncomputable def wSelfBlock (keys : List X) (QK KV Skip : WRel X X) : WRel X X :=
  wAttnBlock keys QK KV Skip

noncomputable def wSelfStack2 (keys1 keys2 : List X)
    (R : WRel X X) (S : WRel X X) (T : WRel X X) : WRel X X :=
  wTwoHop keys1 keys2 R S T

noncomputable def wSelfMHABlock (heads : List H) (F : H -> WRel X X) (Skip : WRel X X) : WRel X X :=
  wMHABlock heads F Skip

--------------------------------------------------------------------------------
-- 961-965: Core identities
--------------------------------------------------------------------------------

-- 961: self-head is 0/1-valued.
theorem ex961 (keys : List X) (QK KV : WRel X X) :
    wBool (wSelfHead keys QK KV) = wSelfHead keys QK KV := by
  -- TODO
  -- Hint: unfold wSelfHead and use ex920.
  sorry

-- 962: self-block with zero skip equals self-head.
theorem ex962 (keys : List X) (QK KV : WRel X X) :
    wSelfBlock keys QK KV (wZero X X) = wSelfHead keys QK KV := by
  -- TODO
  -- Hint: unfold and use ex950.
  sorry

-- 963: self-MHA block with zero skip equals self-MHA.
theorem ex963 (heads : List H) (F : H -> WRel X X) :
    wSelfMHABlock heads F (wZero X X) = wMHA heads F := by
  -- TODO
  -- Hint: unfold and use ex958.
  sorry

-- 964: selected head is below self-MHA block.
theorem ex964 (heads : List H) (F : H -> WRel X X) (Skip : WRel X X) (h : H) :
    List.Mem h heads ->
      WLe (wBool (F h)) (wSelfMHABlock heads F Skip) := by
  -- TODO
  -- Hint: unfold and use ex960.
  sorry

-- 965: self stack reassociation (specialization of two-hop).
theorem ex965 (keys1 keys2 : List X) (R S T : WRel X X) :
    wSelfStack2 keys1 keys2 R S T
      =
    wSelfHead keys1 R (wSelfHead keys2 S T) := by
  -- TODO
  -- Hint: unfold wSelfStack2/wSelfHead and use ex926.
  sorry

--------------------------------------------------------------------------------
-- 966-970: Zero/graph and a non-symmetry challenge
--------------------------------------------------------------------------------

-- 966: self stack with left zero is zero.
theorem ex966 (keys1 keys2 : List X) (S T : WRel X X) :
    wSelfStack2 keys1 keys2 (wZero X X) S T = wZero X X := by
  -- TODO
  -- Hint: unfold and use ex927.
  sorry

-- 967: self stack with middle zero is zero.
theorem ex967 (keys1 keys2 : List X) (R T : WRel X X) :
    wSelfStack2 keys1 keys2 R (wZero X X) T = wZero X X := by
  -- TODO
  -- Hint: unfold and use ex928.
  sorry

-- 968: self stack with right zero is zero.
theorem ex968 (keys1 keys2 : List X) (R S : WRel X X) :
    wSelfStack2 keys1 keys2 R S (wZero X X) = wZero X X := by
  -- TODO
  -- Hint: unfold and use ex929.
  sorry

-- 969: graph self-stack collapse under key coverage.
theorem ex969 (keys1 keys2 : List X) (f g h : X -> X) :
    (forall x : X, List.Mem (f x) keys1) ->
    (forall x : X, List.Mem (g (f x)) keys2) ->
      wSelfStack2 keys1 keys2 (wGraph f) (wGraph g) (wGraph h)
        =
      wGraph (fun x => h (g (f x))) := by
  -- TODO
  -- Hint: unfold and use ex930.
  sorry

-- 970: order swap of keys can change two-hop output (counterexample).
theorem ex970 :
    exists (R S T : WRel Nat Nat),
      wTwoHop [0] [1] R S T != wTwoHop [1] [0] R S T := by
  -- TODO
  -- Hint: make only one key order admit a witness chain.
  sorry

--------------------------------------------------------------------------------
-- 971-975: Final mixed goals (causal + spec + graph)
--------------------------------------------------------------------------------

-- 971: row-wise causal rewrite (reuse ex942).
theorem ex971 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat Nat) (q : Nat) :
    forall c, wHead (causalKeys q keys) QK KV q c = wCausalHead keys QK KV q c := by
  -- TODO
  -- Hint: exact ex942.
  sorry

-- 972: causal head is below ordinary head (Nat specialization).
theorem ex972 (keys : List Nat) (QK : WRel Nat Nat) (KV : WRel Nat Nat) :
    WLe (wCausalHead keys QK KV) (wHead keys QK KV) := by
  -- TODO
  -- Hint: exact ex932.
  sorry

-- 973: if skip and head satisfy T, self-block also satisfies T.
theorem ex973 (keys : List X) (QK KV Skip : WRel X X) (T : Rel X X) :
    WSpec Skip T -> WSpec (wSelfHead keys QK KV) T -> WSpec (wSelfBlock keys QK KV Skip) T := by
  -- TODO
  -- Hint: unfold and use ex951.
  sorry

-- 974: if self-block satisfies T, then skip branch satisfies T.
theorem ex974 (keys : List X) (QK KV Skip : WRel X X) (T : Rel X X) :
    WSpec (wSelfBlock keys QK KV Skip) T -> WSpec Skip T := by
  -- TODO
  -- Hint: unfold and use ex952.
  sorry

-- 975: graph + causal + identity collapse (final style mix).
theorem ex975 (keys : List Nat) (f : Nat -> Nat) :
    (forall a : Nat, List.Mem (f a) keys) ->
    (forall a : Nat, f a <= a) ->
      wCausalHead keys (wGraph f) (wId Nat)
        =
      wGraph f := by
  -- TODO
  -- Hint:
  --   * ex945 with S := wId Nat
  --   * simplify wBool (wId Nat) via ex825 (or definition).
  sorry

end TL