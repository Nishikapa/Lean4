--------------------------------------------------------------------------------
-- Basic_961.lean
-- Exercise set 961-975 (fast-track 15)
-- Theme: self-attention style blocks and stack-level rewrites.
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
-- 0) New helpers: self-head / self-block / 2-layer self stack
--------------------------------------------------------------------------------

noncomputable def wSelfHead (keys : List X) (QK KV : WRel X X) : WRel X X :=
  wHead keys QK KV

noncomputable def wSelfBlock (keys : List X) (QK KV Skip : WRel X X) : WRel X X :=
  wAttnBlock keys QK KV Skip

noncomputable def wSelfStack2 (keys1 keys2 : List X)
    (QK1 KV1 QK2 KV2 Skip : WRel X X) : WRel X X :=
  wSelfBlock keys2 QK2 KV2 (wSelfBlock keys1 QK1 KV1 Skip)

noncomputable def wSelfMHABlock (heads : List H) (F : H -> WRel X X) (Skip : WRel X X) : WRel X X :=
  wMHABlock heads F Skip

--------------------------------------------------------------------------------
-- 961-965: Core self-head/self-block identities
--------------------------------------------------------------------------------

-- 961: self-head is 0/1-valued.
theorem ex961 (keys : List X) (QK KV : WRel X X) :
    wBool (wSelfHead keys QK KV) = wSelfHead keys QK KV := by
  -- TODO
  -- Hint: unfold wSelfHead; use ex920.
  sorry

-- 962: self-block with zero skip equals self-head.
theorem ex962 (keys : List X) (QK KV : WRel X X) :
    wSelfBlock keys QK KV (wZero X X) = wSelfHead keys QK KV := by
  -- TODO
  -- Hint: unfold wSelfBlock/wSelfHead; use ex950.
  sorry

-- 963: self-block with zero value-side gives bool(skip).
theorem ex963 (keys : List X) (QK Skip : WRel X X) :
    wSelfBlock keys QK (wZero X X) Skip = wBool Skip := by
  -- TODO
  -- Hint: unfold wSelfBlock/wAttnBlock/wSkip; use ex919 and ex949.
  sorry

-- 964: if both value-sides are zero, 2-layer stack collapses to bool(skip).
theorem ex964 (keys1 keys2 : List X)
    (QK1 QK2 Skip : WRel X X) :
    wSelfStack2 keys1 keys2 QK1 (wZero X X) QK2 (wZero X X) Skip = wBool Skip := by
  -- TODO
  -- Hint: use ex963 twice.
  sorry

-- 965: zero-skip stack equals second block on first head output.
theorem ex965 (keys1 keys2 : List X)
    (QK1 KV1 QK2 KV2 : WRel X X) :
    wSelfStack2 keys1 keys2 QK1 KV1 QK2 KV2 (wZero X X)
      =
    wSelfBlock keys2 QK2 KV2 (wSelfHead keys1 QK1 KV1) := by
  -- TODO
  -- Hint: unfold wSelfStack2; rewrite inner block by ex962.
  sorry

--------------------------------------------------------------------------------
-- 966-970: Distribution / monotonicity rewrites in self setting
--------------------------------------------------------------------------------

-- 966: self-head left OR distribution.
theorem ex966 (keys : List X) (R R' S : WRel X X) :
    wSelfHead keys (wOr R R') S
      =
    wOr (wSelfHead keys R S) (wSelfHead keys R' S) := by
  -- TODO
  -- Hint: unfold wSelfHead; use ex916.
  sorry

-- 967: self-head right OR distribution.
theorem ex967 (keys : List X) (R S S' : WRel X X) :
    wSelfHead keys R (wOr S S')
      =
    wOr (wSelfHead keys R S) (wSelfHead keys R S') := by
  -- TODO
  -- Hint: unfold wSelfHead; use ex917.
  sorry

-- 968: self-block monotone in skip input.
theorem ex968 (keys : List X)
    (QK KV Skip Skip' : WRel X X) :
    WLe Skip Skip' ->
      WLe (wSelfBlock keys QK KV Skip)
          (wSelfBlock keys QK KV Skip') := by
  -- TODO
  -- Hint: unfold wSelfBlock; use ex954.
  sorry

-- 969: self-block monotone in QK input.
theorem ex969 (keys : List X)
    (QK QK' KV Skip : WRel X X) :
    WLe QK QK' ->
      WLe (wSelfBlock keys QK KV Skip)
          (wSelfBlock keys QK' KV Skip) := by
  -- TODO
  -- Hint: unfold wSelfBlock; use ex955.
  sorry

-- 970: selected head is below self-MHA block.
theorem ex970 (heads : List H) (F : H -> WRel X X) (Skip : WRel X X) (h : H) :
    List.Mem h heads ->
      WLe (wBool (F h)) (wSelfMHABlock heads F Skip) := by
  -- TODO
  -- Hint: unfold wSelfMHABlock; use ex957.
  sorry

--------------------------------------------------------------------------------
-- 971-975: Graph collapse and final stack-level exercises
--------------------------------------------------------------------------------

-- 971: self-MHA block over appended head-list.
theorem ex971 (heads1 heads2 : List H) (F : H -> WRel X X) (Skip : WRel X X) :
    wSelfMHABlock (heads1 ++ heads2) F Skip
      =
    wSkip Skip (wOr (wMHA heads1 F) (wMHA heads2 F)) := by
  -- TODO
  -- Hint: unfold wSelfMHABlock; use ex956.
  sorry

-- 972: zero-skip self-MHA block equals self-MHA.
theorem ex972 (heads : List H) (F : H -> WRel X X) :
    wSelfMHABlock heads F (wZero X X) = wMHA heads F := by
  -- TODO
  -- Hint: unfold wSelfMHABlock; use ex958.
  sorry

-- 973: graph-self head collapse under key coverage.
theorem ex973 (keys : List X) (f g : X -> X) :
    (forall x : X, List.Mem (f x) keys) ->
      wSelfHead keys (wGraph f) (wGraph g)
        =
      wGraph (fun x => g (f x)) := by
  -- TODO
  -- Hint: unfold wSelfHead; use ex909.
  sorry

-- 974: graph-self block collapse under key coverage.
theorem ex974 (keys : List X) (f g : X -> X) (Skip : WRel X X) :
    (forall x : X, List.Mem (f x) keys) ->
      wSelfBlock keys (wGraph f) (wGraph g) Skip
        =
      wSkip Skip (wGraph (fun x => g (f x))) := by
  -- TODO
  -- Hint: unfold wSelfBlock/wSkip and use ex973.
  sorry

-- 975: two-hop graph collapse in self setting (specialization of ex930).
theorem ex975 (keys1 keys2 : List X) (f g h : X -> X) :
    (forall x : X, List.Mem (f x) keys1) ->
    (forall x : X, List.Mem (g (f x)) keys2) ->
      wTwoHop keys1 keys2 (wGraph f) (wGraph g) (wGraph h)
        =
      wGraph (fun x => h (g (f x))) := by
  -- TODO
  -- Hint: apply ex930.
  sorry

end TL