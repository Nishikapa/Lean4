--------------------------------------------------------------------------------
-- Basic_946.lean
-- Exercise set 946-960 (fast-track 14)
-- Theme: residual/skip blocks over hard-attention heads.
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_931.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_931

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {A B C H : Type}

--------------------------------------------------------------------------------
-- 0) New helpers: skip merge / attention blocks
--------------------------------------------------------------------------------

noncomputable def wSkip (X Y : WRel A C) : WRel A C :=
  wOr X Y

noncomputable def wAttnBlock (keys : List B) (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) : WRel A C :=
  wSkip Skip (wHead keys QK KV)

noncomputable def wMaskedAttnBlock (keys : List B) (M : Rel A B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) : WRel A C :=
  wSkip Skip (wMaskedHead keys M QK KV)

noncomputable def wMHABlock (heads : List H) (F : H -> WRel A C) (Skip : WRel A C) : WRel A C :=
  wSkip Skip (wMHA heads F)

--------------------------------------------------------------------------------
-- 946-950: Algebra of wSkip and base block rewrites
--------------------------------------------------------------------------------

-- 946: wSkip is commutative.
theorem ex946 (X Y : WRel A C) :
    wSkip X Y = wSkip Y X := by
  -- TODO
  -- Hint: unfold wSkip; use ex872.
  sorry

-- 947: wSkip is associative.
theorem ex947 (X Y Z : WRel A C) :
    wSkip (wSkip X Y) Z = wSkip X (wSkip Y Z) := by
  -- TODO
  -- Hint: unfold wSkip; use ex873.
  sorry

-- 948: idempotence of wSkip.
theorem ex948 (X : WRel A C) :
    wSkip X X = wBool X := by
  -- TODO
  -- Hint: unfold wSkip; use ex874.
  sorry

-- 949: skipping with zero on the right gives bool(X).
theorem ex949 (X : WRel A C) :
    wSkip X (wZero A C) = wBool X := by
  -- TODO
  -- Hint: unfold wSkip; use ex875.
  sorry

-- 950: zero-skip block is exactly the head.
theorem ex950 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wAttnBlock keys QK KV (wZero A C) = wHead keys QK KV := by
  -- TODO
  -- Hint: unfold wAttnBlock/wSkip; use ex949 and ex920.
  sorry

--------------------------------------------------------------------------------
-- 951-955: Masked block laws
--------------------------------------------------------------------------------

-- 951: masked block is below unmasked block.
theorem ex951 (keys : List B) (M : Rel A B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    WLe (wMaskedAttnBlock keys M QK KV Skip)
        (wAttnBlock keys QK KV Skip) := by
  -- TODO
  -- Hint: use ex934 and monotonicity of wSkip on the right argument.
  sorry

-- 952: True mask gives the unmasked block.
theorem ex952 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    wMaskedAttnBlock keys (fun _ _ => True) QK KV Skip
      =
    wAttnBlock keys QK KV Skip := by
  -- TODO
  -- Hint: unfold wMaskedAttnBlock; use ex921.
  sorry

-- 953: False mask removes the head contribution.
theorem ex953 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    wMaskedAttnBlock keys (fun _ _ => False) QK KV Skip
      =
    wBool Skip := by
  -- TODO
  -- Hint: unfold wMaskedAttnBlock/wAttnBlock/wSkip; use ex922 and ex949.
  sorry

-- 954: block monotone in skip input.
theorem ex954 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip Skip' : WRel A C) :
    WLe Skip Skip' ->
      WLe (wAttnBlock keys QK KV Skip)
          (wAttnBlock keys QK KV Skip') := by
  -- TODO
  -- Hint: unfold wAttnBlock/wSkip; OR is monotone in each argument.
  sorry

-- 955: block monotone in QK input.
theorem ex955 (keys : List B)
    (QK QK' : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    WLe QK QK' ->
      WLe (wAttnBlock keys QK KV Skip)
          (wAttnBlock keys QK' KV Skip) := by
  -- TODO
  -- Hint: monotonicity of head in left input, then monotonicity of wSkip.
  sorry

--------------------------------------------------------------------------------
-- 956-960: MHA blocks and graph specialization
--------------------------------------------------------------------------------

-- 956: MHA block on appended head-list.
theorem ex956 (heads1 heads2 : List H) (F : H -> WRel A C) (Skip : WRel A C) :
    wMHABlock (heads1 ++ heads2) F Skip
      =
    wSkip Skip (wOr (wMHA heads1 F) (wMHA heads2 F)) := by
  -- TODO
  -- Hint: unfold wMHABlock/wSkip; use ex911.
  sorry

-- 957: selected head is below MHA block output.
theorem ex957 (heads : List H) (F : H -> WRel A C) (Skip : WRel A C) (h : H) :
    List.Mem h heads ->
      WLe (wBool (F h)) (wMHABlock heads F Skip) := by
  -- TODO
  -- Hint: ex912 then monotonicity into wSkip.
  sorry

-- 958: zero-skip MHA block is exactly MHA.
theorem ex958 (heads : List H) (F : H -> WRel A C) :
    wMHABlock heads F (wZero A C) = wMHA heads F := by
  -- TODO
  -- Hint: unfold wMHABlock/wSkip; use ex949 and ex856.
  sorry

-- 959: MHA block is 0/1-valued.
theorem ex959 (heads : List H) (F : H -> WRel A C) (Skip : WRel A C) :
    wBool (wMHABlock heads F Skip) = wMHABlock heads F Skip := by
  -- TODO
  -- Hint: wSkip is wOr; outputs are 0/1 after wBool.
  sorry

-- 960: graph-left block under key coverage.
theorem ex960 (keys : List B) (f : A -> B) (S : WRel B C) (Skip : WRel A C) :
    (forall a : A, List.Mem (f a) keys) ->
      wAttnBlock keys (wGraph f) S Skip
        =
      wSkip Skip (fun a c => wBool S (f a) c) := by
  -- TODO
  -- Hint: unfold wAttnBlock/wSkip; use ex907.
  sorry

end TL