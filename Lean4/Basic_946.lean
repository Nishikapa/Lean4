--------------------------------------------------------------------------------
-- Basic_946.lean
-- Exercise set 946-960 (fast-track 14)
-- Theme: residual blocks, WSpec-style obligations, and non-OR-vs-add behavior.
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
-- 946-950: Basic block algebra
--------------------------------------------------------------------------------

-- 946: wSkip is commutative.
theorem ex946 (X Y : WRel A C) :
    wSkip X Y = wSkip Y X := by
  -- TODO
  -- Hint: unfold wSkip and use ex872.
  sorry

-- 947: wSkip is associative.
theorem ex947 (X Y Z : WRel A C) :
    wSkip (wSkip X Y) Z = wSkip X (wSkip Y Z) := by
  -- TODO
  -- Hint: unfold wSkip and use ex873.
  sorry

-- 948: idempotence of wSkip.
theorem ex948 (X : WRel A C) :
    wSkip X X = wBool X := by
  -- TODO
  -- Hint: unfold wSkip and use ex874.
  sorry

-- 949: if head branch is zero, block output is bool(skip).
theorem ex949 (keys : List B) (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    wHead keys QK KV = wZero A C ->
      wAttnBlock keys QK KV Skip = wBool Skip := by
  -- TODO
  -- Hint: unfold wAttnBlock/wSkip and rewrite.
  sorry

-- 950: zero-skip block is exactly the head.
theorem ex950 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wAttnBlock keys QK KV (wZero A C) = wHead keys QK KV := by
  -- TODO
  -- Hint: unfold wAttnBlock/wSkip; use ex875 and ex920.
  sorry

--------------------------------------------------------------------------------
-- 951-955: WSpec and monotonicity viewpoints
--------------------------------------------------------------------------------

-- 951: if both branches satisfy T, then skip-merge also satisfies T.
theorem ex951 (X Y : WRel A C) (T : Rel A C) :
    WSpec X T -> WSpec Y T -> WSpec (wSkip X Y) T := by
  -- TODO
  -- Hint: unfold WSpec/wSkip/wOr pointwise.
  sorry

-- 952: if skip-merge satisfies T, then left branch satisfies T.
theorem ex952 (X Y : WRel A C) (T : Rel A C) :
    WSpec (wSkip X Y) T -> WSpec X T := by
  -- TODO
  -- Hint: left-positive implies skip-positive.
  sorry

-- 953: block is monotone in Skip.
theorem ex953 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip Skip' : WRel A C) :
    WLe Skip Skip' ->
      WLe (wAttnBlock keys QK KV Skip)
          (wAttnBlock keys QK KV Skip') := by
  -- TODO
  -- Hint: monotonicity of wSkip in first argument.
  sorry

-- 954: block is monotone in QK.
theorem ex954 (keys : List B)
    (QK QK' : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    WLe QK QK' ->
      WLe (wAttnBlock keys QK KV Skip)
          (wAttnBlock keys QK' KV Skip) := by
  -- TODO
  -- Hint: head monotonicity in left input, then lift via wSkip.
  sorry

-- 955: masked block is below unmasked block.
theorem ex955 (keys : List B) (M : Rel A B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    WLe (wMaskedAttnBlock keys M QK KV Skip)
        (wAttnBlock keys QK KV Skip) := by
  -- TODO
  -- Hint: ex932/ex903 style on head branch, then wSkip monotonicity.
  sorry

--------------------------------------------------------------------------------
-- 956-960: Counterexample + MHA block consequences
--------------------------------------------------------------------------------

-- 956: wSkip is not the same as pointwise add in general.
theorem ex956 :
    exists (R S : WRel Nat Nat) (a b : Nat),
      wSkip R S a b = 1 /\
      wAdd R S a b = 2 := by
  -- TODO
  -- Hint: choose R = S = maskW True on one point.
  sorry

-- 957: True-mask block equals unmasked block.
theorem ex957 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    wMaskedAttnBlock keys (fun _ _ => True) QK KV Skip
      =
    wAttnBlock keys QK KV Skip := by
  -- TODO
  -- Hint: unfold wMaskedAttnBlock and use ex921.
  sorry

-- 958: False-mask block drops to bool(skip).
theorem ex958 (keys : List B)
    (QK : WRel A B) (KV : WRel B C) (Skip : WRel A C) :
    wMaskedAttnBlock keys (fun _ _ => False) QK KV Skip
      =
    wBool Skip := by
  -- TODO
  -- Hint: unfold, then use ex922 and ex949 for wSkip.
  sorry

-- 959: append decomposition for MHA block.
theorem ex959 (heads1 heads2 : List H) (F : H -> WRel A C) (Skip : WRel A C) :
    wMHABlock (heads1 ++ heads2) F Skip
      =
    wSkip Skip (wOr (wMHA heads1 F) (wMHA heads2 F)) := by
  -- TODO
  -- Hint: unfold wMHABlock/wSkip and use ex911.
  sorry

-- 960: any selected head is below MHA block output.
theorem ex960 (heads : List H) (F : H -> WRel A C) (Skip : WRel A C) (h : H) :
    List.Mem h heads ->
      WLe (wBool (F h)) (wMHABlock heads F Skip) := by
  -- TODO
  -- Hint: ex912 gives <= wMHA; then lift through wSkip.
  sorry

end TL