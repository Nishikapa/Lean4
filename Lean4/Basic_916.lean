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
  -- TODO
  -- Hint: unfold wHead and apply ex876.
  sorry

-- 917: right OR distribution for head.
theorem ex917 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    wHead keys R (wOr S S')
      =
    wOr (wHead keys R S) (wHead keys R S') := by
  -- TODO
  -- Hint: unfold wHead and apply ex877.
  sorry

-- 918: zero on the left gives zero.
theorem ex918 (keys : List B) (S : WRel B C) :
    wHead keys (wZero A B) S = wZero A C := by
  -- TODO
  -- Hint: unfold wHead and apply ex878.
  sorry

-- 919: zero on the right gives zero.
theorem ex919 (keys : List B) (R : WRel A B) :
    wHead keys R (wZero B C) = wZero A C := by
  -- TODO
  -- Hint: unfold wHead and apply ex879.
  sorry

-- 920: head is already 0/1-valued.
theorem ex920 (keys : List B) (R : WRel A B) (S : WRel B C) :
    wBool (wHead keys R S) = wHead keys R S := by
  -- TODO
  -- Hint: unfold wHead and apply ex880.
  sorry

--------------------------------------------------------------------------------
-- 921-925: Mask laws for wMaskedHead
--------------------------------------------------------------------------------

-- 921: True-mask does nothing.
theorem ex921 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (fun _ _ => True) QK KV
      =
    wHead keys QK KV := by
  -- TODO
  -- Hint: unfold wMaskedHead and use ex516.
  sorry

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
