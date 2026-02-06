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
  -- TODO
  -- Hint: unfold wAnd, then use ex668 (wMul commutative).
  sorry

-- 888: wAnd is associative.
theorem ex888 (R S T : WRel A B) :
    wAnd (wAnd R S) T = wAnd R (wAnd S T) := by
  -- TODO
  -- Hint:
  --   * compare supports via ex886
  --   * use relMul associativity pointwise
  --   * finish with maskW / wBool extensionality
  sorry

-- 889: idempotence (AND with itself collapses to bool).
theorem ex889 (R : WRel A B) :
    wAnd R R = wBool R := by
  -- TODO
  -- Hint: unfold wAnd and use positivity of x*x.
  sorry

-- 890: absorption with OR.
theorem ex890 (R S : WRel A B) :
    wAnd R (wOr R S) = wBool R := by
  -- TODO
  -- Hint:
  --   * support side is R /\ (R \/ S)
  --   * use ex871 for wOr support
  --   * conclude by extensionality on 0/1 relations
  sorry

--------------------------------------------------------------------------------
-- 891-895: ReachComp with wAnd (inequalities + singleton equality)
--------------------------------------------------------------------------------

-- 891: AND on the left input can only decrease reach.
theorem ex891 (keys : List B) (R R' : WRel A B) (S : WRel B C) :
    WLe (wReachComp keys (wAnd R R') S)
        (wReachComp keys R S) := by
  -- TODO
  -- Hint: unfold WLe; witness for left is also a witness for right.
  sorry

-- 892: AND on the right input can only decrease reach.
theorem ex892 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    WLe (wReachComp keys R (wAnd S S'))
        (wReachComp keys R S) := by
  -- TODO
  -- Hint: same witness argument as ex891.
  sorry

-- 893: left-AND reach implies AND of the two reaches.
theorem ex893 (keys : List B) (R R' : WRel A B) (S : WRel B C) :
    WLe (wReachComp keys (wAnd R R') S)
        (wAnd (wReachComp keys R S) (wReachComp keys R' S)) := by
  -- TODO
  -- Hint: combine ex891 with the symmetric statement for R'.
  sorry

-- 894: right-AND reach implies AND of the two reaches.
theorem ex894 (keys : List B) (R : WRel A B) (S S' : WRel B C) :
    WLe (wReachComp keys R (wAnd S S'))
        (wAnd (wReachComp keys R S) (wReachComp keys R S')) := by
  -- TODO
  -- Hint: same shape as ex893.
  sorry

-- 895: singleton keys fixes the witness, so right-AND distributes exactly.
theorem ex895 (b : B) (R : WRel A B) (S S' : WRel B C) :
    wReachComp [b] R (wAnd S S')
      =
    wAnd (wReachComp [b] R S) (wReachComp [b] R S') := by
  -- TODO
  -- Hint: use ex867 to rewrite both sides to mask forms with the same b.
  sorry

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
