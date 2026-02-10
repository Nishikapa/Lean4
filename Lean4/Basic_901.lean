--------------------------------------------------------------------------------
-- Basic_901.lean
-- Exercise set 901-915 (fast-track 11)
-- Theme: masked hard-attention heads and multi-head aggregation (0/1 semantics).
--
-- * No Mathlib import.
-- * Exercises only (TODO / sorry).
-- * Reuse prior files through Basic_886.
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_886

namespace TL

open Classical
attribute [local instance] Classical.propDecidable

variable {A B C D H : Type}

--------------------------------------------------------------------------------
-- 0) New helpers: head / masked-head / multi-head aggregate
--------------------------------------------------------------------------------

noncomputable def wHead (keys : List B) (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  wReachComp keys QK KV

noncomputable def wMaskedHead (keys : List B) (M : Rel A B)
    (QK : WRel A B) (KV : WRel B C) : WRel A C :=
  wHead keys (wMask QK M) KV

noncomputable def wMHA (heads : List H) (F : H -> WRel A C) : WRel A C :=
  wsumW heads F

--------------------------------------------------------------------------------
-- 901-905: Head + masking basics
--------------------------------------------------------------------------------

-- 901: support of head is relCompList on supports.
theorem ex901 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wHead keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by
  -- TODO
  -- Hint: unfold wHead, then ex818.
  sorry

-- 902: support of masked-head (left mask) is relMul on left support.
theorem ex902 (keys : List B) (M : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wMaskedHead keys M QK KV)
      =
    relCompList keys (relMul (wSupp QK) M) (wSupp KV) := by
  -- TODO
  -- Hint: ex901 + ex614.
  sorry

-- 903: masking the left side can only reduce support.
theorem ex903 (keys : List B) (M : Rel A B) (QK : WRel A B) (KV : WRel B C) :
    wSupp (wMaskedHead keys M QK KV) ⊆ wSupp (wHead keys QK KV) := by
  -- TODO
  -- Hint:
  --   * ex902/ex901
  --   * pointwise: (wSupp QK a b ∧ M a b) -> wSupp QK a b
  sorry

-- 904: key-membership mask on left is redundant for head.
theorem ex904 (keys : List B) (QK : WRel A B) (KV : WRel B C) :
    wMaskedHead keys (relInKeys (α:=A) keys) QK KV
      =
    wHead keys QK KV := by
  -- TODO
  -- Hint:
  --   * ∈ relCompList, witness b already satisfies b ∈ keys
  --   * so extra left mask by relInKeys is redundant
  sorry

-- 905: singleton head formula.
theorem ex905 (b : B) (R : WRel A B) (S : WRel B C) :
    wHead [b] R S
      =
    maskW (fun a c => wSupp R a b ∧ wSupp S b c) := by
  -- TODO
  -- Hint: unfold wHead; use ex867.
  sorry

--------------------------------------------------------------------------------
-- 906-910: Graph-style head formulas
--------------------------------------------------------------------------------

-- 906: graph on the left gives pullback-with-key-gate mask form.
theorem ex906 (keys : List B) (f : A -> B) (S : WRel B C) :
    wHead keys (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys) := by
  -- TODO
  -- Hint: unfold wHead; use ex848.
  sorry

-- 907: if every f a is ∈ keys, graph-left head drops the gate.
theorem ex907 (keys : List B) (f : A -> B) (S : WRel B C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) S
        =
      (fun a c => wBool S (f a) c) := by
  -- TODO
  -- Hint: unfold wHead; use ex850.
  sorry

-- 908: graph-graph head as one mask.
theorem ex908 (keys : List B) (f : A -> B) (g : B -> C) :
    wHead keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  -- Hint: unfold wHead; use ex849.
  sorry

-- 909: graph-graph head under key coverage becomes composed graph.
theorem ex909 (keys : List B) (f : A -> B) (g : B -> C) :
    (∀ a : A, f a ∈ keys) ->
      wHead keys (wGraph f) (wGraph g)
        =
      wGraph (fun a => g (f a)) := by
  -- TODO
  -- Hint: unfold wHead; use ex836 (or ex870).
  sorry

-- 910: singleton multi-head aggregate is just bool of that head.
theorem ex910 (h0 : H) (F : H -> WRel A C) :
    wMHA [h0] F = wBool (F h0) := by
  -- TODO
  -- Hint:
  --   * unfold wMHA / wsumW on singleton
  --   * or use ex842 + ex841
  sorry

--------------------------------------------------------------------------------
-- 911-915: Multi-head algebra and interaction with head
--------------------------------------------------------------------------------

-- 911: append of head list becomes OR (wOr).
theorem ex911 (heads1 heads2 : List H) (F : H -> WRel A C) :
    wMHA (heads1 ++ heads2) F
      =
    wOr (wMHA heads1 F) (wMHA heads2 F) := by
  -- TODO
  -- Hint: unfold wMHA; ex852 + definition of wOr.
  sorry

-- 912: each selected head is below the aggregate.
theorem ex912 (heads : List H) (F : H -> WRel A C) (h : H) :
    h ∈ heads ->
      WLe (wBool (F h)) (wMHA heads F) := by
  -- TODO
  -- Hint: unfold wMHA; ex857.
  sorry

-- 913: monotonicity ∈ head-list inclusion.
theorem ex913 (heads heads' : List H) (F : H -> WRel A C) :
    (∀ h, h ∈ heads -> h ∈ heads') ->
      WLe (wMHA heads F) (wMHA heads' F) := by
  -- TODO
  -- Hint: unfold wMHA; ex858.
  sorry

-- 914: head distributes over multi-head aggregate on the right.
theorem ex914 (keys : List B) (R : WRel A B) (heads : List H) (F : H -> WRel B C) :
    wHead keys R (wMHA heads F)
      =
    wMHA heads (fun h => wHead keys R (F h)) := by
  -- TODO
  -- Hint: unfold wHead/wMHA; ex863.
  sorry

-- 915: head distributes over multi-head aggregate on the left.
theorem ex915 (keys : List B) (heads : List H) (F : H -> WRel A B) (S : WRel B C) :
    wHead keys (wMHA heads F) S
      =
    wMHA heads (fun h => wHead keys (F h) S) := by
  -- TODO
  -- Hint: unfold wHead/wMHA; ex864.
  sorry

end TL

