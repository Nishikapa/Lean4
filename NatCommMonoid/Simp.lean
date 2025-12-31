import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass
import LeanBook.NatCommMonoid.Induction

attribute [simp] MyNat.add_zero
attribute [simp] MyNat.zero_add

theorem MyNat.ctor_eq_zero  : MyNat.zero = 0 := by
  rfl

attribute [simp] MyNat.ctor_eq_zero
