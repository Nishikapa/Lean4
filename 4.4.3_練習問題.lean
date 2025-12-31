import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass
import LeanBook.NatCommMonoid.Induction
import LeanBook.NatCommMonoid.AcRfl

example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl
