
import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass
import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 2 + n = n + 2 := by

  induction n with
  | zero =>

    rw [MyNat.zero_plus]

    rw [MyNat.add_zero3]

  | succ n ih =>

    rw [MyNat.add_succ]

    rw [ih]

    rw [MyNat.add_succ2]
