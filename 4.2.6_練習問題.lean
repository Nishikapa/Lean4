
import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass
import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 1 + n = .succ n := by

  induction n with
  | zero =>

    rfl

  | succ n ih =>

    rw [MyNat.add_succ]

    rw [←ih]
