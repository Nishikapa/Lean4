
import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass


example (n : Nat) : n + 0 = n := by
  rfl

#reduce fun (n : Nat) => n + 0

#reduce fun (n : Nat) => 0 + n
