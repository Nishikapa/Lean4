import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass
import LeanBook.NatCommMonoid.Induction
import LeanBook.NatCommMonoid.Simp

theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    rw [MyNat.add_succ]
    rw [MyNat.add_succ2]
    simp [ih]

theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
 induction n with
  | zero =>
    rw [MyNat.add_zero3]
    rw [MyNat.add_zero3]
  | succ n ih =>
    rw [MyNat.add_succ]
    rw [MyNat.add_succ]
    rw [MyNat.add_succ]
    rw [ih]

instance : Std.Associative ( α := MyNat ) (· + ·) where
  assoc := MyNat.add_assoc

instance : Std.Commutative ( α := MyNat ) (· + ·) where
  comm := MyNat.add_comm
