import LeanBook.FirstProof.NaturalNumber
import LeanBook.NatCommMonoid.TypeClass

set_option pp.fieldNotation.generalized false in

theorem MyNat.add_zero ( n : MyNat ) : n + 0 = n := by

  change MyNat.add n zero = n

  rewrite [MyNat.add.eq_def]

  apply Eq.trans
  · dsimp

  rfl

theorem MyNat.add_zero2 ( n : MyNat ) : MyNat.add n 0 = n := by
  rfl

theorem MyNat.add_zero3 ( n : MyNat ) : n + MyNat.zero = n := by
  rfl

theorem MyNat.add_zero4 ( n : MyNat ) : MyNat.add 0 n = n := by

  induction n with
  | zero =>

    change MyNat.add 0 0 = 0

    rw [MyNat.add.eq_def]

    rfl

  | succ n ih =>

    rw [MyNat.add.eq_def]

    dsimp

    rw [ih]

theorem MyNat.add_zero5 ( n : MyNat ) : MyNat.zero + n = n := by

  change MyNat.add 0 n = n

  rw [MyNat.add_zero4]

theorem MyNat.add_succ ( m n : MyNat ) : m +  .succ n  = .succ ( m + n ) := by

  change MyNat.add m n.succ = (MyNat.add m n).succ

  rw [MyNat.add.eq_def]

theorem MyNat.add_succ2 ( m n : MyNat ) : .succ m +  n  = .succ ( m + n ) := by

  rw [←MyNat.add_succ]

  change MyNat.add m.succ n = MyNat.add m n.succ

  induction n with
  | zero =>

    rw [MyNat.add.eq_def]

    dsimp

    rw [MyNat.add.eq_def]

    dsimp

    rfl

  | succ n ih =>

    rw [MyNat.add.eq_def]

    dsimp

    rw [ih]

    rfl

theorem MyNat.zero_plus ( n : MyNat ) : MyNat.zero + n = n := by

  induction n with

  | zero =>

    change MyNat.add zero zero = zero

    rw [MyNat.add.eq_def]

  | succ n ih =>

    rw [MyNat.add_succ]

    rw [ih]

theorem MyNat.zero_add ( n : MyNat ) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [MyNat.add_succ]
    rw [ih]
