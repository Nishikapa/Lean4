import LeanBook.FirstProof.NaturalNumber

def MyNat.ofNat ( n: Nat ) : MyNat :=
  match n with
  | 0   => MyNat.zero
  | n + 1 => MyNat.succ ( MyNat.ofNat n )

@[default_instance]
instance (n: Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0
#check 1

instance : Add MyNat where
  add := MyNat.add

#check 1 + 2

#eval 0 + 0

#eval 1 + 2

def MyNat.toNat ( n : MyNat) : Nat :=
  match n with
  | MyNat.zero   => 0
  | MyNat.succ k => Nat.succ ( MyNat.toNat k )

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval (1 + 2 : MyNat)
