inductive MyNat where
  | zero
  | succ (n : MyNat)

def MyNat.one := MyNat.succ MyNat.zero
def MyNat.two := MyNat.succ MyNat.one

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero   => m
  | MyNat.succ n => MyNat.succ (MyNat.add m n)

example : MyNat.add MyNat.one MyNat.two = MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero)) := by
  rfl
