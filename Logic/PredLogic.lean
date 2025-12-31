

def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  intro x
  dsimp [P]
