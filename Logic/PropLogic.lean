#eval True → True
#eval True → False

#eval true → true

example (P Q :Prop) ( h : P ↔ Q ) : P = Q := by

  apply propext

  constructor

  intro p

  rw [←h]

  exact p

  intro q

  rw [h]

  exact q


example (P Q :Prop) ( hp : P ) ( hq : Q ) : P ∧ Q := by
  constructor
  exact hp
  exact hq

example (P Q :Prop) ( h : P ∨ Q ) :  Q ∨ P := by
  cases h with
  | inl p =>
    right
    exact p
  | inr q =>
    left
    exact q

example (P Q :Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro hpq
  intro hnq
  intro hp
  have hq : Q := hpq hp
  apply hnq
  apply hq

example (P :Prop) : P →  ¬¬ P := by
  intro hp
  intro hnp
  apply hnp
  exact hp
