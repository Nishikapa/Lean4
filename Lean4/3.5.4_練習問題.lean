

theorem double_negation_of_contra_equiv ( P: Prop )
 (contra_equiv: ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P) ):
  ¬ ¬ P → P := by

  rw [← contra_equiv P (¬ ¬ P)]

  intro not_p
  intro not_not_p

  contradiction
