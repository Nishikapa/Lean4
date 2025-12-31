
example (P Q: Prop) (hp: P) : Q → P :=

  fun hq => hp
