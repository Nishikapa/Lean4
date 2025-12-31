
inductive ListTest (α : Type) : Type where
  | nil : ListTest α
  | cons : α → ListTest α → ListTest α


inductive VectTest (α : Type) : Nat → Type where
  | vnil : VectTest α 0
  | vcons : α → VectTest α n → VectTest α (n + 1)

example : List ((α : Type) × α) := [ ⟨Nat, 42⟩, ⟨Bool, false⟩ ]

example : {α:Type} → {n:Nat} → (a: α) → (v :VectTest α n) → VectTest α (n + 1) := by

  intro t

  intro n

  intro g

  intro v

  exact VectTest.vcons g v
