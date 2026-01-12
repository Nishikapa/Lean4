
example (P : Prop) : ¬( P ↔ ¬ P) := by

  intro iffp
  -- iffp : P ↔ ¬ P
  -- goal : false

  have hnp : ¬ P := by
    -- goal : ¬ P

    intro hp
    -- hp : P
    -- goal : false
    -- Pを仮定に矛盾を示す必要がある。
    -- ¬ P及びPをhaveで示す。
    -- まずは¬ Pから

    have hnp2 : ¬ P := by
      -- goal : ¬ P

      rw [iffp] at hp
      -- hp : Pを¬ Pに置き換えた

      exact hp

    -- 次にPを示す


    contradiction

  have hp : P := by
    -- goal : P

    rw [ ← iffp] at hnp
    -- hnp : ¬ PをPに置き換えた

    exact hnp

  contradiction
