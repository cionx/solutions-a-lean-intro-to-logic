-- Have: S → ⊥
-- Need: S → B
-- Idea: EFQ gives us ⊥ → B, which we can compose with S → ⊥.

exact h ≫ false_elim
