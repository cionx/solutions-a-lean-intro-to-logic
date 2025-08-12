-- Have: B → ⊥ and (B → C) → ⊥
-- Need: ⊥
-- Idea: We can get B → C from composing B → ⊥ with ⊥ → C.

exact (· ≫ false_elim) ≫ h
