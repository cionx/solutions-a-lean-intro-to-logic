-- Have: S → C and S → D.
-- Need: S → C ∧ D.
-- Idea: Use the universal property of the product.

have ⟨sc, sd⟩ := h
exact λ s ↦ ⟨sc s, sd s⟩
