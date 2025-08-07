-- Have: P ∧ A → ⊥
-- Need: P → A → ⊥
-- Idea: That’s just adjunction.

have adjunct {P Q R} (pqr : P ∧ Q → R) : P → Q → R := λ p q ↦ pqr ⟨p, q⟩

exact adjunct h
