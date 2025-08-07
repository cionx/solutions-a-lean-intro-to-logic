-- Have : A → (A → ⊥)  i.e.  A → A → ⊥
-- Need: A → ⊥
-- Idea: P → Q → R corrensponds to P ∧ Q → R, so
--       A → A → ⊥ corresponds to A ∧ A → ⊥,
--       which can be precomposed with the diagonal A → A ∧ A.

have adjunct {P Q R} (pqr : P → Q → R) : P ∧ Q → R := λ ⟨p, q⟩ ↦ pqr p q
have diag {P} (p : P): P ∧ P := ⟨p, p⟩

exact diag ≫ adjunct h
