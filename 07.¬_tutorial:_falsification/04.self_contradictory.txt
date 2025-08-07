-- Have: L ∧ (L → ⊥), so in other
-- Need: ⊥
-- Idea: Just a swapped version of application/modus ponens.

-- The following two have been proven in earlier levels already.
have and_swap {P Q} (pq : P ∧ Q) : Q ∧ P := ⟨pq.right, pq.left⟩
have adjunct {P Q R} (pqr : P → Q → R) : P ∧ Q → R := λ ⟨p, q⟩ ↦ pqr p q

exact and_swap ≫ adjunct modus_ponens
