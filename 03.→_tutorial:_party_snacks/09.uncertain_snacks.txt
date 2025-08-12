-- Have: Nothing
-- Need: R → (S → R) ∧ (¬S → R).
-- Idea: Every r : R gives a constant T → R for every T,
--       and thus some (T₁ → R) ∧ ⋯ ∧ (Tₙ → R) for all Tᵢ.

have const {R T} (r : R) (_ : T) := r
exact λ r ↦ ⟨const r, const r⟩
