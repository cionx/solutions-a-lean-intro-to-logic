-- For (P ∧ Q ↔ R ∧ Q) → Q → (P ↔ R)

have and_elim_imp {P Q R} (pqr : P ∧ Q → R ∧ Q) (q : Q) : P → R
· exact (⟨·, q⟩) ≫ pqr ≫ and_left

have and_elim_iff {P Q R} (pqr : P ∧ Q ↔ R ∧ Q) (q : Q) : P ↔ R
· exact ⟨and_elim_imp pqr.mp q, and_elim_imp pqr.mpr q⟩

-- For (Q → (P ↔ R)) → (P ∧ Q ↔ R ∧ Q)

have and_intro_imp {P Q R} (pqr : P → Q → R) : Q ∧ P → R ∧ P
· exact λ ⟨q, p⟩ ↦ ⟨pqr p q, p⟩

have and_intro_iff {P Q R} (pqr : P → (Q ↔ R)) : Q ∧ P ↔ R ∧ P
· exact ⟨and_intro_imp (pqr ≫ iff_mp), and_intro_imp (pqr ≫ iff_mpr)⟩

-- Combining both directions

exact ⟨and_elim_iff, and_intro_iff⟩
