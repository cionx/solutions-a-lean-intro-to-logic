-- Have: K → P.
-- Need: K ∨ I → I ∨ P.
-- Idea: By the universal property of the coproduct we need separate
--   K → I ∨ P   and   I → I ∨ P .
-- We can use
--   K → P →₂ I ∨ P   and   I →₁ I ∨ P .

exact λ ki ↦ or_elim ki (h ≫ or_inr) or_inl
