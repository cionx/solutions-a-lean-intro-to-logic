-- Have: Nothing.
-- Need: G ∧ (H ∨ U) → (G ∧ H) ∨ (G ∧ U).
-- Idea: 1. This is distributivity.
--       2. There is no reason to expect such a morphism in an arbitrary category.
--          But we do always get a function
--            GlobalElements(1, A × (X + Y))  →  GlobalElements(1, (A × X) + (A × Y))
--          as follows: A global element of A × (X + Y) gives a global element a :1 → A
--          in the first coordinate. This element allows us to get
--            X  ≅  1 × X  →  A × X  →  (A × X) + (A × Y)
--          and similarly
--            Y  ≅  1 × Y  →  A × Y  →  (A × X ) + (A × Y) ,
--          which we can then combine into
--            X + Y  →  (A × X) + (A × Y) .
--          We have thus found
--              Hom(1, A × (X + Y)) 
--            ≅ Hom(1, A) × Hom(1, X + Y)
--            → Hom(X + Y, (A × X) + (A × Y)) × Hom(1, X + Y)
--            → Hom(1, (A × X) + (A × Y)) .                    (by composition)

have ⟨g, hu⟩ := h
have h1 (h : H) : G ∧ H := ⟨g, h⟩
have h2 (u : U) : G ∧ U := ⟨g, u⟩
exact or_elim hu (h1 ≫ or_inl) (h2 ≫ or_inr)
