-- Have: Nothing.
-- Need: G ∨ (H ∧ U) → (G ∨ H) ∧ (G ∨ U).
-- Idea: 1. This is distributivity.
--       2. There is a canonical morphism coming from universal properties:
--            G → G ∨ H   and   G → G ∨ U   become   G → (G ∨ H) ∧ (G ∨ U),
--          and
--            H → G ∨ H   and   U → G ∨ U   become   H ∧ U → (G ∨ H) ∧ (G ∨ U),
--          Then we combine both results via the universal property of the coproduct.

have h1 (g : G) : (G ∨ H) ∧ (G ∨ U) := ⟨or_inl g, or_inl g⟩
have h2 (x : H ∧ U) : (G ∨ H) ∧ (G ∨ U) := ⟨or_inr x.left, or_inr x.right⟩
exact or_elim h h1 h2
