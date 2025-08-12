-- Have: A and ((A → ⊥) → ⊥) → ⊥
-- Need: ⊥
-- Idea: Say we have A and ((A → B) → B) → B, and we need B.
--       We can get B from ((A → B) → B) → B once we have (A → B) → B.
--       We can get (A → B) → B from A via evaluation.
--       In terms of terms,
--                a   : A
--         gives  e   : (A → B) → B  via evaluation at a
--         gives  h e : B            via applycation of h : ((A → B) → B) → B .
--       The first step, a ↦ e of type A → (A → B) → B, is just modus ponens.

have swap_args {P Q R} (pqr : P → Q → R) : Q → P → R := λ q p ↦ pqr p q

exact (swap_args modus_ponens) ≫ h
