-- Have: C → J.
-- Need: C ∨ R → J ∨ R.
-- Idea: Use functoriality of the coproduct in the first argument. More explicit:
--       By the universal property of the coproduct we need separat
--         C → J ∨ R   and   R → J ∨ R.
--       We can use  C → J →₁ J ∨ R  and  R →₂ J ∨ R.
--       The first one is (h1 ≫ or_inl) and the second is or_inr.

exact or_elim h2 (h1 ≫ or_inl) or_inr
