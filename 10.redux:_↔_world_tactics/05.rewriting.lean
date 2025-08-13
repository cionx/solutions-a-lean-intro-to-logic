-- We refer to
--   ¬((P → Q ∨ ¬R) ∧ (R ∨ P → ¬Q) → (R → Q))
-- as longR, and similarly to
--   P ∧ Q ∧ ¬R
-- as shortR. We similarly use longS and shortS.

cases h1
cases h2
-- mp_1  = longS → shortS
-- mpr_1 = shortS → longS
constructor

· -- We need to go
  --   longR  -->  longS  -->  shortS  -->  shortR
  -- but in reverse.
  --
  -- We start by making longR the assumption and shortR the goal.
  intro longR
  -- Now we make shortS the goal.
  -- For some reason tupel deconstruction for lambda arguments doesn’t work here.
  apply λ (t : P ∧ Q ∧ ¬S) ↦ (⟨t.left, t.right.left, mp ≫ t.right.right⟩ : P ∧ Q ∧ ¬R)
  -- Next we make longS the goal.
  apply mp_1
  -- Lastly we deduce longS from longR.
  intro h1
  apply longR
  intro h2 r
  apply h1
  · apply λ (t : (P → Q ∨ ¬R) ∧ (R ∨ P → ¬Q)) ↦
      ⟨
        t.left ≫ (or_elim · (identity ≫ or_inl) (modus_tollens mpr ≫ or_inr)),
        (or_elim · (mpr ≫ or_inl) or_inr) ≫ t.right
      ⟩
    assumption
  · apply mp
    assumption

· -- Now we need to go
  --   shortR  -->  shortS  -->  longS  -->  longR
  -- but once again in reverse.
  --
  -- We start by making shortR the assumption and longR the goal.
  intro shortR
  -- Next we change the goal from longR to both ¬longS and shortS.
  intro h1
  apply mpr_1
  -- Now we deduce shortS from shortR.
  apply λ (t : P ∧ Q ∧ ¬R) ↦ ⟨t.left, t.right.left, mpr ≫ t.right.right⟩
  assumption
  -- Lastly we deduce ¬longS.
  intro h2
  intro s
  apply h1
  · apply λ (t : (P → Q ∨ ¬S) ∧ (S ∨ P → ¬Q)) ↦
      ⟨
        t.left ≫ (or_elim · (identity ≫ or_inl) (modus_tollens mp ≫ or_inr)),
        (or_elim · (mp ≫ or_inl) or_inr) ≫ t.right
      ⟩
    assumption
  · apply mpr
    assumption
