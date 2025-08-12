constructor
· intro h q
  cases h
  constructor
  · intro p
    apply (and_left : R ∧ Q → R)
    apply mp
    constructor
    · assumption
    · assumption
  intro r
  apply (and_left : P ∧ Q → P)
  apply mpr
  constructor
  · assumption
  · assumption
· intro h
  constructor
  · intro ⟨p, q⟩
    constructor
    · apply (h q).mp
      assumption
    · assumption
  · intro ⟨r, q⟩
    constructor
    · apply (h q).mpr
      assumption
    · assumption
