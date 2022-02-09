universes u u₁ u₂ u₃

section axiom_sets

variable {α : Type*}

section rank

def satisfies_R0 (r : set α → ℤ) : Prop :=
  ∀ X, 0 ≤ r X

def satisfies_R1 (r : set α → ℤ) : Prop :=
  ∀ X, r X ≤ fincard X

def satisfies_R2 (r : set α → ℤ) : Prop :=
  ∀ X Y, X ⊆ Y → r X ≤ r Y

def satisfies_R3 (r : set α → ℤ) : Prop :=
  ∀ X Y, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

@[ext] structure rankfun (α : Type*) :=
  (r : set α → ℤ)
  (R0 : satisfies_R0 r)
  (R1 : satisfies_R1 r)
  (R2 : satisfies_R2 r)
  (R3 : satisfies_R3 r)

end rank
