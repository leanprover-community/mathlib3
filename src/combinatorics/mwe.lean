import analysis.convex.basic

variables {E : Type*} [add_comm_group E] [vector_space ℝ E]

def is_extreme (s : set E) (x : E) : Prop :=
x ∈ s ∧ ∀ (x₁ x₂ ∈ s), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂

variables {m : ℕ}

lemma std_simplex_extreme_points (x : fin m → ℝ) (i : fin m) :
  is_extreme (std_simplex (fin m)) (λ j, ite (i = j) 1 0) :=
sorry
