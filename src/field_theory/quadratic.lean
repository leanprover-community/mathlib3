import number_theory.number_field

/-

Theory of quadratic fields

-/

open finite_dimensional

/-- A number field is a *quadratic field* if its dimension over ℚ is 2. -/
def is_quadratic_field (K : Type*) [field K] [number_field K] :=
finrank ℚ K = 2

namespace is_quadratic_field

variables (K : Type*) [field K] [number_field K]

open polynomial

theorem exists_d (h : is_quadratic_field K) : ∃ d : ℤ, squarefree d ∧
  polynomial.is_splitting_field ℚ K (X^2 - d) :=
begin
  sorry
end

end is_quadratic_field
