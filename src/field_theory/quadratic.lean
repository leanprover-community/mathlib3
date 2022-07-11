import number_theory.number_field

/-

Theory of quadratic fields

-/

noncomputable theory

open finite_dimensional

/-- A number field is a *quadratic field* if its dimension over ℚ is 2. -/
def is_quadratic_field (K : Type*) [field K] [number_field K] :=
finrank ℚ K = 2

namespace is_quadratic_field

variables {K : Type*} [field K] [number_field K]

open polynomial

theorem exists_d (h : is_quadratic_field K) : ∃ d : ℤ, squarefree d ∧
  polynomial.is_splitting_field ℚ K (X^2 - d) :=
begin
  -- choose x in K but not in ℚ
  -- take min poly and then complete the square
  -- Now it's x^2-e with e a non-zero rational
  -- now scale x until e is squareefree integer.
  -- nice challenge :-)
  sorry
end

/-- The unique squarefree integer `d` such that `K=ℚ(√d)`. -/
def d (h : is_quadratic_field K) := (exists_d h).some

-- TODO prove elationship to discriminant once Kevin has figured out how discriminants work!

theorem unique_d (h : is_quadratic_field K) (d' : ℤ)
  (hd' : squarefree d') (hsplit : polynomial.is_splitting_field ℚ K (X^2 - d')) :
d' = d h :=
begin
  sorry
end

-- also need theorem saying what the ring of integers are.
-- and Pell's equation or units or whatever

end is_quadratic_field
