import analysis.convex.basic
import linear_algebra.affine_space.independent

example {m : ℕ}
  (points : fin (m + 1) → fin (m + 1) → ℝ) -- We have (m+1) points in R^(m+1)
  (independent : affine_independent ℝ points) -- which are affinely independent
  (on_simplex : ∀ (x : fin (m + 1)), points x ∈ std_simplex (fin (m + 1)))
      -- and they're all on the standard (m+1)-simplex
  (h3 : ∀ (x : fin (m + 1)), points x 0 = 0) : -- and they all have x₀ = 0
  false := -- is a contradiction
begin

end
