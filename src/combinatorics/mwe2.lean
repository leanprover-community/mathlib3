import analysis.convex.basic
import linear_algebra.affine_space.independent

open_locale classical

lemma disjoint_convex_hulls {m : ℕ} {X : set (fin m → ℝ)}
  (hX : affine_independent ℝ (λ p, p : X → fin m → ℝ))
  (Y₁ Y₂ : set (fin m → ℝ)) (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull Y₁ ∩ convex_hull Y₂ ⊆ convex_hull (Y₁ ∩ Y₂) :=
begin
end

lemma kenny (M : Type*) [add_comm_group M] [vector_space ℝ M] (s : affine_subspace ℝ M) :
  convex (s : set M) :=
λ x y hxs hys a b ha hb hab,
calc a • x + b • y = b • (y - x) + x : convex.combo_to_vadd hab
               ... ∈ s : s.2 _ hys hxs hxs

example {m : ℕ} (X : set (fin m → ℝ)) :
  convex (affine_span ℝ X : set (fin m → ℝ)) :=
kenny _ _

example {m : ℕ}
  (points : fin (m + 1) → fin (m + 1) → ℝ) -- We have (m+1) points in R^(m+1)
  (independent : affine_independent ℝ points) -- which are affinely independent
  (on_simplex : ∀ (x : fin (m + 1)), points x ∈ std_simplex (fin (m + 1)))
      -- and they're all on the standard (m+1)-simplex
  (h3 : ∀ (x : fin (m + 1)), points x 0 = 0) : -- and they all have x₀ = 0
  false := -- is a contradiction
begin

end
