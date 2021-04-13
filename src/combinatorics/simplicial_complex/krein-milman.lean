import combinatorics.simplicial_complex.extreme_point

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {m : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

/--
The Krein-Milman lemma
-/
lemma has_extreme_point_of_convex_of_compact_of_nonempty (hAnemp : A.nonempty)
  (hAcomp : is_compact A) (hAconv : convex A) :
  ∃ x : E, extreme_point A x :=
begin
  sorry
end

/--
The Krein-Milman theorem
-/
lemma eq_convex_hull_extreme_points_of_compact_of_convex (hAcomp : is_compact A) (hAconv : convex A) :
  A = closure (convex_hull {x | extreme_point A x}) :=
begin
  let B := closure (convex_hull {x | extreme_point A x}),
  have hBA : B ⊆ A :=
    closure_minimal (convex_hull_min (λ x hx, hx.1) hAconv) (is_compact.is_closed hAcomp),
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
end
end affine
