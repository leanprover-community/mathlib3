import combinatorics.simplicial_complex.extreme_point

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {m : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

--being proven in another branch, so don't need to unsorry it here
theorem geometric_hahn_banach_closed_closed_compact {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A)
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : disjoint A B) :
∃ (f : E →L[ℝ] ℝ) (s t : ℝ), s < t ∧ (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, t < f b) :=
sorry

/--
The Krein-Milman lemma
-/
lemma has_extreme_point_of_convex_of_compact_of_nonempty (hAnemp : A.nonempty)
  (hAcomp : is_compact A) (hAconv : convex A) :
  A.extreme_points.nonempty :=
begin
  sorry
end

/--
The Krein-Milman theorem
-/
lemma eq_closure_convex_hull_extreme_points_of_compact_of_convex (hAcomp : is_compact A)
  (hAconv : convex A) :
  A = closure (convex_hull A.extreme_points) :=
begin
  let B := closure (convex_hull A.extreme_points),
  have hBA : B ⊆ A :=
    closure_minimal (convex_hull_min (λ x hx, hx.1) hAconv) (is_compact.is_closed hAcomp),
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  have := has_extreme_point_of_convex_of_compact_of_nonempty ⟨x, hxA⟩ hAcomp hAconv,
  obtain ⟨l, s, t, hst, hs, hl⟩ := geometric_hahn_banach_closed_closed_compact (convex_singleton x)
    compact_singleton (convex.closure (convex_convex_hull _)) is_closed_closure
    (disjoint_singleton_left.2 hxB),
  let C := {y ∈ A | ∀ z ∈ A, l y ≤ l z},
  have hCext : is_extreme_set A C := sorry,
  have hCnemp : C.nonempty := sorry, --use hAcomp
  have hCclos : is_closed C := sorry,
  have hCcomp : is_compact C := sorry,
  have hCconv : convex C := sorry,
  obtain ⟨y, hyC⟩ := has_extreme_point_of_convex_of_compact_of_nonempty hCnemp hCcomp hCconv,
  have hyA := extreme_points_subset_extreme_points_of_extreme hCext hyC,
  have := hl _ (subset_closure (subset_convex_hull _ hyA)),
  have := hs x (mem_singleton _),
  have := hyC.1.2 x hxA,
  linarith,
end

/--
Carathéodory's theorem, the extreme points way
-/
lemma eq_convex_hull_extreme_points_of_compact_of_convex [finite_dimensional ℝ E]
  (hAcomp : is_compact A) (hAconv : convex A) :
  A = convex_hull A.extreme_points :=
begin
  let B := convex_hull A.extreme_points,
  have hBA : B ⊆ A :=
    convex_hull_min (λ x hx, hx.1) hAconv,
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
end
end affine
