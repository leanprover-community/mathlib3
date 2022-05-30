/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.krein_milman

/-!
# The Minkowski-Carathéodory theorem
-/

open_locale affine big_operators classical
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {s B : set E}

/-- **Minkowski-Carathéodory theorem** -/
lemma convex_hull_extreme_points [finite_dimensional ℝ E] (hscomp : is_compact s)
  (hsconv : convex ℝ s) :
  convex_hull ℝ (s.extreme_points ℝ) = s :=
begin

  sorry
  /-let B := convex_hull ℝ (s.extreme_points ℝ),
  have hBA : B ⊆ s :=
    convex_hull_min (λ x hx, hx.1) hsconv,
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (s \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  sorry-/
end

lemma closed_convex_hull_extreme_points_of_compact_of_convex [finite_dimensional ℝ E]
  (hscomp : is_compact s) (hsconv : convex ℝ s) :
  is_closed (convex_hull ℝ $ s.extreme_points ℝ) :=
closure_eq_iff_is_closed.1 $
  by rw [closure_convex_hull_extreme_points hscomp hsconv, convex_hull_extreme_points hscomp hsconv]
