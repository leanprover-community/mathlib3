/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.mc.affine
import analysis.convex.mc.extreme
import analysis.convex.mc.intrinsic
import analysis.convex.krein_milman

/-!
# The Minkowski-Carathéodory theorem

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]
-/

open filter set
open_locale big_operators topological_space

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E}
  {x y : E} {r : ℝ}

-- Prop 8.5
lemma is_extreme.subset_intrinsic_frontier (h : is_extreme ℝ s t) (hts : t ⊂ s) :
  t ⊆ intrinsic_frontier ℝ s :=
begin
  rintro x hx,
  obtain ⟨y, hys, hyt⟩ := not_subset_iff_exists_mem_not_mem.1 hts.2,
  sorry
end

-- Prop 8.5
lemma exists_proper_face_mem (hs : (interior s).nonempty) (h : is_extreme ℝ s t) (hts : t ⊂ s)
  (hx₀ : x ∈ s) (hx₁ : x ∈ intrinsic_frontier ℝ s) :
  t ⊆ intrinsic_frontier ℝ s :=
begin
  sorry
end

-- Prop 8.9, i
lemma Union_proper_faces (hx : x ∈ intrinsic_frontier ℝ s) (hy : y ∈ intrinsic_interior ℝ s) :
  (⋃ (t ⊂ s) (hst : is_extreme ℝ s t) (ht : convex ℝ t), t) = intrinsic_interior ℝ s :=
begin
  sorry
end

-- Prop 8.9, iii
lemma exists_neg_line_map_mem (hx : x ∈ intrinsic_frontier ℝ s) (hy : y ∈ s) (hr : r < 0) :
  ∃ r, r < 0 ∧ (1 - r) • x + r • y ∈ s :=
begin
  sorry
end

-- Prop 8.9, ii
lemma exists_line_map_mem_eq_Icc (hx : x ∈ intrinsic_frontier ℝ s)
  (hy : y ∈ intrinsic_interior ℝ s) :
  ∃ r, 1 < r ∧ {θ | (1 - θ) • x + θ • y ∈ s} = Icc 0 r :=
begin
  sorry
end

-- Prop 8.10
lemma is_extreme.affine_span_lt_affine_span (hscomp : is_compact s) (hsconv : convex ℝ s)
  (ht : convex ℝ t) (hts : t ⊂ s) (h : is_extreme ℝ s t) :
  affine_span ℝ t < affine_span ℝ s :=
begin
  obtain rfl | ht' := t.eq_empty_or_nonempty,
  { rwa [affine_subspace.span_empty, bot_lt_affine_span, ←empty_ssubset] },
  refine (affine_span_mono _ h.1).lt_of_ne (λ H, _),
  obtain ⟨x, hx⟩ := (ht'.intrinsic_interior ht).of_image,
  have := h.subset_intrinsic_frontier hts,
  rw intrinsic_frontier at this,
  sorry
end

/-- **Minkowski-Carathéodory theorem** -/
lemma exists_combination (hscomp : is_compact s) (hsconv : convex ℝ s) {t : finset E}
  (hs : s ⊆ affine_span ℝ (t : set E)) {e₀ : E} (he₀ : e₀ ∈ s.extreme_points ℝ) (hx : x ∈ s) :
  ∃ u : finset E, e₀ ∈ u ∧ u.card ≤ t.card ∧ (u : set E) ⊆ s.extreme_points ℝ ∧
    x ∈ convex_hull ℝ (u : set E) :=
begin
  classical,
  induction t using finset.induction_on with a t ha ih generalizing s e₀,
  { simp only [finset.coe_empty, affine_subspace.span_empty, affine_subspace.bot_coe] at hs,
    cases hs hx },
    sorry
end

/-- Corollary of the **Minkowski-Carathéodory theorem** -/
lemma convex_hull_extreme_points [finite_dimensional ℝ E] (hscomp : is_compact s)
  (hsconv : convex ℝ s) :
  convex_hull ℝ (s.extreme_points ℝ) = s :=
begin
  refine (convex_hull_min (extreme_points_subset) hsconv).antisymm (λ x hx, _),
  obtain ⟨e₀, he₀⟩ := hscomp.extreme_points_nonempty ⟨x, hx⟩,
  obtain ⟨u, hu₀, hut, hus, hxu⟩ := exists_combination hscomp hsconv _ he₀ hx,
  exact convex_hull_mono hus hxu,
  sorry,
  sorry
end
