/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.topology
import analysis.inner_product_space.pi_L2

/-!
# Convex functions are continuous

This file proves that a convex function from a finite dimensional real inner product space to `ℝ` is
continuous.

## TODO

Can this be extended to real normed spaces?
-/

section
variables {α β : Type*} [topological_space α] [topological_space β] {s : set α} {f : α → β}

lemma is_open.continuous_on_iff (hs : is_open s) :
  continuous_on f s ↔ ∀ ⦃a⦄, a ∈ s → continuous_at f a :=
ball_congr $ λ _, continuous_within_at_iff_continuous_at ∘ hs.mem_nhds

end

namespace finset
variables {R E F ι ι' : Type*} [linear_ordered_field R] [add_comm_group E] [add_comm_group F]
  [module R E] [module R F]

open_locale big_operators

lemma mem_convex_hull {s : finset E} {x : E} :
  x ∈ convex_hull R (s : set E) ↔
    ∃ (w : E → R) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1), s.center_mass w id = x :=
by rw [convex_hull_eq, set.mem_set_of_eq]

end finset

namespace finset
variables {𝕜 E β ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E]
  [linear_ordered_add_comm_group β] [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E}
  {f : E → β} {t : finset E} {x : E}

open_locale big_operators

lemma center_mass_le_sup {s : finset ι} (hs : s.nonempty) {w : ι → 𝕜} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
  (hw₁ : 0 < ∑ i in s, w i) {f : ι → β} : s.center_mass w f ≤ s.sup' hs f :=
begin
  rw [center_mass, inv_smul_le_iff hw₁, sum_smul],
  exact sum_le_sum (λ i hi, smul_le_smul_of_nonneg (le_sup' _ hi) $ hw₀ i hi),
  apply_instance,
end

lemma inf_le_center_mass {s : finset ι} (hs : s.nonempty) {w : ι → 𝕜} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
  (hw₁ : 0 < ∑ i in s, w i) {f : ι → β} : s.inf' hs f ≤ s.center_mass w f :=
@center_mass_le_sup 𝕜 βᵒᵈ _ _ _ _ _ _ hs _ hw₀ hw₁ _

lemma le_sup_of_mem_convex_hull (hf : convex_on 𝕜 (convex_hull 𝕜 (t : set E)) f)
  (hx : x ∈ convex_hull 𝕜 (t : set E)) :
  f x ≤ t.sup' (coe_nonempty.1 $ convex_hull_nonempty_iff.1 ⟨x, hx⟩) f :=
begin
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convex_hull.1 hx,
  have := hw₁.ge,
  exact (hf.map_center_mass_le hw₀ (by positivity) (subset_convex_hull _ _)).trans
    (center_mass_le_sup _ hw₀ $ by positivity),
end

lemma inf_le_of_mem_convex_hull (hf : concave_on 𝕜 (convex_hull 𝕜 (t : set E)) f)
  (hx : x ∈ convex_hull 𝕜 (t : set E)) :
  t.inf' (coe_nonempty.1 $ convex_hull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
le_sup_of_mem_convex_hull hf.dual hx

end finset

section
variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E] {s : set E} {x : E}

open finite_dimensional metric set
open_locale big_operators

-- TODO: Can we weaken `inner_product_space` to `normed_space`?
/-- We can intercalate a polyhedron between an open set and one if its elements, namely a small
enough cube. -/
lemma is_open.exists_mem_interior_convex_hull_finset (hs : is_open s) (hx : x ∈ s) :
  ∃ t : finset E, x ∈ interior (convex_hull ℝ (t : set E)) ∧ convex_hull ℝ (t : set E) ⊆ s :=
begin
  classical,
  obtain ⟨ε, hε, hεx⟩ := is_open_iff.1 hs _ hx,
  --TODO: `ε / finrank ℝ E` is not quite the right constant.
  -- Do we have to treat `finrank ℝ E = 0` separately?
  set f : finset (fin (finrank ℝ E)) → E :=
    λ u, ∑ i, if i ∈ u then (ε / finrank ℝ E) • std_orthonormal_basis ℝ E i else
      -(ε / finrank ℝ E) • std_orthonormal_basis ℝ E i with hf,
  set t := finset.univ.image (λ u, x + f u) with ht,
  refine ⟨t, _, (convex_hull_min _ $ convex_ball _ _).trans hεx⟩,
  { rw [mem_interior_iff_mem_nhds, metric.mem_nhds_iff],
    refine ⟨ε / finrank ℝ E, _, λ y hy, _⟩,
    sorry,
    sorry,
  },
  { have hε' : 0 ≤ ε / finrank ℝ E := by positivity,
    simp_rw [ht, finset.coe_image, finset.coe_univ,image_univ, range_subset_iff, mem_ball,
      dist_self_add_left],
    rintro u,
    refine (norm_sum_le _ _).trans_lt _,
    simp_rw [apply_ite norm, norm_smul, norm_neg, if_t_t, (std_orthonormal_basis ℝ E).orthonormal.1,
      finset.sum_const, real.norm_of_nonneg hε', mul_one, finset.card_univ, fintype.card_fin,
      nsmul_eq_mul],
    sorry }
end

end

open finite_dimensional metric set

variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E] {s : set E} {f : E → ℝ}

-- TODO: This proof actually gives local Lipschitz continuity.
-- See `is_open.exists_mem_interior_convex_hull_finset` for more todo.
protected lemma convex_on.continuous_on (hf : convex_on ℝ s f) : continuous_on f (interior s) :=
begin
  classical,
  refine is_open_interior.continuous_on_iff.2 (λ x hx, _),
  obtain ⟨t, hxt, hts⟩ := is_open_interior.exists_mem_interior_convex_hull_finset hx,
  set M := t.sup' (convex_hull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  refine metric.continuous_at_iff.2 (λ ε hε, _),
  have : f x ≤ M := finset.le_sup_of_mem_convex_hull
    (hf.subset (hts.trans interior_subset) $ convex_convex_hull _ _) (interior_subset hxt),
  refine ⟨ε / (M - f x), _, λ y hy, _⟩,
  sorry,
  sorry,
end

lemma concave_on.continuous_on (hf : concave_on ℝ s f) : continuous_on f s := sorry
