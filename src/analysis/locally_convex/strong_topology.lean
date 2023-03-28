/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/


import analysis.locally_convex.with_seminorms
import topology.algebra.module.strong_topology
import topology.algebra.module.locally_convex

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Todo

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/

open_locale topology uniform_convergence

variables {𝕜 𝕜₂ E F ι 𝓕 : Type*}

namespace continuous_linear_map

section general

variables [add_comm_group E] [topological_space E]
  [add_comm_group F] [topological_space F] [topological_add_group F]
  [normed_field 𝕜] [nontrivially_normed_field 𝕜₂] [module 𝕜 E] [module 𝕜₂ F]
  [has_continuous_const_smul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂}

#check normed_add_comm_group.tendsto_nhds_nhds

#check filter.has_basis.tendsto_right_iff

variable [nonempty ι]

variables [module ℝ F] [module ℝ E]

lemma with_seminorms.tendsto_nhds [ring_hom_isometric σ₁₂] {p : ι → seminorm 𝕜₂ F} (hp : with_seminorms p)
  (u : E → F) (i : ι) {M : set E} (hM : bornology.is_vonN_bounded 𝕜 M)
  (h : filter.tendsto u (𝓝 0) (𝓝 0)) : ∀ ε, 0 < ε →
    ∃ (r : ℝ) (h : 0 < r), ∀ x, r • x ∈ M → p i (u x) < ε :=
begin
  intros ε hε,
  rcases hM ((hp.tendsto_nhds u 0).1 h i ε hε) with ⟨r, hr, h⟩,
  use [r, hr],
  intros x hx,
  specialize h (r • 1),
  have h' := set.mem_of_subset_of_mem h hx,
  rw set.mem_smul_set at h',
  rcases h' with ⟨y, hy, h'⟩,
  simp only [set.mem_set_of_eq] at hy,
  sorry,
end

theorem bound' [ring_hom_isometric σ₁₂] {p : ι → seminorm 𝕜₂ F} (hp : with_seminorms p) {M : set E}
  (hM : bornology.is_vonN_bounded 𝕜 M) (f : E →SL[σ₁₂] F) (i : ι) :
  ∃ C, 0 < C ∧ (∀ x : E, x ∈ M → p i (f x) ≤ C) :=
begin
  have h := f.cont.tendsto 0,
  simp only [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe,
    linear_map.to_fun_eq_coe, map_zero] at h,
  rw hp.tendsto_nhds f 0 at h,
  specialize h i 1 zero_lt_one,
  rcases hM h with ⟨r, hr, h⟩,
  simp only [sub_zero] at h,
  --rcases hM ((hp.tendsto_nhds f 0).1 h i ε hε) with ⟨r, hr, h⟩,
  sorry,
end

#exit

lemma with_seminorms.tendsto_nhds {p : seminorm 𝕜₂ F} (hp : continuous p) (u : E → F) {f : filter E} (y₀ : F)
  (h : filter.tendsto u f (𝓝 y₀)) : ∀ ε, 0 < ε → ∀ᶠ x in f, p (u x - y₀) < ε :=
begin
  intros ε hε,
  have hp' := hp.tendsto y₀,
  rw metric.tendsto_nhds at hp',
  specialize hp' ε hε,
  have := hp'.filter_mono h,
  rw [filter.eventually_map] at this,
  refine this.mono (λ x hx, _),
  simp only at hx,
  rw real.dist_eq at hx,
  refine lt_of_le_of_lt _ hx,
  sorry,
end

/-

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
lemma semilinear_map_class.bound_of_continuous [semilinear_map_class 𝓕 σ₁₂ E F]
  {p : seminorm 𝕜₂ F} (hp : continuous p) {M : set E}
  (f : 𝓕) (hf : continuous f) : ∃ C, 0 < C ∧ (∀ x : E, x ∈ M → p (f x) ≤ C) :=
begin
  have hf' := hf.tendsto 0,
  rw [map_zero] at hf',
  /-rcases normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  simp only [sub_zero, map_zero] at hε,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have : 0 < ‖c‖ / ε, from div_pos (zero_lt_one.trans hc) ε_pos,
  refine ⟨‖c‖ / ε, this, λ x, _⟩,
  by_cases hx : ‖x‖ = 0,
  { rw [hx, mul_zero],
    exact le_of_eq (norm_image_of_norm_zero f hf hx) },
  refine semilinear_map_class.bound_of_shell_semi_normed f ε_pos hc (λ x hle hlt, _) hx,
  refine (hε _ hlt).le.trans _,
  rwa [← div_le_iff' this, one_div_div]-/
  sorry,
end

theorem bound' {p : seminorm 𝕜₂ F} (hp : continuous p) {M : set E} (f : E →SL[σ₁₂] F) :
  ∃ C, 0 < C ∧ (∀ x : E, x ∈ M → p (f x) ≤ C) := sorry

theorem bound (p : seminorm 𝕜₂ F) (M : set E) (f : E →SL[σ₁₂] F) :
  ∃ C, 0 < C ∧ (∀ x : E, x ∈ M → p (f x) ≤ C) := sorry

noncomputable
def operator_seminorm_aux (p : seminorm 𝕜₂ F) (M : set E) (f : E →SL[σ₁₂] F) : ℝ :=
Inf {c | 0 ≤ c ∧ ∀ x, x ∈ M → p (f x) ≤ c}

lemma bounds_nonempty (p : seminorm 𝕜₂ F) (M : set E)  {f : E →SL[σ₁₂] F} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, x ∈ M → p (f x) ≤ c } :=
let ⟨M, hMp, hMb⟩ := f.bound p M in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below (p : seminorm 𝕜₂ F) (M : set E) {f : E →SL[σ₁₂] F} :
  bdd_below { c | 0 ≤ c ∧ ∀ x, x ∈ M → p (f x) ≤ c } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

noncomputable
def operator_seminorm [has_continuous_const_smul 𝕜 F] (p : seminorm 𝕜 F) (M : set E) :
  seminorm 𝕜 (E →L[𝕜] F) :=
seminorm.of (operator_seminorm_aux p M)
  (λ u v, begin

    sorry,
  end) sorry
-/
variables [module ℝ F] [module ℝ E] [has_continuous_const_smul ℝ F] [locally_convex_space ℝ F]
  [smul_comm_class 𝕜₂ ℝ F]

lemma strong_topology.locally_convex_space (𝔖 : set (set E)) (h𝔖₁ : 𝔖.nonempty)
  (h𝔖₂ : directed_on (⊆) 𝔖) :
  @locally_convex_space ℝ (E →SL[σ₁₂] F) _ _ _ (strong_topology σ₁₂ F 𝔖) :=
begin
  letI : topological_space (E →SL[σ₁₂] F) := strong_topology σ₁₂ F 𝔖,
  haveI : topological_add_group (E →SL[σ₁₂] F) := strong_topology.topological_add_group _ _ _,
  refine locally_convex_space.of_basis_zero _ _ _ _
    (strong_topology.has_basis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (locally_convex_space.convex_basis_zero ℝ F)) _,
  rintros ⟨S, V⟩ ⟨hS, hVmem, hVconvex⟩ f hf g hg a b ha hb hab x hx,
  exact hVconvex (hf x hx) (hg x hx) ha hb hab,
end

/-
variables [nonempty ι] [normed_field 𝕜] [normed_space ℝ 𝕜]
  [module 𝕜 F] [is_scalar_tower ℝ 𝕜 F]
lemma strong_topology.with_seminorm (𝔖 : set (set E)) (h𝔖₁ : 𝔖.nonempty)
  (h𝔖₂ : directed_on (⊆) 𝔖) {p : ι → seminorm ℝ F} (hp : with_seminorms p) :
-/
end general

section bounded_sets

variables [add_comm_group E] [module ℝ E] [topological_space E]
  [add_comm_group F] [module ℝ F] [topological_space F] [topological_add_group F]
  [has_continuous_const_smul ℝ F] [locally_convex_space ℝ F]
  [normed_field 𝕜] [module 𝕜 E] [module 𝕜 F] [smul_comm_class 𝕜 ℝ F]

instance : locally_convex_space ℝ (E →L[𝕜] F) :=
strong_topology.locally_convex_space _ ⟨∅, bornology.is_vonN_bounded_empty 𝕜 E⟩
  (directed_on_of_sup_mem $ λ _ _, bornology.is_vonN_bounded.union)

end bounded_sets

end continuous_linear_map
