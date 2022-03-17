/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.locally_convex.balanced_core_hull

/-!
# Balanced Basis

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open_locale pointwise topological_space filter

variables {𝕜 E : Type*}

section balanced_core

variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [topological_space E]
  [has_continuous_smul 𝕜 E]

lemma balanced_core_is_closed {U : set E} (hU : is_closed U) : is_closed (balanced_core 𝕜 U) :=
begin
  by_cases h : (0 : E) ∈ U,
  { rw balanced_core_eq_Inter h,
    refine is_closed_Inter (λ a, _),
    refine is_closed_Inter (λ ha, _),
    have ha' := lt_of_lt_of_le zero_lt_one ha,
    rw norm_pos_iff at ha',
    refine is_closed_map_smul_of_ne_zero ha' U hU },
  convert is_closed_empty,
  contrapose! h,
  exact balanced_core_nonempty_iff.mp (set.ne_empty_iff_nonempty.mp h),
end

lemma balanced_core_emptyset : balanced_core 𝕜 (∅ : set E) = ∅ :=
set.eq_empty_of_subset_empty (balanced_core_subset _)

lemma subset_balanced_core {U V : set E} (hV' : (0 : E) ∈ V)
  (hUV : ∀ (a : 𝕜) (ha : ∥a∥ ≤ 1), a • U ⊆ V) :
  U ⊆ balanced_core 𝕜 V :=
begin
  rw balanced_core_eq_Inter hV',
  refine set.subset_Inter₂ (λ a ha, _),
  rw [←one_smul 𝕜 U, ←mul_inv_cancel (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one ha)),
    ←smul_eq_mul, smul_assoc],
  refine set.smul_set_mono (hUV a⁻¹ _),
  rw [norm_inv],
  exact inv_le_one ha,
end

lemma balanced_core_nhds_zero {U : set E} (hU : U ∈ 𝓝 (0 : E)) : balanced_core 𝕜 U ∈ 𝓝 (0 : E) :=
begin
  have h : filter.tendsto (λ (x : 𝕜 × E), x.fst • x.snd) (𝓝 (0,0)) (𝓝 ((0 : 𝕜) • (0 : E))) :=
  continuous_iff_continuous_at.mp has_continuous_smul.continuous_smul (0, 0),
  rw [smul_zero] at h,
  have h' := filter.has_basis.prod (@metric.nhds_basis_ball 𝕜 _ 0) (filter.basis_sets (𝓝 (0 : E))),
  simp_rw [←nhds_prod_eq, id.def] at h',
  have h'' := filter.tendsto.basis_left h h' U hU,
  rcases h'' with ⟨x, hx, h''⟩,
  cases normed_field.exists_norm_lt 𝕜 hx.left with y hy,
  have hy' : y ≠ 0 := norm_pos_iff.mp hy.1,
  let W := y • x.snd,
  have hW : ∀ (a : 𝕜) (ha : ∥a∥ ≤ 1), a • W ⊆ U :=
  begin
    intros a ha,
    refine set.subset.trans _ (set.maps_to'.mp h''),
    intros z hz,
    rw [set.image_prod, set.image2_smul],
    rw set.mem_smul_set at hz,
    rcases hz with ⟨z', hz', hz⟩,
    rw [←hz, set.mem_smul],
    refine ⟨a • y, y⁻¹ • z', _, _, _⟩,
    { rw [algebra.id.smul_eq_mul, mem_ball_zero_iff, norm_mul, ←one_mul x.fst],
      exact mul_lt_mul' ha hy.2 hy.1.le zero_lt_one },
    { convert set.smul_mem_smul_set hz',
      rw [←smul_assoc y⁻¹ y x.snd, smul_eq_mul, inv_mul_cancel hy', one_smul] },
    rw [smul_assoc, ←smul_assoc y y⁻¹ z', smul_eq_mul, mul_inv_cancel hy', one_smul],
  end,
  rw ←filter.exists_mem_subset_iff,
  refine ⟨W, _, subset_balanced_core (mem_of_mem_nhds hU) hW⟩,
  sorry,
end

variables (𝕜 E)

lemma closed_balanced_nhds_basis [regular_space E] : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ 𝓝 (0 : E) ∧ is_closed s ∧ balanced 𝕜 s) id :=
begin
  refine (closed_nhds_basis 0).to_has_basis (λ s hs, _) (λ s hs, ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩),
  refine ⟨balanced_core 𝕜 s, ⟨balanced_core_nhds_zero hs.1, _⟩, balanced_core_subset s⟩,
  refine ⟨balanced_core_is_closed hs.2, balanced_core_balanced s⟩
end

end balanced_core
