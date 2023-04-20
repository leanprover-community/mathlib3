/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.basic

/-!
# Balanced Core and Balanced Hull

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `balanced_core`: The largest balanced subset of a set `s`.
* `balanced_hull`: The smallest balanced superset of a set `s`.

## Main statements

* `balanced_core_eq_Inter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `‖r‖ ≤ 1`. We show that `balanced_hull` has the
defining properties of a hull in `balanced.hull_minimal` and `subset_balanced_hull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balanced_core_eq_Inter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open set
open_locale pointwise topology filter


variables {𝕜 E ι : Type*}

section balanced_hull

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_smul
variables (𝕜) [has_smul 𝕜 E] {s t : set E} {x : E}

/-- The largest balanced subset of `s`.-/
def balanced_core (s : set E) := ⋃₀ {t : set E | balanced 𝕜 t ∧ t ⊆ s}

/-- Helper definition to prove `balanced_core_eq_Inter`-/
def balanced_core_aux (s : set E) := ⋂ (r : 𝕜) (hr : 1 ≤ ‖r‖), r • s

/-- The smallest balanced superset of `s`.-/
def balanced_hull (s : set E) := ⋃ (r : 𝕜) (hr : ‖r‖ ≤ 1), r • s

variables {𝕜}

lemma balanced_core_subset (s : set E) : balanced_core 𝕜 s ⊆ s := sUnion_subset $ λ t ht, ht.2

lemma balanced_core_empty : balanced_core 𝕜 (∅ : set E) = ∅ :=
eq_empty_of_subset_empty (balanced_core_subset _)

lemma mem_balanced_core_iff : x ∈ balanced_core 𝕜 s ↔ ∃ t, balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t :=
by simp_rw [balanced_core, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

lemma smul_balanced_core_subset (s : set E) {a : 𝕜} (ha : ‖a‖ ≤ 1) :
  a • balanced_core 𝕜 s ⊆ balanced_core 𝕜 s :=
begin
  rintro x ⟨y, hy, rfl⟩,
  rw mem_balanced_core_iff at hy,
  rcases hy with ⟨t, ht1, ht2, hy⟩,
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩,
end

lemma balanced_core_balanced (s : set E) : balanced 𝕜 (balanced_core 𝕜 s) :=
λ _, smul_balanced_core_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`.-/
lemma balanced.subset_core_of_subset (hs : balanced 𝕜 s) (h : s ⊆ t) : s ⊆ balanced_core 𝕜 t :=
subset_sUnion_of_mem ⟨hs, h⟩

lemma mem_balanced_core_aux_iff : x ∈ balanced_core_aux 𝕜 s ↔ ∀ r : 𝕜, 1 ≤ ‖r‖ → x ∈ r • s :=
mem_Inter₂

lemma mem_balanced_hull_iff : x ∈ balanced_hull 𝕜 s ↔ ∃ (r : 𝕜) (hr : ‖r‖ ≤ 1), x ∈ r • s :=
mem_Union₂

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
lemma balanced.hull_subset_of_subset (ht : balanced 𝕜 t) (h : s ⊆ t) : balanced_hull 𝕜 s ⊆ t :=
λ x hx, by { obtain ⟨r, hr, y, hy, rfl⟩ := mem_balanced_hull_iff.1 hx, exact ht.smul_mem hr (h hy) }

end has_smul

section module
variables [add_comm_group E] [module 𝕜 E] {s : set E}

lemma balanced_core_zero_mem (hs : (0 : E) ∈ s) : (0 : E) ∈ balanced_core 𝕜 s :=
mem_balanced_core_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, zero_mem_zero⟩

lemma balanced_core_nonempty_iff : (balanced_core 𝕜 s).nonempty ↔ (0 : E) ∈ s :=
⟨λ h, zero_subset.1 $ (zero_smul_set h).superset.trans $ (balanced_core_balanced s (0 : 𝕜) $
  norm_zero.trans_le zero_le_one).trans $ balanced_core_subset _,
    λ h, ⟨0, balanced_core_zero_mem h⟩⟩

variables (𝕜)

lemma subset_balanced_hull [norm_one_class 𝕜] {s : set E} : s ⊆ balanced_hull 𝕜 s :=
λ _ hx, mem_balanced_hull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

variables {𝕜}

lemma balanced_hull.balanced (s : set E) : balanced 𝕜 (balanced_hull 𝕜 s) :=
begin
  intros a ha,
  simp_rw [balanced_hull, smul_set_Union₂, subset_def, mem_Union₂],
  rintro x ⟨r, hr, hx⟩,
  rw ←smul_assoc at hx,
  exact ⟨a • r, (semi_normed_ring.norm_mul _ _).trans (mul_le_one ha (norm_nonneg r) hr), hx⟩,
end

end module
end semi_normed_ring

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] {s t : set E}

@[simp] lemma balanced_core_aux_empty : balanced_core_aux 𝕜 (∅ : set E) = ∅ :=
begin
  simp_rw [balanced_core_aux, Inter₂_eq_empty_iff, smul_set_empty],
  exact λ _, ⟨1, norm_one.ge, not_mem_empty _⟩,
end

lemma balanced_core_aux_subset (s : set E) : balanced_core_aux 𝕜 s ⊆ s :=
λ x hx, by simpa only [one_smul] using mem_balanced_core_aux_iff.1 hx 1 norm_one.ge

lemma balanced_core_aux_balanced (h0 : (0 : E) ∈ balanced_core_aux 𝕜 s):
  balanced 𝕜 (balanced_core_aux 𝕜 s) :=
begin
  rintro a ha x ⟨y, hy, rfl⟩,
  obtain rfl | h := eq_or_ne a 0,
  { rwa zero_smul },
  rw mem_balanced_core_aux_iff at ⊢ hy,
  intros r hr,
  have h'' : 1 ≤ ‖a⁻¹ • r‖,
  { rw [norm_smul, norm_inv],
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr },
  have h' := hy (a⁻¹ • r) h'',
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h',
end

lemma balanced_core_aux_maximal (h : t ⊆ s) (ht : balanced 𝕜 t) : t ⊆ balanced_core_aux 𝕜 s :=
begin
  refine λ x hx, mem_balanced_core_aux_iff.2 (λ r hr, _),
  rw mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp $ zero_lt_one.trans_le hr),
  refine h (ht.smul_mem _ hx),
  rw norm_inv,
  exact inv_le_one hr,
end

lemma balanced_core_subset_balanced_core_aux : balanced_core 𝕜 s ⊆ balanced_core_aux 𝕜 s :=
balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

lemma balanced_core_eq_Inter (hs : (0 : E) ∈ s) :
  balanced_core 𝕜 s = ⋂ (r : 𝕜) (hr : 1 ≤ ‖r‖), r • s :=
begin
  refine balanced_core_subset_balanced_core_aux.antisymm  _,
  refine (balanced_core_aux_balanced _).subset_core_of_subset (balanced_core_aux_subset s),
  exact balanced_core_subset_balanced_core_aux (balanced_core_zero_mem hs),
end

lemma subset_balanced_core (ht : (0 : E) ∈ t) (hst : ∀ (a : 𝕜) (ha : ‖a‖ ≤ 1), a • s ⊆ t) :
  s ⊆ balanced_core 𝕜 t :=
begin
  rw balanced_core_eq_Inter ht,
  refine subset_Inter₂ (λ a ha, _),
  rw ←smul_inv_smul₀ (norm_pos_iff.mp $ zero_lt_one.trans_le ha) s,
  refine smul_set_mono (hst _ _),
  rw [norm_inv],
  exact inv_le_one ha,
end

end normed_field

end balanced_hull

/-! ### Topological properties -/

section topology

variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [topological_space E]
  [has_continuous_smul 𝕜 E] {U : set E}

protected lemma is_closed.balanced_core (hU : is_closed U) : is_closed (balanced_core 𝕜 U) :=
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
  exact balanced_core_nonempty_iff.mp (set.nonempty_iff_ne_empty.2 h),
end

lemma balanced_core_mem_nhds_zero (hU : U ∈ 𝓝 (0 : E)) : balanced_core 𝕜 U ∈ 𝓝 (0 : E) :=
begin
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : ∃ (r : ℝ) (V : set E), 0 < r ∧ V ∈ 𝓝 (0 : E) ∧
    ∀ (c : 𝕜) (y : E), ‖c‖ < r → y ∈ V → c • y ∈ U,
  { have h : filter.tendsto (λ (x : 𝕜 × E), x.fst • x.snd) (𝓝 (0,0)) (𝓝 0),
      from continuous_smul.tendsto' (0, 0) _ (smul_zero _),
    simpa only [← prod.exists', ← prod.forall', ← and_imp, ← and.assoc, exists_prop]
      using h.basis_left (normed_add_comm_group.nhds_zero_basis_norm_lt.prod_nhds
        ((𝓝 _).basis_sets)) U hU },
  rcases normed_field.exists_norm_lt 𝕜 hr with ⟨y, hy₀, hyr⟩,
  rw [norm_pos_iff] at hy₀,
  have : y • V ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV,
  -- It remains to show that `y • V ⊆ balanced_core 𝕜 U`
  refine filter.mem_of_superset this (subset_balanced_core (mem_of_mem_nhds hU) $ λ a ha, _),
  rw [smul_smul],
  rintro _ ⟨z, hz, rfl⟩,
  refine hrVU _ _ _ hz,
  rw [norm_mul, ← one_mul r],
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos
end

variables (𝕜 E)

lemma nhds_basis_balanced : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ 𝓝 (0 : E) ∧ balanced 𝕜 s) id :=
filter.has_basis_self.mpr
  (λ s hs, ⟨balanced_core 𝕜 s, balanced_core_mem_nhds_zero hs,
            balanced_core_balanced s, balanced_core_subset s⟩)

lemma nhds_basis_closed_balanced [regular_space E] : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ 𝓝 (0 : E) ∧ is_closed s ∧ balanced 𝕜 s) id :=
begin
  refine (closed_nhds_basis 0).to_has_basis (λ s hs, _) (λ s hs, ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩),
  refine ⟨balanced_core 𝕜 s, ⟨balanced_core_mem_nhds_zero hs.1, _⟩, balanced_core_subset s⟩,
  exact ⟨hs.2.balanced_core, balanced_core_balanced s⟩
end

end topology
