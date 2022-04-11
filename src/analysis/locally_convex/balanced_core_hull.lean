/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.seminorm
import order.closure

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balanced_core`: The largest balanced subset of a set `s`.
* `balanced_hull`: The smallest balanced superset of a set `s`.

## Main statements

* `balanced_core_eq_Inter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `∥r∥ ≤ 1`. We show that `balanced_hull` has the
defining properties of a hull in `balanced.hull_minimal` and `subset_balanced_hull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balanced_core_eq_Inter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open set
open_locale pointwise topological_space filter


variables {𝕜 E ι : Type*}

section balanced_hull

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_scalar
variables [has_scalar 𝕜 E]

variables (𝕜)

/-- The largest balanced subset of `s`.-/
def balanced_core (s : set E) := ⋃₀ {t : set E | balanced 𝕜 t ∧ t ⊆ s}

/-- Helper definition to prove `balanced_core_eq_Inter`-/
def balanced_core_aux (s : set E) := ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s

/-- The smallest balanced superset of `s`.-/
def balanced_hull (s : set E) := ⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • s

variables {𝕜}

lemma balanced_core_subset (s : set E) : balanced_core 𝕜 s ⊆ s :=
begin
  refine sUnion_subset (λ t ht, _),
  simp only [mem_set_of_eq] at ht,
  exact ht.2,
end

lemma balanced_core_emptyset : balanced_core 𝕜 (∅ : set E) = ∅ :=
set.eq_empty_of_subset_empty (balanced_core_subset _)

lemma balanced_core_mem_iff {s : set E} {x : E} : x ∈ balanced_core 𝕜 s ↔
  ∃ t : set E, balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t :=
by simp_rw [balanced_core, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

lemma smul_balanced_core_subset (s : set E) {a : 𝕜} (ha : ∥a∥ ≤ 1) :
  a • balanced_core 𝕜 s ⊆ balanced_core 𝕜 s :=
begin
  rw subset_def,
  intros x hx,
  rw mem_smul_set at hx,
  rcases hx with ⟨y, hy, hx⟩,
  rw balanced_core_mem_iff at hy,
  rcases hy with ⟨t, ht1, ht2, hy⟩,
  rw ←hx,
  refine ⟨t, _, ht1 a ha (smul_mem_smul_set hy)⟩,
  rw mem_set_of_eq,
  exact ⟨ht1, ht2⟩,
end

lemma balanced_core_balanced (s : set E) : balanced 𝕜 (balanced_core 𝕜 s) :=
λ _, smul_balanced_core_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`.-/
lemma balanced.subset_core_of_subset {s t : set E} (hs : balanced 𝕜 s) (h : s ⊆ t):
  s ⊆ balanced_core 𝕜 t :=
begin
  refine subset_sUnion_of_mem _,
  rw [mem_set_of_eq],
  exact ⟨hs, h⟩,
end

lemma balanced_core_aux_mem_iff (s : set E) (x : E) : x ∈ balanced_core_aux 𝕜 s ↔
  ∀ (r : 𝕜) (hr : 1 ≤ ∥r∥), x ∈ r • s :=
by rw [balanced_core_aux, set.mem_Inter₂]

lemma balanced_hull_mem_iff (s : set E) (x : E) : x ∈ balanced_hull 𝕜 s ↔
  ∃ (r : 𝕜) (hr : ∥r∥ ≤ 1), x ∈ r • s :=
by rw [balanced_hull, set.mem_Union₂]

/-- The balanced core of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
lemma balanced.hull_subset_of_subset {s t : set E} (ht : balanced 𝕜 t) (h : s ⊆ t) :
  balanced_hull 𝕜 s ⊆ t :=
begin
  intros x hx,
  rcases (balanced_hull_mem_iff _ _).mp hx with ⟨r, hr, hx⟩,
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩,
  rw ←hx,
  exact balanced_mem ht (h hy) hr,
end

end has_scalar

section add_comm_monoid

variables [add_comm_monoid E] [module 𝕜 E]

lemma balanced_core_nonempty_iff {s : set E} : (balanced_core 𝕜 s).nonempty ↔ (0 : E) ∈ s :=
begin
  split; intro h,
  { cases h with x hx,
    have h' : balanced 𝕜 (balanced_core 𝕜 s) := balanced_core_balanced s,
    have h'' := h' 0 (has_le.le.trans norm_zero.le zero_le_one),
    refine mem_of_subset_of_mem (subset.trans h'' (balanced_core_subset s)) _,
    exact mem_smul_set.mpr ⟨x, hx, zero_smul _ _⟩ },
  refine nonempty_of_mem (mem_of_subset_of_mem _ (mem_singleton 0)),
  exact balanced.subset_core_of_subset zero_singleton_balanced (singleton_subset_iff.mpr h),
end

lemma balanced_core_zero_mem {s : set E} (hs: (0 : E) ∈ s) : (0 : E) ∈ balanced_core 𝕜 s :=
balanced_core_mem_iff.mpr
  ⟨{0}, zero_singleton_balanced, singleton_subset_iff.mpr hs, mem_singleton 0⟩

variables (𝕜)

lemma subset_balanced_hull [norm_one_class 𝕜] {s : set E} : s ⊆ balanced_hull 𝕜 s :=
λ _ hx, (balanced_hull_mem_iff _ _).mpr ⟨1, norm_one.le, mem_smul_set.mp ⟨_, hx, one_smul _ _⟩⟩

variables {𝕜}

lemma balanced_hull.balanced (s : set E) : balanced 𝕜 (balanced_hull 𝕜 s) :=
begin
  intros a ha,
  simp_rw [balanced_hull, smul_set_Union₂, subset_def, mem_Union₂],
  intros x hx,
  rcases hx with ⟨r, hr, hx⟩,
  use [a • r],
  split,
  { rw smul_eq_mul,
    refine has_le.le.trans (semi_normed_ring.norm_mul _ _) _,
    refine mul_le_one ha (norm_nonneg r) hr },
  rw smul_assoc,
  exact hx,
end

end add_comm_monoid

end semi_normed_ring

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

@[simp] lemma balanced_core_aux_empty : balanced_core_aux 𝕜 (∅ : set E) = ∅ :=
begin
  rw [balanced_core_aux, set.Inter₂_eq_empty_iff],
  intros _,
  simp only [smul_set_empty, mem_empty_eq, not_false_iff, exists_prop, and_true],
  exact ⟨1, norm_one.ge⟩,
end

lemma balanced_core_aux_subset (s : set E) : balanced_core_aux 𝕜 s ⊆ s :=
begin
  rw subset_def,
  intros x hx,
  rw balanced_core_aux_mem_iff at hx,
  have h := hx 1 norm_one.ge,
  rw one_smul at h,
  exact h,
end

lemma balanced_core_aux_balanced {s : set E} (h0 : (0 : E) ∈ balanced_core_aux 𝕜 s):
  balanced 𝕜 (balanced_core_aux 𝕜 s) :=
begin
  intros a ha x hx,
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩,
  by_cases (a = 0),
  { simp[h] at hx,
    rw ←hx,
    exact h0 },
  rw [←hx, balanced_core_aux_mem_iff],
  rw balanced_core_aux_mem_iff at hy,
  intros r hr,
  have h'' : 1 ≤ ∥a⁻¹ • r∥ :=
  begin
    rw smul_eq_mul,
    simp only [norm_mul, norm_inv],
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr,
  end,
  have h' := hy (a⁻¹ • r) h'',
  rw smul_assoc at h',
  exact (mem_inv_smul_set_iff₀ h _ _).mp h',
end

lemma balanced_core_aux_maximal {s t : set E} (h : t ⊆ s) (ht : balanced 𝕜 t) :
  t ⊆ balanced_core_aux 𝕜 s :=
begin
  intros x hx,
  rw balanced_core_aux_mem_iff,
  intros r hr,
  rw mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hr)),
  refine h (balanced_mem ht hx _),
  rw norm_inv,
  exact inv_le_one hr,
end

lemma balanced_core_subset_balanced_core_aux {s : set E} :
  balanced_core 𝕜 s ⊆ balanced_core_aux 𝕜 s :=
balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

lemma balanced_core_eq_Inter {s : set E} (hs : (0 : E) ∈ s) :
  balanced_core 𝕜 s = ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s :=
begin
  rw ←balanced_core_aux,
  refine subset_antisymm balanced_core_subset_balanced_core_aux _,
  refine balanced.subset_core_of_subset (balanced_core_aux_balanced _) (balanced_core_aux_subset s),
  refine mem_of_subset_of_mem balanced_core_subset_balanced_core_aux (balanced_core_zero_mem hs),
end

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

end normed_field

end balanced_hull

/-! ### Topological properties -/

section topology

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

lemma balanced_core_mem_nhds_zero {U : set E} (hU : U ∈ 𝓝 (0 : E)) :
  balanced_core 𝕜 U ∈ 𝓝 (0 : E) :=
begin
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
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
  rw ←filter.exists_mem_subset_iff,
  refine ⟨W, (set_smul_mem_nhds_zero_iff hy').mpr hx.2, _⟩,
  -- It remains to show that `W ⊆ balanced_core 𝕜 U`
  refine subset_balanced_core (mem_of_mem_nhds hU) (λ a ha, _),
  refine set.subset.trans (λ z hz, _) (set.maps_to'.mp h''),
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
end

variables (𝕜 E)

lemma nhds_basis_closed_balanced [regular_space E] : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ 𝓝 (0 : E) ∧ is_closed s ∧ balanced 𝕜 s) id :=
begin
  refine (closed_nhds_basis 0).to_has_basis (λ s hs, _) (λ s hs, ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩),
  refine ⟨balanced_core 𝕜 s, ⟨balanced_core_mem_nhds_zero hs.1, _⟩, balanced_core_subset s⟩,
  refine ⟨balanced_core_is_closed hs.2, balanced_core_balanced s⟩
end

end topology
