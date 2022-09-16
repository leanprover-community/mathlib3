/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.algebra.const_mul_action
import topology.instances.real
import tactic.linear_combination

/-!
# The topology on the quotient group `ℝ / a ℤ`

-/

open add_subgroup

section move_to_group_theory_subgroup_basic

lemma add_monoid_hom.coe_comp_range_restrict {G : Type*} [add_group G] {N : Type*} [add_group N]
  (f : G →+ N) :
  (coe : f.range → N) ∘ (⇑(f.range_restrict) : G → f.range) = f :=
begin
  ext g,
  exact f.coe_range_restrict g,
end

lemma add_monoid_hom.subtype_comp_range_restrict {G : Type*} [add_group G] {N : Type*} [add_group N]
  (f : G →+ N) :
  f.range.subtype.comp (f.range_restrict) = f :=
begin
  ext g,
  exact f.coe_range_restrict g,
end

end move_to_group_theory_subgroup_basic

section move_to_topology_subset_properties

lemma set.surj_on.compact_space {X : Type*} [topological_space X] {s : set X} (hs : is_compact s)
  {Y : Type*} [topological_space Y] {f : X → Y} (hf : continuous f)
  (hf' : set.surj_on f s set.univ) :
  compact_space Y :=
is_compact_univ_iff.mp
begin
  convert ← hs.image hf,
  rw ← set.univ_subset_iff,
  exact hf',
end

end move_to_topology_subset_properties

section move_to_topology_algebra_monoid

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right {R : Type*} [monoid R] [topological_space R]
  [has_continuous_mul R] {a : R} {b : R} (ha : a * b = 1) :
  filter.tendsto (λ x : R, x * a) (filter.cocompact R) (filter.cocompact R) :=
begin
  refine filter.tendsto.of_tendsto_comp _ (filter.comap_cocompact_le (continuous_mul_right b)),
  convert filter.tendsto_id,
  ext x,
  simp [ha],
end

end move_to_topology_algebra_monoid

section move_to_topology_algebra_field

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right₀ {R : Type*} [division_ring R] [topological_space R]
  [has_continuous_mul R] {a : R} (ha : a ≠ 0) :
  filter.tendsto (λ x : R, x * a) (filter.cocompact R) (filter.cocompact R) :=
filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)

end move_to_topology_algebra_field

section move_to_topology_metric_space_basic

/-- For nonzero `a`, the "multiples of `a`" map `zmultiples_hom` from `ℤ` to `ℝ` is discrete, i.e.
inverse images of compact sets are finite. -/
lemma int.tendsto_zmultiples_hom_cofinite {a : ℝ} (ha : a ≠ 0) :
  filter.tendsto (zmultiples_hom ℝ a) filter.cofinite (filter.cocompact ℝ) :=
begin
  convert (filter.tendsto_cocompact_mul_right₀ ha).comp int.tendsto_coe_cofinite,
  ext n,
  simp,
end

/-- The coercion into `ℝ` from its subtype "multiples of `a`" (`zmultiples a`) is discrete, i.e.
inverse images of compact sets are finite. -/
lemma int.tendsto_coe_zmultiples_cofinite (a : ℝ) :
  filter.tendsto (coe : zmultiples a → ℝ) filter.cofinite (filter.cocompact ℝ) :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { rw add_subgroup.zmultiples_zero_eq_bot,
    intros K hK,
    rw [filter.mem_map, filter.mem_cofinite],
    apply set.to_finite },
  intros K hK,
  have H := int.tendsto_zmultiples_hom_cofinite ha hK,
  simp only [filter.mem_map, filter.mem_cofinite, ← set.preimage_compl] at ⊢ H,
  rw [← (zmultiples_hom ℝ a).range_restrict_surjective.image_preimage (coe ⁻¹' Kᶜ),
    ← set.preimage_comp, ← add_monoid_hom.coe_comp_range_restrict],
  exact set.finite.image _ H,
end

end move_to_topology_metric_space_basic

variables {a : ℝ}

instance : has_continuous_const_vadd (zmultiples a).opposite ℝ :=
sorry
-- follows by `to_additive` of `smul_comm_class.has_continuous_const_smul`

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples a` (the multiples of
`a:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples a).opposite ℝ :=
{ finite_disjoint_inter_image := begin
    intros K L hK hL,
    have H : set.finite _ := int.tendsto_coe_zmultiples_cofinite
      a ((hL.prod hK).image continuous_sub).compl_mem_cocompact,
    convert H,
    ext x,
    rcases x with ⟨(x:ℝ) , (hx : x ∈ zmultiples a)⟩,
    change (_ ≠ ∅) ↔ _,
    simp only [set.image_vadd, set.image_prod, set.image2_sub, compl_compl, set.mem_preimage,
      coe_mk, set.ne_empty_iff_nonempty, set.preimage_compl],
    congrm (∃ ℓ, _),
    simp only [set.mem_inter_eq, coe_mk, exists_and_distrib_left],
    rw and_comm,
    congrm _ ∧ (∃ k, _ ∧ _),
    change (k + x = ℓ) ↔ _,
    split; intros hh; linear_combination - hh,
  end }

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is Hausdorff. -/
instance : t2_space (ℝ ⧸ zmultiples a) := t2_space_of_properly_discontinuous_vadd_of_t2_space

variables [fact (0 < a)]

local notation `π` := quotient_add_group.mk' (zmultiples a)

/-- Under the map from `ℝ` to its quotient by `zmultiples a` (the multiples of `a:ℝ`), the image of
the interval [0, a) is the whole quotient. -/
lemma real.surj_on_quotient_Ico : set.surj_on π (set.Ico 0 a) set.univ :=
begin
  rintros x₀ -,
  apply @quotient.induction_on ℝ (quotient_add_group.left_rel (zmultiples a))
    (λ x, x ∈ quotient.mk' '' set.Ico 0 a),
  intros x,
  obtain ⟨k, hk, -⟩ := exists_unique_add_zsmul_mem_Ico (fact.out _ : 0 < a) x 0,
  refine ⟨x + k • a, _, _⟩,
  { simpa using hk },
  refine quotient_add_group.eq'.mpr _,
  use - k,
  simp,
  push_cast,
  ring,
end

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is compact. -/
instance : compact_space (ℝ ⧸ zmultiples a) :=
(real.surj_on_quotient_Ico.mono set.Ico_subset_Icc_self (set.subset.refl _)).compact_space
  is_compact_Icc
  continuous_quotient_mk

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is normal. -/
instance : normal_space (ℝ ⧸ zmultiples a) := normal_of_compact_t2
