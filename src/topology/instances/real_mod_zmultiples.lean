/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.algebra.const_mul_action
import topology.instances.real

/-!
# The topology on the quotient group `ℝ / a ℤ`
-/

open add_subgroup

variables {a : ℝ} --[fact (0 < a)]

instance : has_continuous_const_vadd (zmultiples a).opposite ℝ :=
sorry
-- follows by `to_additive` of `smul_comm_class.has_continuous_const_smul`

-- move to `group_theory.subgroup.basic` and `to_additive` it
@[simp] lemma add_subgroup.zmultiples_zero {G : Type*} [add_group G] : zmultiples (0:G) = ⊥ :=
begin
  sorry,
end

-- move to `topology.metric_space.basic`

/-- For nonzero `a`, under the "multiples of `a`" map from `ℤ` to `ℝ`, inverse images of compact
sets are finite. -/
lemma int.tendsto_zmultiples_hom_cofinite {a : ℝ} (ha : a ≠ 0) :
  filter.tendsto (zmultiples_hom ℝ a) filter.cofinite (filter.cocompact ℝ) :=
begin
  refine tendsto_cocompact_of_tendsto_dist_comp_at_top (0 : ℝ) _,
  simp only [filter.tendsto_at_top, filter.eventually_cofinite, not_le, ← metric.mem_ball],
  change ∀ r : ℝ, ((λ n : ℤ, n • a) ⁻¹' (metric.ball (0 : ℝ) r)).finite,
  simp [real.ball_eq_Ioo, set.finite_Ioo],
end


-- this is the version we actually use
lemma int.tendsto_zmultiples_hom_cofinite' (a : ℝ) :
  filter.tendsto (coe : zmultiples a → ℝ) filter.cofinite (filter.cocompact ℝ) :=
sorry

-- move to `topology.metric_space.basic`

lemma is_compact.finite_inter_zmultiples (a : ℝ) {s : set ℝ} (hs : is_compact s) :
  ((coe : zmultiples a → ℝ) ⁻¹' s).finite :=
begin
  by_cases ha : a = 0,
  { sorry }, --exact set.finite.inter_of_left (by simp [ha]) s },
  convert (int.tendsto_zmultiples_hom_cofinite ha hs.compl_mem_cocompact).image (zmultiples_hom ℝ a),
  dsimp,
  rw [compl_compl,  set.image_preimage_eq_inter_range, set.inter_comm, ← range_zmultiples_hom],
  refl,
end

lemma is_compact.finite_inter_zmultiples' (a : ℝ) {s : set ℝ} (hs : is_compact s) :
  ((zmultiples a : set ℝ) ∩ s).finite :=
begin
  by_cases ha : a = 0,
  { exact set.finite.inter_of_left (by simp [ha]) s },
  convert (int.tendsto_zmultiples_hom_cofinite ha hs.compl_mem_cocompact).image (zmultiples_hom ℝ a),
  dsimp,
  rw [compl_compl,  set.image_preimage_eq_inter_range, set.inter_comm, ← range_zmultiples_hom],
  refl,
end

-- **


instance : properly_discontinuous_vadd (zmultiples a).opposite ℝ :=
{ finite_disjoint_inter_image := begin
    intros K L hK hL,
    have H : set.finite _ := int.tendsto_zmultiples_hom_cofinite'
      a ((hL.prod hK).image continuous_sub).compl_mem_cocompact,
    convert H,
    ext x,
    cases x with x hx,
    change add_opposite.unop x ∈ zmultiples a at hx,
    change (_ ≠ ∅) ↔ _,
    simp only [set.image_vadd, set.image_prod, set.image2_sub, compl_compl, set.mem_preimage,
      coe_mk],
    sorry,
  end }

instance : t2_space (ℝ ⧸ zmultiples a) := t2_space_of_properly_discontinuous_vadd_of_t2_space

-- check, remove later
example : topological_add_group (ℝ ⧸ zmultiples a) := by apply_instance

variables [fact (0 < a)]

lemma is_compact.compact_space {X : Type*} [topological_space X] {s : set X} (hs : is_compact s)
  {Y : Type*} [topological_space Y] {f : X → Y} (hf : continuous f)
  (hf' : set.surj_on f s set.univ) :
  compact_space Y :=
{ compact_univ := begin
    convert hs.image hf,
    symmetry,
    rw ← set.univ_subset_iff,
    exact hf',
  end }

local notation `π` := quotient_add_group.mk' (zmultiples a)

lemma baz₁ : set.surj_on π (set.Ico 0 a) set.univ :=
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

lemma baz₂ : set.surj_on π (set.Ioc 0 a) set.univ :=
begin
  sorry
end

instance : compact_space (ℝ ⧸ zmultiples a) :=
is_compact_Icc.compact_space continuous_quotient_mk $
  baz₁.mono set.Ico_subset_Icc_self (set.subset.refl _)

instance : normal_space (ℝ ⧸ zmultiples a) := normal_of_compact_t2
