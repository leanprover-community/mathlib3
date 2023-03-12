import topology.algebra.group_with_zero
import to_mathlib.algebra.group_with_zero.units.basic
import to_mathlib.algebra.big_operators.basic

instance {α : Type*} [has_zero α] [has_mul α] [has_inv α] [topological_space α]
  [has_continuous_inv₀ α] : has_continuous_inv₀ αᵐᵒᵖ :=
⟨λ x hx, begin
  refine (mul_opposite.continuous_op.continuous_at).comp
    (mul_opposite.continuous_unop.continuous_at.inv₀ _),
  simp [hx]
end⟩

open filter set function finset
open_locale filter topology big_operators

lemma finset.prod_surj_units {M β : Type*} [comm_monoid M] [decidable_pred (is_unit : M → Prop)]
  (s : finset β) (f : β → M) (hf : ∀ i ∈ s, is_unit (f i)) :
  ∏ i in s, surj_units (f i) = surj_units (∏ i in s, f i) :=
begin
  ext,
  rw [surj_units_apply_is_unit (is_unit_prod _ _ hf), is_unit.unit_spec, units.coe_prod],
  refine prod_congr rfl (λ i hi, _),
  simp [surj_units_apply_is_unit (hf _ hi)]
end

lemma continuous_on_surj_units {G₀ : Type*} [group_with_zero G₀]
  [topological_space G₀] [has_continuous_inv₀ G₀] [decidable_pred (is_unit : G₀ → Prop)] :
  continuous_on surj_units ({x : G₀ | is_unit x}) :=
begin
  intros x hx U,
  simp only [filter.mem_map, nhds_induced],
  simp only [units.embed_product_apply, units.coe_inv, mul_opposite.op_inv,
             mem_comap, exists_prop, forall_exists_index, and_imp, mem_nhds_prod_iff],
  intros V s hs t ht hst hVU,
  rw [surj_units_apply_is_unit hx, is_unit.unit_spec] at hs ht,
  refine mem_of_superset _ (set.preimage_mono hVU),
  rw set.preimage_preimage,
  rw [←mul_opposite.op_inv] at ht,
  have hne : mul_opposite.op x ≠ 0,
  { simpa [is_unit_iff_ne_zero] using hx },
  have ht' := (mul_opposite.continuous_op.tendsto _).inv₀ hne ht,
  rw filter.mem_map at ht',
  rw [nhds_within, mem_inf_iff_superset],
  refine ⟨_, inter_mem hs ht', _, mem_principal_self _, _⟩,
  intros y,
  simp only [set.mem_inter_iff, set.mem_preimage, set.mem_set_of_eq, units.embed_product_apply,
             units.coe_inv, mul_opposite.op_inv, and_imp],
  intros hxs hxt hy,
  simp_rw [surj_units_apply_is_unit hy, is_unit.unit_spec],
  refine hst _,
  simp [hxs, hxt]
end

lemma tendsto_surj_units_of_ne_zero {G₀ : Type*} [group_with_zero G₀] [topological_space G₀]
  [t1_space G₀] [has_continuous_inv₀ G₀] [decidable_pred (is_unit : G₀ → Prop)]
  (y : G₀) (hy : y ≠ 0) :
  tendsto surj_units (𝓝 y) (𝓝 (surj_units y)) :=
begin
  refine (((continuous_on_surj_units) y (is_unit_iff_ne_zero.mpr hy)).tendsto).comp _,
  refine tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_id _,
  rw eventually_nhds_iff,
  refine ⟨set.univ \ {0}, _, is_open_univ.sdiff is_closed_singleton, _⟩,
  { simp [is_unit_iff_ne_zero] },
  { simp [hy] }
end

lemma coe_surj_units_nonneg {R : Type*} [linear_ordered_field R]
  [decidable_pred (is_unit : R → Prop)] {x : R} (hx : 0 ≤ x) : (0 : R) ≤ surj_units x :=
begin
  rcases hx.eq_or_lt with rfl|hx',
  { simp, },
  { simp [coe_surj_units_apply_ne_zero hx'.ne', hx] }
end

lemma coe_surj_units_pos {R : Type*} [linear_ordered_field R]
  [decidable_pred (is_unit : R → Prop)] {x : R} (hx : 0 < x) : (0 : R) < surj_units x :=
by simp [coe_surj_units_apply_ne_zero hx.ne', hx]

-- lemma tendsto_surj_units {G₀ : Type*} [group_with_zero G₀]
--   [topological_space G₀] [has_continuous_inv₀ G₀] (x : G₀) [decidable_pred (is_unit : G₀ → Prop)] :
--   tendsto (λ x, surj_units x) (𝓝 x) (𝓝 (surj_units x)) :=
-- begin
--   classical,
--   intros z,
--   simp only [filter.mem_map, nhds_induced],
--   simp only [units.embed_product_apply, units.coe_inv, mul_opposite.op_inv,
--              filter.mem_comap, exists_prop,
--              forall_exists_index, and_imp, mem_nhds_prod_iff],
--   intros V s hs t ht hst hVU,
--   by_cases hx : is_unit x,
--   rw [surj_units_apply_is_unit hx, is_unit.unit_spec] at hs ht,
--   refine filter.mem_of_superset _ (set.preimage_mono hVU),
--   rw set.preimage_preimage,
--   rw [←mul_opposite.op_inv] at ht,
--   have hne : mul_opposite.op x ≠ 0,
--   { simpa [is_unit_iff_ne_zero] using hx },
--   have ht' := (mul_opposite.continuous_op.tendsto _).inv₀ hne ht,
--   rw filter.mem_map at ht',
--   refine mem_of_superset (filter.inter_mem hs ht') _,
--   intros y,
--   simp only [set.mem_inter_iff, set.mem_preimage, set.mem_set_of_eq, units.embed_product_apply,
--              units.coe_inv, mul_opposite.op_inv, and_imp],
--   intros hxs hxt,
--   by_cases hy : is_unit y,
--   { simp_rw [surj_units_apply_is_unit hy, is_unit.unit_spec],
--     refine hst _,
--     simp [hxs, hxt] },
--   { simp only [surj_units_apply_not_is_unit hy, units.coe_one, mul_opposite.op_one, inv_one], },
-- end
