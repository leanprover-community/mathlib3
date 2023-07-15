/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm

/-! # The left-regular representation is an isometry for C⋆-algebras 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

open continuous_linear_map

local postfix `⋆`:std.prec.max_plus := star

variables (𝕜 : Type*) {E : Type*}
variables [densely_normed_field 𝕜] [non_unital_normed_ring E] [star_ring E] [cstar_ring E]
variables [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E] (a : E)

/-- In a C⋆-algebra `E`, either unital or non-unital, multiplication on the left by `a : E` has
norm equal to the norm of `a`. -/
@[simp] lemma op_nnnorm_mul : ‖mul 𝕜 E a‖₊ = ‖a‖₊ :=
begin
  rw ←Sup_closed_unit_ball_eq_nnnorm,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ (λ r hr, _),
  { exact (metric.nonempty_closed_ball.mpr zero_le_one).image _ },
  { rintro - ⟨x, hx, rfl⟩,
    exact ((mul 𝕜 E a).unit_le_op_norm x $ mem_closed_ball_zero_iff.mp hx).trans
      (op_norm_mul_apply_le 𝕜 E a) },
  { have ha : 0 < ‖a‖₊ := zero_le'.trans_lt hr,
    rw [←inv_inv (‖a‖₊), nnreal.lt_inv_iff_mul_lt (inv_ne_zero ha.ne')] at hr,
    obtain ⟨k, hk₁, hk₂⟩ := normed_field.exists_lt_nnnorm_lt 𝕜 (mul_lt_mul_of_pos_right hr $
      inv_pos.2 ha),
    refine ⟨_, ⟨k • star a, _, rfl⟩, _⟩,
    { simpa only [mem_closed_ball_zero_iff, norm_smul, one_mul, norm_star] using
        (nnreal.le_inv_iff_mul_le ha.ne').1 (one_mul ‖a‖₊⁻¹ ▸ hk₂.le : ‖k‖₊ ≤ ‖a‖₊⁻¹) },
    { simp only [map_smul, nnnorm_smul, mul_apply', mul_smul_comm, cstar_ring.nnnorm_self_mul_star],
      rwa [←nnreal.div_lt_iff (mul_pos ha ha).ne', div_eq_mul_inv, mul_inv, ←mul_assoc] } },
end

/-- In a C⋆-algebra `E`, either unital or non-unital, multiplication on the right by `a : E` has
norm eqaul to the norm of `a`. -/
@[simp] lemma op_nnnorm_mul_flip : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊ :=
begin
  rw [←Sup_unit_ball_eq_nnnorm, ←nnnorm_star, ←@op_nnnorm_mul 𝕜 E, ←Sup_unit_ball_eq_nnnorm],
  congr' 1,
  simp only [mul_apply', flip_apply],
  refine set.subset.antisymm _ _;
  rintro - ⟨b, hb, rfl⟩;
  refine ⟨star b, by simpa only [norm_star, mem_ball_zero_iff] using hb, _⟩,
  { simp only [←star_mul, nnnorm_star] },
  { simpa using (nnnorm_star (star b * a)).symm }
end

variables (E)

/-- In a C⋆-algebra `E`, either unital or non-unital, the left regular representation is an
isometry. -/
lemma mul_isometry : isometry (mul 𝕜 E) :=
add_monoid_hom_class.isometry_of_norm _ (λ a, congr_arg coe $ op_nnnorm_mul 𝕜 a)

/-- In a C⋆-algebra `E`, either unital or non-unital, the right regular anti-representation is an
isometry. -/
lemma mul_flip_isometry : isometry (mul 𝕜 E).flip :=
add_monoid_hom_class.isometry_of_norm _ (λ a, congr_arg coe $ op_nnnorm_mul_flip 𝕜 a)
