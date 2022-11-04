/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import group_theory.divisible
import algebra.order.floor
import algebra.order.to_interval_mod
import topology.instances.real

/-!
# The additive circle

We define the additive circle `add_circle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.

See also `circle` and `real.angle`.  For the normed group structure on `add_circle`, see
`add_circle.normed_add_comm_group` in a later file.

## Main definitions:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico 0 p`

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/

noncomputable theory

open set int (hiding mem_zmultiples_iff) add_subgroup topological_space

variables {𝕜 : Type*}

/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[derive [add_comm_group, topological_space, topological_add_group, inhabited, has_coe_t 𝕜],
  nolint unused_arguments]
def add_circle [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p : 𝕜) :=
𝕜 ⧸ zmultiples p

namespace add_circle

section linear_ordered_field

variables [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p q : 𝕜)

@[continuity, nolint unused_arguments] protected lemma continuous_mk' :
  continuous (quotient_add_group.mk' (zmultiples p) : 𝕜 → add_circle p) :=
continuous_coinduced_rng

/-- An auxiliary definition used only for constructing `add_circle.equiv_add_circle`. -/
private def equiv_add_circle_aux (hp : p ≠ 0) : add_circle p →+ add_circle q :=
quotient_add_group.lift _
  ((quotient_add_group.mk' (zmultiples q)).comp $ add_monoid_hom.mul_right (p⁻¹ * q))
  (λ x h, by obtain ⟨z, rfl⟩ := mem_zmultiples_iff.1 h; simp [hp, mul_assoc (z : 𝕜), ← mul_assoc p])

/-- The rescaling equivalence between additive circles with different periods. -/
def equiv_add_circle (hp : p ≠ 0) (hq : q ≠ 0) : add_circle p ≃+ add_circle q :=
{ to_fun := equiv_add_circle_aux p q hp,
  inv_fun := equiv_add_circle_aux q p hq,
  left_inv := by { rintros ⟨x⟩, show quotient_add_group.mk _ = _, congr, field_simp [hp, hq], },
  right_inv := by { rintros ⟨x⟩, show quotient_add_group.mk _ = _, congr, field_simp [hp, hq], },
  .. equiv_add_circle_aux p q hp }

@[simp] lemma equiv_add_circle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  equiv_add_circle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
rfl

@[simp] lemma equiv_add_circle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  (equiv_add_circle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
rfl

variables [floor_ring 𝕜] [hp : fact (0 < p)]
include hp

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equiv_Ico : add_circle p ≃ Ico 0 p :=
{ inv_fun := quotient_add_group.mk' _ ∘ coe,
  to_fun := λ x, ⟨(to_Ico_mod_periodic 0 hp.out).lift x,
    quot.induction_on x $ to_Ico_mod_mem_Ico' hp.out⟩,
  right_inv := by { rintros ⟨x, hx⟩, ext, simp [to_Ico_mod_eq_self, hx.1, hx.2], },
  left_inv :=
  begin
    rintros ⟨x⟩,
    change quotient_add_group.mk (to_Ico_mod 0 hp.out x) = quotient_add_group.mk x,
    rw [quotient_add_group.eq', neg_add_eq_sub, self_sub_to_Ico_mod, zsmul_eq_mul],
    apply int_cast_mul_mem_zmultiples,
  end }

@[simp] lemma coe_equiv_Ico_mk_apply (x : 𝕜) :
  (equiv_Ico p $ quotient_add_group.mk x : 𝕜) = fract (x / p) * p :=
to_Ico_mod_eq_fract_mul _ x

@[continuity] lemma continuous_equiv_Ico_symm : continuous (equiv_Ico p).symm :=
continuous_coinduced_rng.comp continuous_induced_dom

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Icc_eq :
  (coe : 𝕜 → add_circle p) '' (Icc 0 p) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ x, _),
  let y := equiv_Ico p x,
  exact ⟨y, ⟨y.2.1, y.2.2.le⟩, (equiv_Ico p).symm_apply_apply x⟩,
end

instance : divisible_by (add_circle p) ℤ :=
{ div := λ x n, (↑(((n : 𝕜)⁻¹) * (equiv_Ico p x : 𝕜)) : add_circle p),
  div_zero := λ x,
    by simp only [algebra_map.coe_zero, quotient_add_group.coe_zero, inv_zero, zero_mul],
  div_cancel := λ n x hn,
  begin
    replace hn : (n : 𝕜) ≠ 0, { norm_cast, assumption, },
    change n • quotient_add_group.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p x)) = x,
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul],
    exact (equiv_Ico p).symm_apply_apply x,
  end, }

end linear_ordered_field

variables (p : ℝ)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compact_space [fact (0 < p)] : compact_space $ add_circle p :=
begin
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p],
  exact is_compact_Icc.image (add_circle.continuous_mk' p),
end

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples p).opposite ℝ :=
(zmultiples p).properly_discontinuous_vadd_opposite_of_tendsto_cofinite
  (add_subgroup.tendsto_zmultiples_subtype_cofinite p)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is Hausdorff. -/
instance : t2_space (add_circle p) := t2_space_of_properly_discontinuous_vadd_of_t2_space

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is normal. -/
instance [fact (0 < p)] : normal_space (add_circle p) := normal_of_compact_t2

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is second-countable. -/
instance : second_countable_topology (add_circle p) := quotient_add_group.second_countable_topology

end add_circle

private lemma fact_zero_lt_one : fact ((0:ℝ) < 1) := ⟨zero_lt_one⟩
local attribute [instance] fact_zero_lt_one

/-- The unit circle `ℝ ⧸ ℤ`. -/
@[derive [compact_space, normal_space, second_countable_topology]]
abbreviation unit_add_circle := add_circle (1 : ℝ)
