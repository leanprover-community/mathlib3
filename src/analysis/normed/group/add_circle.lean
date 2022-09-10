/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.order.floor
import algebra.order.to_interval_mod
import analysis.normed.group.quotient

/-!
# The additive circle

We define the additive circle `add_circle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.
Note that when `𝕜 = ℝ`, this is naturally a normed group; for example if `p = 1` then:
`∥(x : add_circle 1)∥ = |x - round x|` for any `x : ℝ` (see `unit_add_circle.norm_eq`).

See also `circle` and `real.angle`.

## Main definitions:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico 0 p`
 * `add_circle.norm_eq`: a characterisation of the norm on `add_circle p`

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Measure space structure
 * Lie group structure
 * Exponential equivalence to `circle`
 * The fact `inner_product_geometry.angle (real.cos θ) (real.sin θ) = ∥(θ : real.angle)∥`

-/

noncomputable theory

open set int (hiding mem_zmultiples_iff) add_subgroup

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

variables [floor_ring 𝕜]

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equiv_Ico (hp : 0 < p) : add_circle p ≃ Ico 0 p :=
{ inv_fun := quotient_add_group.mk' _ ∘ coe,
  to_fun := λ x, ⟨(to_Ico_mod_periodic 0 hp).lift x, quot.induction_on x $ to_Ico_mod_mem_Ico' hp⟩,
  right_inv := by { rintros ⟨x, hx⟩, ext, simp [to_Ico_mod_eq_self, hx.1, hx.2], },
  left_inv :=
  begin
    rintros ⟨x⟩,
    change quotient_add_group.mk (to_Ico_mod 0 hp x) = quotient_add_group.mk x,
    rw [quotient_add_group.eq', neg_add_eq_sub, self_sub_to_Ico_mod, zsmul_eq_mul],
    apply int_cast_mul_mem_zmultiples,
  end }

@[simp] lemma coe_equiv_Ico_mk_apply (hp : 0 < p) (x : 𝕜) :
  (equiv_Ico p hp $ quotient_add_group.mk x : 𝕜) = fract (x / p) * p :=
to_Ico_mod_eq_fract_mul hp x

@[continuity] lemma continuous_equiv_Ico_symm (hp : 0 < p) : continuous (equiv_Ico p hp).symm :=
continuous_coinduced_rng.comp continuous_induced_dom

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Icc_eq (hp : 0 < p) :
  (coe : 𝕜 → add_circle p) '' (Icc 0 p) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ x, _),
  let y := equiv_Ico p hp x,
  exact ⟨y, ⟨y.2.1, y.2.2.le⟩, (equiv_Ico p hp).symm_apply_apply x⟩,
end

end linear_ordered_field

section real

variables (p : ℝ)

instance : normed_add_comm_group (add_circle p) := add_subgroup.normed_add_comm_group_quotient _

lemma compact_space (hp : 0 < p) : compact_space $ add_circle p :=
begin
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p hp],
  exact is_compact_Icc.image (add_circle.continuous_mk' p),
end

@[simp] lemma norm_coe_mul (x : ℝ) (t : ℝ) :
  ∥(↑(t * x) : add_circle (t * p))∥ = |t| * ∥(x : add_circle p)∥ :=
begin
  have aux : ∀ {a b c : ℝ}, a ∈ zmultiples b → c * a ∈ zmultiples (c * b) := λ a b c h, by
  { simp only [mem_zmultiples_iff] at ⊢ h,
    obtain ⟨n, rfl⟩ := h,
    exact ⟨n, (mul_smul_comm n c b).symm⟩, },
  rcases eq_or_ne t 0 with rfl | ht, { simp, },
  have ht' : |t| ≠ 0 := (not_congr abs_eq_zero).mpr ht,
  simp only [quotient_norm_eq, real.norm_eq_abs],
  conv_rhs { rw [← smul_eq_mul, ← real.Inf_smul_of_nonneg (abs_nonneg t)], },
  simp only [quotient_add_group.mk'_apply, quotient_add_group.eq_iff_sub_mem],
  congr' 1,
  ext z,
  rw mem_smul_set_iff_inv_smul_mem₀ ht',
  show (∃ y, y - t * x ∈ zmultiples (t * p) ∧ |y| = z) ↔ ∃w, w - x ∈ zmultiples p ∧ |w| = |t|⁻¹ * z,
  split,
  { rintros ⟨y, hy, rfl⟩,
    refine ⟨t⁻¹ * y, _, by rw [abs_mul, abs_inv]⟩,
    rw [← inv_mul_cancel_left₀ ht x, ← inv_mul_cancel_left₀ ht p, ← mul_sub],
    exact aux hy, },
  { rintros ⟨w, hw, hw'⟩,
    refine ⟨t * w, _, by rw [← (eq_inv_mul_iff_mul_eq₀ ht').mp hw', abs_mul]⟩,
    rw ← mul_sub,
    exact aux hw, },
end

@[simp] lemma norm_eq_of_zero {x : ℝ} : ∥(x : add_circle (0 : ℝ))∥ = |x| :=
begin
  suffices : {y : ℝ | (y : add_circle (0 : ℝ)) = (x : add_circle (0 : ℝ)) } = { x },
  { rw [quotient_norm_eq, this, image_singleton, real.norm_eq_abs, cInf_singleton], },
  ext y,
  simp [quotient_add_group.eq_iff_sub_mem, mem_zmultiples_iff, sub_eq_zero],
end

lemma norm_eq {x : ℝ} : ∥(x : add_circle p)∥ = |x - round (p⁻¹ * x) * p| :=
begin
  suffices : ∀ (x : ℝ), ∥(x : add_circle (1 : ℝ))∥ = |x - round x|,
  { rcases eq_or_ne p 0 with rfl | hp, { simp, },
    intros,
    have hx := norm_coe_mul p x p⁻¹,
    rw [abs_inv, eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx,
    rw [← hx, inv_mul_cancel hp, this, ← abs_mul, mul_sub, mul_inv_cancel_left₀ hp, mul_comm p], },
  clear x p,
  intros,
  rw [quotient_norm_eq, abs_sub_round_eq_min],
  have h₁ : bdd_below (abs '' {m : ℝ | (m : add_circle (1 : ℝ)) = x}) :=
    ⟨0, by simp [mem_lower_bounds]⟩,
  have h₂ : (abs '' {m : ℝ | (m : add_circle (1 : ℝ)) = x}).nonempty := ⟨|x|, ⟨x, rfl, rfl⟩⟩,
  apply le_antisymm,
  { simp only [le_min_iff, real.norm_eq_abs, cInf_le_iff h₁ h₂],
    intros b h,
    refine ⟨mem_lower_bounds.1 h _ ⟨fract x, _, abs_fract⟩,
            mem_lower_bounds.1 h _ ⟨fract x - 1, _, by rw [abs_sub_comm, abs_one_sub_fract]⟩⟩,
    { simp only [mem_set_of_eq, fract, sub_eq_self, quotient_add_group.coe_sub,
        quotient_add_group.eq_zero_iff, int_cast_mem_zmultiples_one], },
    { simp only [mem_set_of_eq, fract, sub_eq_self, quotient_add_group.coe_sub,
        quotient_add_group.eq_zero_iff, int_cast_mem_zmultiples_one, sub_sub,
        (by norm_cast : (⌊x⌋ : ℝ) + 1 = (↑(⌊x⌋ + 1) : ℝ))], }, },
  { simp only [quotient_add_group.mk'_apply, real.norm_eq_abs, le_cInf_iff h₁ h₂],
    rintros b' ⟨b, hb, rfl⟩,
    simp only [mem_set_of_eq, quotient_add_group.eq_iff_sub_mem, mem_zmultiples_iff,
      smul_one_eq_coe] at hb,
    obtain ⟨z, hz⟩ := hb,
    rw [(by { rw hz, abel, } : x = b - z), fract_sub_int, ← abs_sub_round_eq_min],
    exact abs_sub_round_le_abs_self _, },
end

end real

end add_circle

/-- The unit circle `ℝ ⧸ ℤ`. -/
abbreviation unit_add_circle := add_circle (1 : ℝ)

namespace unit_add_circle

instance : compact_space unit_add_circle := add_circle.compact_space _ zero_lt_one

lemma norm_eq {x : ℝ} : ∥(x : unit_add_circle)∥ = |x - round x| := by simp [add_circle.norm_eq]

end unit_add_circle
