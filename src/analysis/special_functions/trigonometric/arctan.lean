/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.complex

/-!
# The `arctan` function.

Inequalities, derivatives,
and `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line.
-/

noncomputable theory

namespace real

open set filter
open_locale topological_space real

lemma tan_add {x y : ℝ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
by simpa only [← complex.of_real_inj, complex.of_real_sub, complex.of_real_add, complex.of_real_div,
              complex.of_real_mul, complex.of_real_tan]
    using @complex.tan_add (x:ℂ) (y:ℂ) (by convert h; norm_cast)

lemma tan_add' {x y : ℝ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
tan_add (or.inl h)

lemma tan_two_mul {x:ℝ} : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) :=
by simpa only [← complex.of_real_inj, complex.of_real_sub, complex.of_real_div, complex.of_real_pow,
              complex.of_real_mul, complex.of_real_tan, complex.of_real_bit0, complex.of_real_one]
    using complex.tan_two_mul

lemma tan_ne_zero_iff {θ : ℝ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 :=
by rw [← complex.of_real_ne_zero, complex.of_real_tan, complex.tan_ne_zero_iff]; norm_cast

lemma tan_eq_zero_iff {θ : ℝ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 :=
by rw [← not_iff_not, not_exists, ← ne, tan_ne_zero_iff]

lemma tan_int_mul_pi_div_two (n : ℤ) : tan (n * π/2) = 0 :=
tan_eq_zero_iff.mpr (by use n)

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
begin
  suffices : continuous_on (λ x, sin x / cos x) {x | cos x ≠ 0},
  { have h_eq : (λ x, sin x / cos x) = tan, by {ext1 x, rw tan_eq_sin_div_cos, },
    rwa h_eq at this, },
  exact continuous_on_sin.div continuous_on_cos (λ x, id),
end

@[continuity]
lemma continuous_tan : continuous (λ x : {x | cos x ≠ 0}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

lemma continuous_on_tan_Ioo : continuous_on tan (Ioo (-(π/2)) (π/2)) :=
begin
  refine continuous_on.mono continuous_on_tan (λ x, _),
  simp only [and_imp, mem_Ioo, mem_set_of_eq, ne.def],
  rw cos_eq_zero_iff,
  rintros hx_gt hx_lt ⟨r, hxr_eq⟩,
  cases le_or_lt 0 r,
  { rw lt_iff_not_ge at hx_lt,
    refine hx_lt _,
    rw [hxr_eq, ← one_mul (π / 2), mul_div_assoc, ge_iff_le, mul_le_mul_right (half_pos pi_pos)],
    simp [h], },
  { rw lt_iff_not_ge at hx_gt,
    refine hx_gt _,
    rw [hxr_eq, ← one_mul (π / 2), mul_div_assoc, ge_iff_le, neg_mul_eq_neg_mul,
      mul_le_mul_right (half_pos pi_pos)],
    have hr_le : r ≤ -1, by rwa [int.lt_iff_add_one_le, ← le_neg_iff_add_nonpos_right] at h,
    rw [← le_sub_iff_add_le, mul_comm, ← le_div_iff],
    { norm_num, rw [← int.cast_one, ← int.cast_neg], norm_cast, exact hr_le, },
    { exact zero_lt_two, }, },
end

lemma surj_on_tan : surj_on tan (Ioo (-(π / 2)) (π / 2)) univ :=
have _ := neg_lt_self pi_div_two_pos,
continuous_on_tan_Ioo.surj_on_of_tendsto (nonempty_Ioo.2 this)
  (by simp [tendsto_tan_neg_pi_div_two, this]) (by simp [tendsto_tan_pi_div_two, this])

lemma tan_surjective : function.surjective tan :=
λ x, surj_on_tan.subset_range trivial

lemma image_tan_Ioo : tan '' (Ioo (-(π / 2)) (π / 2)) = univ :=
univ_subset_iff.1 surj_on_tan

/-- `real.tan` as an `order_iso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tan_order_iso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
(strict_mono_on_tan.order_iso _ _).trans $ (order_iso.set_congr _ _ image_tan_Ioo).trans
  order_iso.set.univ

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot] noncomputable def arctan (x : ℝ) : ℝ :=
tan_order_iso.symm x

@[simp] lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
tan_order_iso.apply_symm_apply x

lemma arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
subtype.coe_prop _

lemma arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
subtype.ext_iff.1 $ tan_order_iso.symm_apply_apply ⟨x, hx₁, hx₂⟩

lemma cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
cos_pos_of_mem_Ioo $ arctan_mem_Ioo x

lemma cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) :=
by rw [one_div, ← inv_one_add_tan_sq (cos_arctan_pos x).ne', tan_arctan]

lemma sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) :=
by rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) :=
by rw [one_div, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
(arctan_mem_Ioo x).2

lemma neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
(arctan_mem_Ioo x).1

lemma arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / sqrt (1 + x ^ 2)) :=
eq.symm $ arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo $ arctan_mem_Ioo x)

lemma arcsin_eq_arctan {x : ℝ} (h : x ∈ Ioo (-(1:ℝ)) 1) :
  arcsin x = arctan (x / sqrt (1 - x ^ 2)) :=
begin
  rw [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div,
      ← sqrt_mul, mul_div_cancel', sub_add_cancel, sqrt_one, div_one];
  nlinarith [h.1, h.2],
end

@[simp] lemma arctan_zero : arctan 0 = 0 :=
by simp [arctan_eq_arcsin]

lemma arctan_eq_of_tan_eq {x y : ℝ} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
  arctan y = x :=
inj_on_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp] lemma arctan_one : arctan 1 = π / 4 :=
arctan_eq_of_tan_eq tan_pi_div_four $ by split; linarith [pi_pos]

@[simp] lemma arctan_neg (x : ℝ) : arctan (-x) = - arctan x :=
by simp [arctan_eq_arcsin, neg_div]

@[continuity]
lemma continuous_arctan : continuous arctan :=
continuous_subtype_coe.comp tan_order_iso.to_homeomorph.continuous_inv_fun

lemma continuous_at_arctan {x : ℝ} : continuous_at arctan x := continuous_arctan.continuous_at

/-- `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tan_local_homeomorph : local_homeomorph ℝ ℝ :=
{ to_fun := tan,
  inv_fun := arctan,
  source := Ioo (-(π / 2)) (π / 2),
  target := univ,
  map_source' := maps_to_univ _ _,
  map_target' := λ y hy, arctan_mem_Ioo y,
  left_inv' := λ x hx, arctan_tan hx.1 hx.2,
  right_inv' := λ y hy, tan_arctan y,
  open_source := is_open_Ioo,
  open_target := is_open_univ,
  continuous_to_fun := continuous_on_tan_Ioo,
  continuous_inv_fun := continuous_arctan.continuous_on }

@[simp] lemma coe_tan_local_homeomorph : ⇑tan_local_homeomorph = tan := rfl
@[simp] lemma coe_tan_local_homeomorph_symm : ⇑tan_local_homeomorph.symm = arctan := rfl

end real
