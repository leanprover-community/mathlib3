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


lemma has_strict_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_strict_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_strict_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
begin
  have hx : complex.cos x = 0, by exact_mod_cast hx,
  simp only [← complex.abs_of_real, complex.of_real_tan],
  refine (complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _,
  refine tendsto.inf complex.continuous_of_real.continuous_at _,
  exact tendsto_principal_principal.2 (λ y, mt complex.of_real_inj.1)
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[{(2 * k + 1) * π / 2}ᶜ] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

lemma continuous_at_tan {x : ℝ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

lemma differentiable_at_tan {x : ℝ} : differentiable_at ℝ tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℝ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℝ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, sq]
else (has_deriv_at_tan h).deriv

@[simp] lemma times_cont_diff_at_tan {n x} : times_cont_diff_at ℝ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  λ h, (complex.times_cont_diff_at_tan.2 $ by exact_mod_cast h).real_of_complex⟩

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
λ x hx, (continuous_at_tan.2 hx).continuous_within_at

@[continuity]
lemma continuous_tan : continuous (λ x : {x | cos x ≠ 0}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

lemma has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  has_deriv_at tan (1 / (cos x)^2) x :=
has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

lemma differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  differentiable_at ℝ tan x :=
(has_deriv_at_tan_of_mem_Ioo h).differentiable_at

lemma continuous_on_tan_Ioo : continuous_on tan (Ioo (-(π/2)) (π/2)) :=
λ x hx, (differentiable_at_tan_of_mem_Ioo hx).continuous_at.continuous_within_at

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
(strict_mono_incr_on_tan.order_iso _ _).trans $ (order_iso.set_congr _ _ image_tan_Ioo).trans
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
  rw [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div_eq_div_mul,
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

lemma has_strict_deriv_at_arctan (x : ℝ) : has_strict_deriv_at arctan (1 / (1 + x^2)) x :=
have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
by simpa [cos_sq_arctan]
  using tan_local_homeomorph.has_strict_deriv_at_symm trivial (by simpa) (has_strict_deriv_at_tan A)

lemma has_deriv_at_arctan (x : ℝ) : has_deriv_at arctan (1 / (1 + x^2)) x :=
(has_strict_deriv_at_arctan x).has_deriv_at

lemma differentiable_at_arctan (x : ℝ) : differentiable_at ℝ arctan x :=
(has_deriv_at_arctan x).differentiable_at

lemma differentiable_arctan : differentiable ℝ arctan := differentiable_at_arctan

@[simp] lemma deriv_arctan : deriv arctan = (λ x, 1 / (1 + x^2)) :=
funext $ λ x, (has_deriv_at_arctan x).deriv

lemma times_cont_diff_arctan {n : with_top ℕ} : times_cont_diff ℝ n arctan :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x,
have cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
tan_local_homeomorph.times_cont_diff_at_symm_deriv (by simpa) trivial (has_deriv_at_tan this)
  (times_cont_diff_at_tan.2 this)

end real

section
/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/

open real

section deriv

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_strict_deriv_at.arctan (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') x :=
(real.has_strict_deriv_at_arctan (f x)).comp x hf

lemma has_deriv_at.arctan (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') x :=
(real.has_deriv_at_arctan (f x)).comp x hf

lemma has_deriv_within_at.arctan (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') s x :=
(real.has_deriv_at_arctan (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) * (deriv_within f s x) :=
hf.has_deriv_within_at.arctan.deriv_within hxs

@[simp] lemma deriv_arctan (hc : differentiable_at ℝ f x) :
  deriv (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) * (deriv f x) :=
hc.has_deriv_at.arctan.deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : set E} {n : with_top ℕ}

lemma has_strict_fderiv_at.arctan (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') x :=
(has_strict_deriv_at_arctan (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.arctan (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.arctan (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') s x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_within_at x hf

lemma fderiv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.arctan.fderiv_within hxs

@[simp] lemma fderiv_arctan (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) • (fderiv ℝ f x) :=
hc.has_fderiv_at.arctan.fderiv

lemma differentiable_within_at.arctan (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.arctan (f x)) s x :=
hf.has_fderiv_within_at.arctan.differentiable_within_at

@[simp] lemma differentiable_at.arctan (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ x, arctan (f x)) x :=
hc.has_fderiv_at.arctan.differentiable_at

lemma differentiable_on.arctan (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ x, arctan (f x)) s :=
λ x h, (hc x h).arctan

@[simp] lemma differentiable.arctan (hc : differentiable ℝ f) :
  differentiable ℝ (λ x, arctan (f x)) :=
λ x, (hc x).arctan

lemma times_cont_diff_at.arctan (h : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, arctan (f x)) x :=
times_cont_diff_arctan.times_cont_diff_at.comp x h

lemma times_cont_diff.arctan (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, arctan (f x)) :=
times_cont_diff_arctan.comp h

lemma times_cont_diff_within_at.arctan (h : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, arctan (f x)) s x :=
times_cont_diff_arctan.comp_times_cont_diff_within_at h

lemma times_cont_diff_on.arctan (h : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, arctan (f x)) s :=
times_cont_diff_arctan.comp_times_cont_diff_on h

end fderiv
end
