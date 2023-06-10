/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.arctan
import analysis.special_functions.trigonometric.complex_deriv

/-!
# Derivatives of the `tan` and `arctan` functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Continuity and derivatives of the tangent and arctangent functions.
-/

noncomputable theory

namespace real

open set filter
open_locale topology real

lemma has_strict_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_strict_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_strict_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[≠] x) at_top :=
begin
  have hx : complex.cos x = 0, by exact_mod_cast hx,
  simp only [← complex.abs_of_real, complex.of_real_tan],
  refine (complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _,
  refine tendsto.inf complex.continuous_of_real.continuous_at _,
  exact tendsto_principal_principal.2 (λ y, mt complex.of_real_inj.1)
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) at_top :=
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

@[simp] lemma cont_diff_at_tan {n x} : cont_diff_at ℝ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  λ h, (complex.cont_diff_at_tan.2 $ by exact_mod_cast h).real_of_complex⟩

lemma has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  has_deriv_at tan (1 / (cos x)^2) x :=
has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

lemma differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  differentiable_at ℝ tan x :=
(has_deriv_at_tan_of_mem_Ioo h).differentiable_at

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

lemma cont_diff_arctan {n : ℕ∞} : cont_diff ℝ n arctan :=
cont_diff_iff_cont_diff_at.2 $ λ x,
have cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
tan_local_homeomorph.cont_diff_at_symm_deriv (by simpa) trivial (has_deriv_at_tan this)
  (cont_diff_at_tan.2 this)

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

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E} {n : ℕ∞}

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

lemma cont_diff_at.arctan (h : cont_diff_at ℝ n f x) :
  cont_diff_at ℝ n (λ x, arctan (f x)) x :=
cont_diff_arctan.cont_diff_at.comp x h

lemma cont_diff.arctan (h : cont_diff ℝ n f) :
  cont_diff ℝ n (λ x, arctan (f x)) :=
cont_diff_arctan.comp h

lemma cont_diff_within_at.arctan (h : cont_diff_within_at ℝ n f s x) :
  cont_diff_within_at ℝ n (λ x, arctan (f x)) s x :=
cont_diff_arctan.comp_cont_diff_within_at h

lemma cont_diff_on.arctan (h : cont_diff_on ℝ n f s) :
  cont_diff_on ℝ n (λ x, arctan (f x)) s :=
cont_diff_arctan.comp_cont_diff_on h

end fderiv
end
