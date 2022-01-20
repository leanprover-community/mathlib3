/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.complex
import analysis.special_functions.trigonometric.deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/

noncomputable theory

namespace complex

open set filter
open_locale real

lemma has_strict_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) :
  has_strict_deriv_at tan (1 / (cos x)^2) x :=
begin
  convert (has_strict_deriv_at_sin x).div (has_strict_deriv_at_cos x) h,
  rw ← sin_sq_add_cos_sq x,
  ring,
end

lemma has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
(has_strict_deriv_at_tan h).has_deriv_at

open_locale topological_space

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[≠] x) at_top :=
begin
  simp only [tan_eq_sin_div_cos, ← norm_eq_abs, normed_field.norm_div],
  have A : sin x ≠ 0 := λ h, by simpa [*, sq] using sin_sq_add_cos_sq x,
  have B : tendsto cos (𝓝[≠] (x)) (𝓝[≠] 0),
    from hx ▸ (has_deriv_at_cos x).tendsto_punctured_nhds (neg_ne_zero.2 A),
  exact continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A)
    (tendsto_norm_nhds_within_zero.comp B).inv_tendsto_zero,
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp] lemma continuous_at_tan {x : ℂ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

@[simp] lemma differentiable_at_tan {x : ℂ} : differentiable_at ℂ tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℂ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℂ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, sq]
else (has_deriv_at_tan h).deriv

@[simp] lemma times_cont_diff_at_tan {x : ℂ} {n : with_top ℕ} :
  times_cont_diff_at ℂ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  times_cont_diff_sin.times_cont_diff_at.div times_cont_diff_cos.times_cont_diff_at⟩

end complex
