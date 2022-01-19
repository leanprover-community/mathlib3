/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.special_functions.log
import analysis.special_functions.exp_deriv

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarighm, derivative
-/

open filter finset set
open_locale topological_space big_operators

namespace real

variables {x : ℝ}

lemma has_strict_deriv_at_log_of_pos (hx : 0 < x) : has_strict_deriv_at log x⁻¹ x :=
have has_strict_deriv_at log (exp $ log x)⁻¹ x,
from (has_strict_deriv_at_exp $ log x).of_local_left_inverse (continuous_at_log hx.ne')
  (ne_of_gt $ exp_pos _) $ eventually.mono (lt_mem_nhds hx) @exp_log,
by rwa [exp_log hx] at this

lemma has_strict_deriv_at_log (hx : x ≠ 0) : has_strict_deriv_at log x⁻¹ x :=
begin
  cases hx.lt_or_lt with hx hx,
  { convert (has_strict_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_strict_deriv_at_neg x),
    { ext y, exact (log_neg_eq_log y).symm },
    { field_simp [hx.ne] } },
  { exact has_strict_deriv_at_log_of_pos hx }
end

lemma has_deriv_at_log (hx : x ≠ 0) : has_deriv_at log x⁻¹ x :=
(has_strict_deriv_at_log hx).has_deriv_at

lemma differentiable_at_log (hx : x ≠ 0) : differentiable_at ℝ log x :=
(has_deriv_at_log hx).differentiable_at

lemma differentiable_on_log : differentiable_on ℝ log {0}ᶜ :=
λ x hx, (differentiable_at_log hx).differentiable_within_at

@[simp] lemma differentiable_at_log_iff : differentiable_at ℝ log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at, differentiable_at_log⟩

lemma deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
if hx : x = 0 then
  by rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx,
    inv_zero]
else (has_deriv_at_log hx).deriv

@[simp] lemma deriv_log' : deriv log = has_inv.inv := funext deriv_log

lemma times_cont_diff_on_log {n : with_top ℕ} : times_cont_diff_on ℝ n log {0}ᶜ :=
begin
  suffices : times_cont_diff_on ℝ ⊤ log {0}ᶜ, from this.of_le le_top,
  refine (times_cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _,
  simp [differentiable_on_log, times_cont_diff_on_inv]
end

lemma times_cont_diff_at_log {n : with_top ℕ} : times_cont_diff_at ℝ n log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at,
  λ hx, (times_cont_diff_on_log x hx).times_cont_diff_at $
    is_open.mem_nhds is_open_compl_singleton hx⟩

end real

section log_differentiable
open real

section deriv

variables {f : ℝ → ℝ} {x f' : ℝ} {s : set ℝ}

lemma has_deriv_within_at.log (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, log (f y)) (f' / (f x)) s x :=
begin
  rw div_eq_inv_mul,
  exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf
end

lemma has_deriv_at.log (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.log hx
end

lemma has_strict_deriv_at.log (hf : has_strict_deriv_at f f' x) (hx : f x ≠ 0) :
  has_strict_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw div_eq_inv_mul,
  exact (has_strict_deriv_at_log hx).comp x hf
end

lemma deriv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, log (f x)) s x = (deriv_within f s x) / (f x) :=
(hf.has_deriv_within_at.log hx).deriv_within hxs

@[simp] lemma deriv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, log (f x)) x = (deriv f x) / (f x) :=
(hf.has_deriv_at.log hx).deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : set E}

lemma has_fderiv_within_at.log (hf : has_fderiv_within_at f f' s x) (hx : f x ≠ 0) :
  has_fderiv_within_at (λ x, log (f x)) ((f x)⁻¹ • f') s x :=
(has_deriv_at_log hx).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.log (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_deriv_at_log hx).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.log (hf : has_strict_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_strict_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log hx).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, log (f x)) s x :=
(hf.has_fderiv_within_at.log hx).differentiable_within_at

@[simp] lemma differentiable_at.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, log (f x)) x :=
(hf.has_fderiv_at.log hx).differentiable_at

lemma times_cont_diff_at.log {n} (hf : times_cont_diff_at ℝ n f x) (hx : f x ≠ 0) :
  times_cont_diff_at ℝ n (λ x, log (f x)) x :=
(times_cont_diff_at_log.2 hx).comp x hf

lemma times_cont_diff_within_at.log {n} (hf : times_cont_diff_within_at ℝ n f s x) (hx : f x ≠ 0) :
  times_cont_diff_within_at ℝ n (λ x, log (f x)) s x :=
(times_cont_diff_at_log.2 hx).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_on.log {n} (hf : times_cont_diff_on ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
  times_cont_diff_on ℝ n (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (hs x hx)

lemma times_cont_diff.log {n} (hf : times_cont_diff ℝ n f) (h : ∀ x, f x ≠ 0) :
  times_cont_diff ℝ n (λ x, log (f x)) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, hf.times_cont_diff_at.log (h x)

lemma differentiable_on.log (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, log (f x)) s :=
λx h, (hf x h).log (hx x h)

@[simp] lemma differentiable.log (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, log (f x)) :=
λx, (hf x).log (hx x)

lemma fderiv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, log (f x)) s x = (f x)⁻¹ • fderiv_within ℝ f s x :=
(hf.has_fderiv_within_at.log hx).fderiv_within hxs

@[simp] lemma fderiv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (λx, log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
(hf.has_fderiv_at.log hx).fderiv

end fderiv

end log_differentiable

namespace real

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
lemma tendsto_mul_log_one_plus_div_at_top (t : ℝ) :
  tendsto (λ x, x * log (1 + t / x)) at_top (𝓝 t) :=
begin
  have h₁ : tendsto (λ h, h⁻¹ * log (1 + t * h)) (𝓝[{0}ᶜ] 0) (𝓝 t),
  { simpa [has_deriv_at_iff_tendsto_slope] using
      ((has_deriv_at_const _ 1).add ((has_deriv_at_id (0 : ℝ)).const_mul t)).log (by simp) },
  have h₂ : tendsto (λ x : ℝ, x⁻¹) at_top (𝓝[{0}ᶜ] 0) :=
    tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ (λ x hx, (set.mem_Ioi.mp hx).ne')),
  convert h₁.comp h₂,
  ext,
  field_simp [mul_comm],
end

open_locale big_operators

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
lemma abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |((∑ i in range n, x^(i+1)/(i+1)) + log (1-x))| ≤ (|x|)^(n+1) / (1 - |x|) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, ∑ i in range n, x^(i+1)/(i+1) + log (1-x),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - (y^n) / (1 - y),
  { assume y hy,
    have : (∑ i in range n, (↑i + 1) * y ^ i / (↑i + 1)) = (∑ i in range n, y ^ i),
    { congr' with i,
      have : (i : ℝ) + 1 ≠ 0 := ne_of_gt (nat.cast_add_one_pos i),
      field_simp [this, mul_comm] },
    field_simp [F, this, ← geom_sum_def, geom_sum_eq (ne_of_lt hy.2),
                sub_ne_zero_of_ne (ne_of_gt hy.2), sub_ne_zero_of_ne (ne_of_lt hy.2)],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) (|x|), |deriv F y| ≤ |x|^n / (1 - |x|),
  { assume y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_le (neg_lt_neg h) hy.1, lt_of_le_of_lt hy.2 h⟩,
    calc |deriv F y| = | -(y^n) / (1 - y)| : by rw [A y this]
    ... ≤ |x|^n / (1 - |x|) :
      begin
        have : |y| ≤ |x| := abs_le.2 hy,
        have : 0 < 1 - |x|, by linarith,
        have : 1 - |x| ≤ |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _),
        simp only [← pow_abs, abs_div, abs_neg],
        apply_rules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
      end },
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ (|x|^n / (1 - |x|)) * ∥x - 0∥,
  { have : ∀ y ∈ Icc (- |x|) (|x|), differentiable_at ℝ F y,
    { assume y hy,
      have : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gt (lt_of_le_of_lt hy.2 h)),
      simp [F, this] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simpa using abs_nonneg x },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, norm_eq_abs, div_mul_eq_mul_div, pow_succ'] using C
end

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : |x| < 1) :
  has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x)) :=
begin
  rw summable.has_sum_iff_tendsto_nat,
  show tendsto (λ (n : ℕ), ∑ (i : ℕ) in range n, x ^ (i + 1) / (i + 1)) at_top (𝓝 (-log (1 - x))),
  { rw [tendsto_iff_norm_tendsto_zero],
    simp only [norm_eq_abs, sub_neg_eq_add],
    refine squeeze_zero (λ n, abs_nonneg _) (abs_log_sub_add_sum_range_le h) _,
    suffices : tendsto (λ (t : ℕ), |x| ^ (t + 1) / (1 - |x|)) at_top
      (𝓝 (|x| * 0 / (1 - |x|))), by simpa,
    simp only [pow_succ],
    refine (tendsto_const_nhds.mul _).div_const,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h },
  show summable (λ (n : ℕ), x ^ (n + 1) / (n + 1)),
  { refine summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) (λ i, _),
    calc ∥x ^ (i + 1) / (i + 1)∥
    = |x| ^ (i+1) / (i+1) :
      begin
        have : (0 : ℝ) ≤ i + 1 := le_of_lt (nat.cast_add_one_pos i),
        rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this],
      end
    ... ≤ |x| ^ (i+1) / (0 + 1) :
      begin
        apply_rules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right,
          i.cast_nonneg],
        norm_num,
      end
    ... ≤ |x| ^ i :
      by simpa [pow_succ'] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h) }
end

end real
