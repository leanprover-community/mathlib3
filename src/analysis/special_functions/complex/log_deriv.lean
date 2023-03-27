/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.complex.log
import analysis.special_functions.exp_deriv

/-!
# Differentiability of the complex `log` function

-/

noncomputable theory

namespace complex

open set filter

open_locale real topology

/-- `complex.exp` as a `local_homeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}`. This definition is used to prove that `complex.log`
is complex differentiable at all points but the negative real semi-axis. -/
def exp_local_homeomorph : local_homeomorph ℂ ℂ :=
local_homeomorph.of_continuous_open
{ to_fun := exp,
  inv_fun := log,
  source := {z : ℂ | z.im ∈ Ioo (- π) π},
  target := {z : ℂ | 0 < z.re} ∪ {z : ℂ | z.im ≠ 0},
  map_source' :=
    begin
      rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩,
      refine (not_or_of_imp $ λ hz, _).symm,
      obtain rfl : y = 0,
      { rw exp_im at hz,
        simpa [(real.exp_pos _).ne', real.sin_eq_zero_iff_of_lt_of_lt h₁ h₂] using hz },
      rw [mem_set_of_eq, ← of_real_def, exp_of_real_re],
      exact real.exp_pos x
    end,
  map_target' := λ z h,
    suffices 0 ≤ z.re ∨ z.im ≠ 0,
      by simpa [log_im, neg_pi_lt_arg, (arg_le_pi _).lt_iff_ne, arg_eq_pi_iff, not_and_distrib],
    h.imp (λ h, le_of_lt h) id,
  left_inv' := λ x hx, log_exp hx.1 (le_of_lt hx.2),
  right_inv' := λ x hx, exp_log $ by { rintro rfl, simpa [lt_irrefl] using hx } }
continuous_exp.continuous_on is_open_map_exp (is_open_Ioo.preimage continuous_im)

lemma has_strict_deriv_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_deriv_at log x⁻¹ x :=
have h0 :  x ≠ 0, by { rintro rfl, simpa [lt_irrefl] using h },
exp_local_homeomorph.has_strict_deriv_at_symm h h0 $
  by simpa [exp_log h0] using has_strict_deriv_at_exp (log x)

lemma has_strict_fderiv_at_log_real {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_fderiv_at log (x⁻¹ • (1 : ℂ →L[ℝ] ℂ)) x :=
(has_strict_deriv_at_log h).complex_to_real_fderiv

lemma cont_diff_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) {n : ℕ∞} :
  cont_diff_at ℂ n log x :=
exp_local_homeomorph.cont_diff_at_symm_deriv (exp_ne_zero $ log x) h
  (has_deriv_at_exp _) cont_diff_exp.cont_diff_at

end complex

section log_deriv

open complex filter
open_locale topology

variables {α : Type*} [topological_space α] {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]

lemma has_strict_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_strict_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).comp_has_strict_fderiv_at x h₁

lemma has_strict_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_strict_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).comp x h₁ }

lemma has_strict_deriv_at.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : has_strict_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ t, log (f t)) (f' / f x) x :=
by simpa only [div_eq_inv_mul]
  using (has_strict_fderiv_at_log_real h₂).comp_has_strict_deriv_at x h₁

lemma has_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_at x h₁

lemma has_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).has_deriv_at.comp x h₁ }

lemma has_deriv_at.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : has_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ t, log (f t)) (f' / f x) x :=
by simpa only [div_eq_inv_mul]
  using (has_strict_fderiv_at_log_real h₂).has_fderiv_at.comp_has_deriv_at x h₁

lemma differentiable_at.clog {f : E → ℂ} {x : E} (h₁ : differentiable_at ℂ f x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_at ℂ (λ t, log (f t)) x :=
(h₁.has_fderiv_at.clog h₂).differentiable_at

lemma has_fderiv_within_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {s : set E} {x : E}
  (h₁ : has_fderiv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_within_at (λ t, log (f t)) ((f x)⁻¹ • f') s x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_within_at x h₁

lemma has_deriv_within_at.clog {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}
  (h₁ : has_deriv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ t, log (f t)) (f' / f x) s x :=
by { rw div_eq_inv_mul,
     exact (has_strict_deriv_at_log h₂).has_deriv_at.comp_has_deriv_within_at x h₁ }

lemma has_deriv_within_at.clog_real {f : ℝ → ℂ} {s : set ℝ} {x : ℝ} {f' : ℂ}
  (h₁ : has_deriv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ t, log (f t)) (f' / f x) s x :=
by simpa only [div_eq_inv_mul]
  using (has_strict_fderiv_at_log_real h₂).has_fderiv_at.comp_has_deriv_within_at x h₁

lemma differentiable_within_at.clog {f : E → ℂ} {s : set E} {x : E}
  (h₁ : differentiable_within_at ℂ f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_within_at ℂ (λ t, log (f t)) s x :=
(h₁.has_fderiv_within_at.clog h₂).differentiable_within_at

lemma differentiable_on.clog {f : E → ℂ} {s : set E}
  (h₁ : differentiable_on ℂ f s) (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_on ℂ (λ t, log (f t)) s :=
λ x hx, (h₁ x hx).clog (h₂ x hx)

lemma differentiable.clog {f : E → ℂ} (h₁ : differentiable ℂ f)
  (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable ℂ (λ t, log (f t)) :=
λ x, (h₁ x).clog (h₂ x)

end log_deriv
