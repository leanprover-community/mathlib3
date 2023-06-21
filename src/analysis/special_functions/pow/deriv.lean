/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
import analysis.special_functions.pow.continuity
import analysis.special_functions.complex.log_deriv
import analysis.calculus.extend_deriv
import analysis.calculus.deriv.prod
import analysis.special_functions.log.deriv
import analysis.special_functions.trigonometric.deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

noncomputable theory

open_locale classical real topology nnreal ennreal filter
open filter

namespace complex

lemma has_strict_fderiv_at_cpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
  has_strict_fderiv_at (λ x : ℂ × ℂ, x.1 ^ x.2)
    ((p.2 * p.1 ^ (p.2 - 1)) • continuous_linear_map.fst ℂ ℂ ℂ +
      (p.1 ^ p.2 * log p.1) • continuous_linear_map.snd ℂ ℂ ℂ) p :=
begin
  have A : p.1 ≠ 0, by { intro h, simpa [h, lt_irrefl] using hp },
  have : (λ x : ℂ × ℂ, x.1 ^ x.2) =ᶠ[𝓝 p] (λ x, exp (log x.1 * x.2)),
    from ((is_open_ne.preimage continuous_fst).eventually_mem A).mono
      (λ p hp, cpow_def_of_ne_zero hp _),
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul, ← smul_add],
  refine has_strict_fderiv_at.congr_of_eventually_eq _ this.symm,
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm]
    using ((has_strict_fderiv_at_fst.clog hp).mul has_strict_fderiv_at_snd).cexp
end

lemma has_strict_fderiv_at_cpow' {x y : ℂ} (hp : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_fderiv_at (λ x : ℂ × ℂ, x.1 ^ x.2)
    ((y * x ^ (y - 1)) • continuous_linear_map.fst ℂ ℂ ℂ +
      (x ^ y * log x) • continuous_linear_map.snd ℂ ℂ ℂ) (x, y) :=
@has_strict_fderiv_at_cpow (x, y) hp

lemma has_strict_deriv_at_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
  has_strict_deriv_at (λ y, x ^ y) (x ^ y * log x) y :=
begin
  rcases em (x = 0) with rfl|hx,
  { replace h := h.neg_resolve_left rfl,
    rw [log_zero, mul_zero],
    refine (has_strict_deriv_at_const _ 0).congr_of_eventually_eq _,
    exact (is_open_ne.eventually_mem h).mono (λ y hy, (zero_cpow hy).symm) },
  { simpa only [cpow_def_of_ne_zero hx, mul_one]
      using ((has_strict_deriv_at_id y).const_mul (log x)).cexp }
end

lemma has_fderiv_at_cpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
  has_fderiv_at (λ x : ℂ × ℂ, x.1 ^ x.2)
    ((p.2 * p.1 ^ (p.2 - 1)) • continuous_linear_map.fst ℂ ℂ ℂ +
      (p.1 ^ p.2 * log p.1) • continuous_linear_map.snd ℂ ℂ ℂ) p :=
(has_strict_fderiv_at_cpow hp).has_fderiv_at

end complex

section fderiv

open complex

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {f g : E → ℂ} {f' g' : E →L[ℂ] ℂ}
  {x : E} {s : set E} {c : ℂ}

lemma has_strict_fderiv_at.cpow (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_fderiv_at (λ x, f x ^ g x)
    ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
by convert (@has_strict_fderiv_at_cpow ((λ x, (f x, g x)) x) h0).comp x (hf.prod hg)

lemma has_strict_fderiv_at.const_cpow (hf : has_strict_fderiv_at f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  has_strict_fderiv_at (λ x, c ^ f x) ((c ^ f x * log c) • f') x :=
(has_strict_deriv_at_const_cpow h0).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.cpow (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_at (λ x, f x ^ g x)
    ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
by convert (@complex.has_fderiv_at_cpow ((λ x, (f x, g x)) x) h0).comp x (hf.prod hg)

lemma has_fderiv_at.const_cpow (hf : has_fderiv_at f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  has_fderiv_at (λ x, c ^ f x) ((c ^ f x * log c) • f') x :=
(has_strict_deriv_at_const_cpow h0).has_deriv_at.comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cpow (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_within_at (λ x, f x ^ g x)
    ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') s x :=
by convert (@complex.has_fderiv_at_cpow ((λ x, (f x, g x)) x) h0).comp_has_fderiv_within_at x
  (hf.prod hg)

lemma has_fderiv_within_at.const_cpow (hf : has_fderiv_within_at f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  has_fderiv_within_at (λ x, c ^ f x) ((c ^ f x * log c) • f') s x :=
(has_strict_deriv_at_const_cpow h0).has_deriv_at.comp_has_fderiv_within_at x hf

lemma differentiable_at.cpow (hf : differentiable_at ℂ f x) (hg : differentiable_at ℂ g x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_at ℂ (λ x, f x ^ g x) x :=
(hf.has_fderiv_at.cpow hg.has_fderiv_at h0).differentiable_at

lemma differentiable_at.const_cpow (hf : differentiable_at ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  differentiable_at ℂ (λ x, c ^ f x) x :=
(hf.has_fderiv_at.const_cpow h0).differentiable_at

lemma differentiable_within_at.cpow (hf : differentiable_within_at ℂ f s x)
  (hg : differentiable_within_at ℂ g s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_within_at ℂ (λ x, f x ^ g x) s x :=
(hf.has_fderiv_within_at.cpow hg.has_fderiv_within_at h0).differentiable_within_at

lemma differentiable_within_at.const_cpow (hf : differentiable_within_at ℂ f s x)
  (h0 : c ≠ 0 ∨ f x ≠ 0) :
  differentiable_within_at ℂ (λ x, c ^ f x) s x :=
(hf.has_fderiv_within_at.const_cpow h0).differentiable_within_at

end fderiv

section deriv

open complex

variables {f g : ℂ → ℂ} {s : set ℂ} {f' g' x c : ℂ}

/-- A private lemma that rewrites the output of lemmas like `has_fderiv_at.cpow` to the form
expected by lemmas like `has_deriv_at.cpow`. -/
private lemma aux :
  ((g x * f x ^ (g x - 1)) • (1 : ℂ →L[ℂ] ℂ).smul_right f' +
    (f x ^ g x * log (f x)) • (1 : ℂ →L[ℂ] ℂ).smul_right g') 1 =
    g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g' :=
by simp only [algebra.id.smul_eq_mul, one_mul, continuous_linear_map.one_apply,
  continuous_linear_map.smul_right_apply, continuous_linear_map.add_apply, pi.smul_apply,
  continuous_linear_map.coe_smul']

lemma has_strict_deriv_at.cpow (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ x, f x ^ g x)
    (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g') x :=
by simpa only [aux] using (hf.cpow hg h0).has_strict_deriv_at

lemma has_strict_deriv_at.const_cpow (hf : has_strict_deriv_at f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
  has_strict_deriv_at (λ x, c ^ f x) (c ^ f x * log c * f') x :=
(has_strict_deriv_at_const_cpow h).comp x hf

lemma complex.has_strict_deriv_at_cpow_const (h : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_deriv_at (λ z : ℂ, z ^ c) (c * x ^ (c - 1)) x :=
by simpa only [mul_zero, add_zero, mul_one]
  using (has_strict_deriv_at_id x).cpow (has_strict_deriv_at_const x c) h

lemma has_strict_deriv_at.cpow_const (hf : has_strict_deriv_at f f' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ x, f x ^ c) (c * f x ^ (c - 1) * f') x :=
(complex.has_strict_deriv_at_cpow_const h0).comp x hf

lemma has_deriv_at.cpow (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ x, f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g') x :=
by simpa only [aux] using (hf.has_fderiv_at.cpow hg h0).has_deriv_at

lemma has_deriv_at.const_cpow (hf : has_deriv_at f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  has_deriv_at (λ x, c ^ f x) (c ^ f x * log c * f') x :=
(has_strict_deriv_at_const_cpow h0).has_deriv_at.comp x hf

lemma has_deriv_at.cpow_const (hf : has_deriv_at f f' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ x, f x ^ c) (c * f x ^ (c - 1) * f') x :=
(complex.has_strict_deriv_at_cpow_const h0).has_deriv_at.comp x hf

lemma has_deriv_within_at.cpow (hf : has_deriv_within_at f f' s x)
  (hg : has_deriv_within_at g g' s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ x, f x ^ g x)
    (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g') s x :=
by simpa only [aux] using (hf.has_fderiv_within_at.cpow hg h0).has_deriv_within_at

lemma has_deriv_within_at.const_cpow (hf : has_deriv_within_at f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  has_deriv_within_at (λ x, c ^ f x) (c ^ f x * log c * f') s x :=
(has_strict_deriv_at_const_cpow h0).has_deriv_at.comp_has_deriv_within_at x hf

lemma has_deriv_within_at.cpow_const (hf : has_deriv_within_at f f' s x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ x, f x ^ c) (c * f x ^ (c - 1) * f') s x :=
(complex.has_strict_deriv_at_cpow_const h0).has_deriv_at.comp_has_deriv_within_at x hf

/-- Although `λ x, x ^ r` for fixed `r` is *not* complex-differentiable along the negative real
line, it is still real-differentiable, and the derivative is what one would formally expect. -/
lemma has_deriv_at_of_real_cpow {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ -1) :
  has_deriv_at (λ y:ℝ, (y:ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x :=
begin
  rw [ne.def, ←add_eq_zero_iff_eq_neg, ←ne.def] at hr,
  rcases lt_or_gt_of_ne hx.symm with hx | hx,
  { -- easy case : `0 < x`
    convert (((has_deriv_at_id (x:ℂ)).cpow_const _).div_const (r + 1)).comp_of_real,
    { rw [add_sub_cancel, id.def, mul_one, mul_comm, mul_div_cancel _ hr] },
    { rw [id.def, of_real_re], exact or.inl hx } },
  { -- harder case : `x < 0`
    have : ∀ᶠ (y:ℝ) in nhds x, (y:ℂ) ^ (r + 1) / (r + 1) =
      (-y:ℂ) ^ (r + 1) * exp (π * I * (r + 1)) / (r + 1),
    { refine filter.eventually_of_mem (Iio_mem_nhds hx) (λ y hy, _),
      rw of_real_cpow_of_nonpos (le_of_lt hy) },
    refine has_deriv_at.congr_of_eventually_eq _ this,
    rw of_real_cpow_of_nonpos (le_of_lt hx),
    suffices : has_deriv_at (λ (y : ℝ), (-↑y) ^ (r + 1) * exp (↑π * I * (r + 1)))
      ((r + 1) * (-↑x) ^ r * exp (↑π * I * r)) x,
    { convert this.div_const (r + 1) using 1,
      conv_rhs { rw [mul_assoc, mul_comm, mul_div_cancel _ hr] } },
    rw [mul_add ((π:ℂ) * _), mul_one, exp_add, exp_pi_mul_I,
      mul_comm (_ : ℂ) (-1 : ℂ), neg_one_mul],
    simp_rw [mul_neg, ←neg_mul, ←of_real_neg],
    suffices : has_deriv_at (λ (y : ℝ), (↑-y) ^ (r + 1)) (-(r + 1) * (↑-x) ^ r) x,
    { convert this.neg.mul_const _, ring },
    suffices : has_deriv_at (λ (y : ℝ), (↑y) ^ (r + 1)) ((r + 1) * (↑-x) ^ r) (-x),
    { convert @has_deriv_at.scomp ℝ _ ℂ _ _ x ℝ _ _ _ _ _ _ _ _ this (has_deriv_at_neg x) using 1,
      rw [real_smul, of_real_neg 1, of_real_one], ring },
    suffices : has_deriv_at (λ (y : ℂ), y ^ (r + 1)) ((r + 1) * (↑-x) ^ r) (↑-x),
    { exact this.comp_of_real },
    conv in ((↑_) ^ _) { rw (by ring : r = (r + 1) - 1) },
    convert (has_deriv_at_id ((-x : ℝ) : ℂ)).cpow_const _ using 1,
    { simp },
    { left, rwa [id.def, of_real_re, neg_pos] } },
end

end deriv

namespace real

variables {x y z : ℝ}

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
lemma has_strict_fderiv_at_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.1) :
  has_strict_fderiv_at (λ x : ℝ × ℝ, x.1 ^ x.2)
    ((p.2 * p.1 ^ (p.2 - 1)) • continuous_linear_map.fst ℝ ℝ ℝ +
      (p.1 ^ p.2 * log p.1) • continuous_linear_map.snd ℝ ℝ ℝ) p :=
begin
  have : (λ x : ℝ × ℝ, x.1 ^ x.2) =ᶠ[𝓝 p] (λ x, exp (log x.1 * x.2)),
    from (continuous_at_fst.eventually (lt_mem_nhds hp)).mono (λ p hp, rpow_def_of_pos hp _),
  refine has_strict_fderiv_at.congr_of_eventually_eq _ this.symm,
  convert ((has_strict_fderiv_at_fst.log hp.ne').mul has_strict_fderiv_at_snd).exp,
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]
end

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
lemma has_strict_fderiv_at_rpow_of_neg (p : ℝ × ℝ) (hp : p.1 < 0) :
  has_strict_fderiv_at (λ x : ℝ × ℝ, x.1 ^ x.2)
    ((p.2 * p.1 ^ (p.2 - 1)) • continuous_linear_map.fst ℝ ℝ ℝ +
      (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
        continuous_linear_map.snd ℝ ℝ ℝ) p :=
begin
  have : (λ x : ℝ × ℝ, x.1 ^ x.2) =ᶠ[𝓝 p] (λ x, exp (log x.1 * x.2) * cos (x.2 * π)),
    from (continuous_at_fst.eventually (gt_mem_nhds hp)).mono (λ p hp, rpow_def_of_neg hp _),
  refine has_strict_fderiv_at.congr_of_eventually_eq _ this.symm,
  convert ((has_strict_fderiv_at_fst.log hp.ne).mul has_strict_fderiv_at_snd).exp.mul
    (has_strict_fderiv_at_snd.mul_const _).cos using 1,
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp],
  rw [div_eq_mul_inv, add_comm], congr' 2; ring
end

/-- The function `λ (x, y), x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
lemma cont_diff_at_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : ℕ∞} :
  cont_diff_at ℝ n (λ p : ℝ × ℝ, p.1 ^ p.2) p :=
begin
  cases hp.lt_or_lt with hneg hpos,
  exacts [(((cont_diff_at_fst.log hneg.ne).mul cont_diff_at_snd).exp.mul
    (cont_diff_at_snd.mul cont_diff_at_const).cos).congr_of_eventually_eq
      ((continuous_at_fst.eventually (gt_mem_nhds hneg)).mono (λ p hp, rpow_def_of_neg hp _)),
    ((cont_diff_at_fst.log hpos.ne').mul cont_diff_at_snd).exp.congr_of_eventually_eq
      ((continuous_at_fst.eventually (lt_mem_nhds hpos)).mono (λ p hp, rpow_def_of_pos hp _))]
end

lemma differentiable_at_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
  differentiable_at ℝ (λ p : ℝ × ℝ, p.1 ^ p.2) p :=
(cont_diff_at_rpow_of_ne p hp).differentiable_at le_rfl

lemma _root_.has_strict_deriv_at.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : has_strict_deriv_at f f' x)
  (hg : has_strict_deriv_at g g' x) (h : 0 < f x) :
  has_strict_deriv_at (λ x, f x ^ g x)
    (f' * g x * (f x) ^ (g x - 1) + g' * f x ^ g x * log (f x)) x :=
begin
  convert (has_strict_fderiv_at_rpow_of_pos ((λ x, (f x, g x)) x) h).comp_has_strict_deriv_at _
    (hf.prod hg) using 1,
  simp [mul_assoc, mul_comm, mul_left_comm]
end

lemma has_strict_deriv_at_rpow_const_of_ne {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
  has_strict_deriv_at (λ x, x ^ p) (p * x ^ (p - 1)) x :=
begin
  cases hx.lt_or_lt with hx hx,
  { have := (has_strict_fderiv_at_rpow_of_neg (x, p) hx).comp_has_strict_deriv_at x
      ((has_strict_deriv_at_id x).prod (has_strict_deriv_at_const _ _)),
    convert this, simp },
  { simpa using (has_strict_deriv_at_id x).rpow (has_strict_deriv_at_const x p) hx }
end

lemma has_strict_deriv_at_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
  has_strict_deriv_at (λ x, a ^ x) (a ^ x * log a) x :=
by simpa using (has_strict_deriv_at_const _ _).rpow (has_strict_deriv_at_id x) ha

/-- This lemma says that `λ x, a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
lemma has_strict_deriv_at_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
  has_strict_deriv_at (λ x, a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x :=
by simpa using (has_strict_fderiv_at_rpow_of_neg (a, x) ha).comp_has_strict_deriv_at x
  ((has_strict_deriv_at_const _ _).prod (has_strict_deriv_at_id _))

end real

namespace real

variables {z x y : ℝ}

lemma has_deriv_at_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
  has_deriv_at (λ x, x ^ p) (p * x ^ (p - 1)) x :=
begin
  rcases ne_or_eq x 0 with hx | rfl,
  { exact (has_strict_deriv_at_rpow_const_of_ne hx _).has_deriv_at },
  replace h : 1 ≤ p := h.neg_resolve_left rfl,
  apply has_deriv_at_of_has_deriv_at_of_ne
    (λ x hx, (has_strict_deriv_at_rpow_const_of_ne hx p).has_deriv_at),
  exacts [continuous_at_id.rpow_const (or.inr (zero_le_one.trans h)),
    continuous_at_const.mul (continuous_at_id.rpow_const (or.inr (sub_nonneg.2 h)))]
end

lemma differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) :
  differentiable ℝ (λ x : ℝ, x ^ p) :=
λ x, (has_deriv_at_rpow_const (or.inr hp)).differentiable_at

lemma deriv_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
  deriv (λ x : ℝ, x ^ p) x = p * x ^ (p - 1) :=
(has_deriv_at_rpow_const h).deriv

lemma deriv_rpow_const' {p : ℝ} (h : 1 ≤ p) :
  deriv (λ x : ℝ, x ^ p) = λ x, p * x ^ (p - 1) :=
funext $ λ x, deriv_rpow_const (or.inr h)

lemma cont_diff_at_rpow_const_of_ne {x p : ℝ} {n : ℕ∞} (h : x ≠ 0) :
  cont_diff_at ℝ n (λ x, x ^ p) x :=
(cont_diff_at_rpow_of_ne (x, p) h).comp x
  (cont_diff_at_id.prod cont_diff_at_const)

lemma cont_diff_rpow_const_of_le {p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
  cont_diff ℝ n (λ x : ℝ, x ^ p) :=
begin
  induction n with n ihn generalizing p,
  { exact cont_diff_zero.2 (continuous_id.rpow_const (λ x, by exact_mod_cast or.inr h)) },
  { have h1 : 1 ≤ p, from le_trans (by simp) h,
    rw [nat.cast_succ, ← le_sub_iff_add_le] at h,
    rw [cont_diff_succ_iff_deriv, deriv_rpow_const' h1],
    refine ⟨differentiable_rpow_const h1, cont_diff_const.mul (ihn h)⟩ }
end

lemma cont_diff_at_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
  cont_diff_at ℝ n (λ x : ℝ, x ^ p) x :=
(cont_diff_rpow_const_of_le h).cont_diff_at

lemma cont_diff_at_rpow_const {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ ↑n ≤ p) :
  cont_diff_at ℝ n (λ x : ℝ, x ^ p) x :=
h.elim cont_diff_at_rpow_const_of_ne cont_diff_at_rpow_const_of_le

lemma has_strict_deriv_at_rpow_const {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) :
  has_strict_deriv_at (λ x, x ^ p) (p * x ^ (p - 1)) x :=
cont_diff_at.has_strict_deriv_at'
  (cont_diff_at_rpow_const (by rwa nat.cast_one))
  (has_deriv_at_rpow_const hx) le_rfl

end real

section differentiability
open real

section fderiv

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ}
  {x : E} {s : set E} {c p : ℝ} {n : ℕ∞}

lemma has_fderiv_within_at.rpow (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' s x) (h : 0 < f x) :
  has_fderiv_within_at (λ x, f x ^ g x)
    ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') s x :=
(has_strict_fderiv_at_rpow_of_pos (f x, g x) h).has_fderiv_at.comp_has_fderiv_within_at x
  (hf.prod hg)

lemma has_fderiv_at.rpow (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) (h : 0 < f x) :
  has_fderiv_at (λ x, f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
(has_strict_fderiv_at_rpow_of_pos (f x, g x) h).has_fderiv_at.comp x (hf.prod hg)

lemma has_strict_fderiv_at.rpow (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) (h : 0 < f x) :
  has_strict_fderiv_at (λ x, f x ^ g x)
    ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
(has_strict_fderiv_at_rpow_of_pos (f x, g x) h).comp x (hf.prod hg)

lemma differentiable_within_at.rpow (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) (h : f x ≠ 0) :
  differentiable_within_at ℝ (λ x, f x ^ g x) s x :=
(differentiable_at_rpow_of_ne (f x, g x) h).comp_differentiable_within_at x (hf.prod hg)

lemma differentiable_at.rpow (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x)
  (h : f x ≠ 0) :
  differentiable_at ℝ (λ x, f x ^ g x) x :=
(differentiable_at_rpow_of_ne (f x, g x) h).comp x (hf.prod hg)

lemma differentiable_on.rpow (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s)
  (h : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λ x, f x ^ g x) s :=
λ x hx, (hf x hx).rpow (hg x hx) (h x hx)

lemma differentiable.rpow (hf : differentiable ℝ f) (hg : differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
  differentiable ℝ (λ x, f x ^ g x) :=
λ x, (hf x).rpow (hg x) (h x)

lemma has_fderiv_within_at.rpow_const (hf : has_fderiv_within_at f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  has_fderiv_within_at (λ x, f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
(has_deriv_at_rpow_const h).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.rpow_const (hf : has_fderiv_at f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  has_fderiv_at (λ x, f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
(has_deriv_at_rpow_const h).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.rpow_const (hf : has_strict_fderiv_at f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  has_strict_fderiv_at (λ x, f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
(has_strict_deriv_at_rpow_const h).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.rpow_const (hf : differentiable_within_at ℝ f s x)
  (h : f x ≠ 0 ∨ 1 ≤ p) :
  differentiable_within_at ℝ (λ x, f x ^ p) s x :=
(hf.has_fderiv_within_at.rpow_const h).differentiable_within_at

@[simp] lemma differentiable_at.rpow_const (hf : differentiable_at ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  differentiable_at ℝ (λ x, f x ^ p) x :=
(hf.has_fderiv_at.rpow_const h).differentiable_at

lemma differentiable_on.rpow_const (hf : differentiable_on ℝ f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
  differentiable_on ℝ (λ x, f x ^ p) s :=
λ x hx, (hf x hx).rpow_const (h x hx)

lemma differentiable.rpow_const (hf : differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
  differentiable ℝ (λ x, f x ^ p) :=
λ x, (hf x).rpow_const (h x)

lemma has_fderiv_within_at.const_rpow (hf : has_fderiv_within_at f f' s x) (hc : 0 < c) :
  has_fderiv_within_at (λ x, c ^ f x) ((c ^ f x * log c) • f') s x :=
(has_strict_deriv_at_const_rpow hc (f x)).has_deriv_at.comp_has_fderiv_within_at x hf

lemma has_fderiv_at.const_rpow (hf : has_fderiv_at f f' x) (hc : 0 < c) :
  has_fderiv_at (λ x, c ^ f x) ((c ^ f x * log c) • f') x :=
(has_strict_deriv_at_const_rpow hc (f x)).has_deriv_at.comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.const_rpow (hf : has_strict_fderiv_at f f' x) (hc : 0 < c) :
  has_strict_fderiv_at (λ x, c ^ f x) ((c ^ f x * log c) • f') x :=
(has_strict_deriv_at_const_rpow hc (f x)).comp_has_strict_fderiv_at x hf

lemma cont_diff_within_at.rpow (hf : cont_diff_within_at ℝ n f s x)
  (hg : cont_diff_within_at ℝ n g s x) (h : f x ≠ 0) :
  cont_diff_within_at ℝ n (λ x, f x ^ g x) s x :=
(cont_diff_at_rpow_of_ne (f x, g x) h).comp_cont_diff_within_at x (hf.prod hg)

lemma cont_diff_at.rpow (hf : cont_diff_at ℝ n f x) (hg : cont_diff_at ℝ n g x)
  (h : f x ≠ 0) :
  cont_diff_at ℝ n (λ x, f x ^ g x) x :=
(cont_diff_at_rpow_of_ne (f x, g x) h).comp x (hf.prod hg)

lemma cont_diff_on.rpow (hf : cont_diff_on ℝ n f s) (hg : cont_diff_on ℝ n g s)
  (h : ∀ x ∈ s, f x ≠ 0) :
  cont_diff_on ℝ n (λ x, f x ^ g x) s :=
λ x hx, (hf x hx).rpow (hg x hx) (h x hx)

lemma cont_diff.rpow (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g)
  (h : ∀ x, f x ≠ 0) :
  cont_diff ℝ n (λ x, f x ^ g x) :=
cont_diff_iff_cont_diff_at.mpr $
  λ x, hf.cont_diff_at.rpow hg.cont_diff_at (h x)

lemma cont_diff_within_at.rpow_const_of_ne (hf : cont_diff_within_at ℝ n f s x)
  (h : f x ≠ 0) :
  cont_diff_within_at ℝ n (λ x, f x ^ p) s x :=
hf.rpow cont_diff_within_at_const h

lemma cont_diff_at.rpow_const_of_ne (hf : cont_diff_at ℝ n f x) (h : f x ≠ 0) :
  cont_diff_at ℝ n (λ x, f x ^ p) x :=
hf.rpow cont_diff_at_const h

lemma cont_diff_on.rpow_const_of_ne (hf : cont_diff_on ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
  cont_diff_on ℝ n (λ x, f x ^ p) s :=
λ x hx, (hf x hx).rpow_const_of_ne (h x hx)

lemma cont_diff.rpow_const_of_ne (hf : cont_diff ℝ n f) (h : ∀ x, f x ≠ 0) :
  cont_diff ℝ n (λ x, f x ^ p) :=
hf.rpow cont_diff_const h

variable {m : ℕ}

lemma cont_diff_within_at.rpow_const_of_le (hf : cont_diff_within_at ℝ m f s x)
  (h : ↑m ≤ p) :
  cont_diff_within_at ℝ m (λ x, f x ^ p) s x :=
(cont_diff_at_rpow_const_of_le h).comp_cont_diff_within_at x hf

lemma cont_diff_at.rpow_const_of_le (hf : cont_diff_at ℝ m f x) (h : ↑m ≤ p) :
  cont_diff_at ℝ m (λ x, f x ^ p) x :=
by { rw ← cont_diff_within_at_univ at *, exact hf.rpow_const_of_le h }

lemma cont_diff_on.rpow_const_of_le (hf : cont_diff_on ℝ m f s) (h : ↑m ≤ p) :
  cont_diff_on ℝ m (λ x, f x ^ p) s :=
λ x hx, (hf x hx).rpow_const_of_le h

lemma cont_diff.rpow_const_of_le (hf : cont_diff ℝ m f) (h : ↑m ≤ p) :
  cont_diff ℝ m (λ x, f x ^ p) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, hf.cont_diff_at.rpow_const_of_le h

end fderiv

section deriv

variables {f g : ℝ → ℝ} {f' g' x y p : ℝ} {s : set ℝ}

lemma has_deriv_within_at.rpow (hf : has_deriv_within_at f f' s x)
  (hg : has_deriv_within_at g g' s x) (h : 0 < f x) :
  has_deriv_within_at (λ x, f x ^ g x)
    (f' * g x * (f x) ^ (g x - 1) + g' * f x ^ g x * log (f x)) s x :=
begin
  convert (hf.has_fderiv_within_at.rpow hg.has_fderiv_within_at h).has_deriv_within_at using 1,
  dsimp, ring
end

lemma has_deriv_at.rpow (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) (h : 0 < f x) :
  has_deriv_at (λ x, f x ^ g x) (f' * g x * (f x) ^ (g x - 1) + g' * f x ^ g x * log (f x)) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.rpow hg h
end

lemma has_deriv_within_at.rpow_const (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  has_deriv_within_at (λ y, (f y)^p) (f' * p * (f x) ^ (p - 1)) s x :=
begin
  convert (has_deriv_at_rpow_const hx).comp_has_deriv_within_at x hf using 1,
  ring
end

lemma has_deriv_at.rpow_const (hf : has_deriv_at f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  has_deriv_at (λ y, (f y)^p) (f' * p * (f x)^(p-1)) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.rpow_const hx
end

lemma deriv_within_rpow_const (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, (f x) ^ p) s x = (deriv_within f s x) * p * (f x) ^ (p - 1) :=
(hf.has_deriv_within_at.rpow_const hx).deriv_within hxs

@[simp] lemma deriv_rpow_const (hf : differentiable_at ℝ f x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  deriv (λx, (f x)^p) x = (deriv f x) * p * (f x)^(p-1) :=
(hf.has_deriv_at.rpow_const hx).deriv

end deriv

end differentiability

section limits
open real filter

/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞`. -/
lemma tendsto_one_plus_div_rpow_exp (t : ℝ) :
  tendsto (λ (x : ℝ), (1 + t / x) ^ x) at_top (𝓝 (exp t)) :=
begin
  apply ((real.continuous_exp.tendsto _).comp (tendsto_mul_log_one_plus_div_at_top t)).congr' _,
  have h₁ : (1:ℝ)/2 < 1 := by linarith,
  have h₂ : tendsto (λ x : ℝ, 1 + t / x) at_top (𝓝 1) :=
    by simpa using (tendsto_inv_at_top_zero.const_mul t).const_add 1,
  refine (eventually_ge_of_tendsto_gt h₁ h₂).mono (λ x hx, _),
  have hx' : 0 < 1 + t / x := by linarith,
  simp [mul_comm x, exp_mul, exp_log hx'],
end

/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞` for naturals `x`. -/
lemma tendsto_one_plus_div_pow_exp (t : ℝ) :
  tendsto (λ (x : ℕ), (1 + t / (x:ℝ)) ^ x) at_top (𝓝 (real.exp t)) :=
((tendsto_one_plus_div_rpow_exp t).comp tendsto_coe_nat_at_top_at_top).congr (by simp)

end limits
