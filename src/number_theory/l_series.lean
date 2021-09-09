/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import analysis.p_series
import number_theory.arithmetic_function
import topology.algebra.infinite_sum

/-!
# L-series

Given an arithmetic function, we define the corresponding L-series.

## Main Definitions
 * `nat.arithmetic_function.l_series` is the `l_series` with a given arithmetic function as its
  coefficients. This is not the analytic continuation, just the infinite series.
 * `nat.arithmetic_function.l_series_summable` indicates that the `l_series`
  converges at a given point.

## Main Results
 * `nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re`: the `l_series` of a bounded
  arithmetic function converges when `1 < z.re`.
 * `nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re`: the `l_series` of `ζ`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

-/

noncomputable theory
open_locale big_operators

namespace nat
namespace arithmetic_function

/-- The L-series of an `arithmetic_function`. -/
def l_series (f : arithmetic_function ℂ) (z : ℂ) : ℂ := ∑'n, (f n) / (n ^ z)

/-- `f.l_series_summable z` indicates that the L-series of `f` converges at `z`. -/
def l_series_summable (f : arithmetic_function ℂ) (z : ℂ) : Prop := summable (λ n, (f n) / (n ^ z))

lemma l_series_eq_zero_of_not_l_series_summable (f : arithmetic_function ℂ) (z : ℂ) :
  ¬ f.l_series_summable z → f.l_series z = 0 :=
tsum_eq_zero_of_not_summable

@[simp]
lemma l_series_summable_zero {z : ℂ} : l_series_summable 0 z :=
by simp [l_series_summable, summable_zero]

theorem l_series_summable_of_bounded_of_one_lt_real {f : arithmetic_function ℂ} {m : ℝ}
  (h : ∀ (n : ℕ), complex.abs (f n) ≤ m) {z : ℝ} (hz : 1 < z) :
  f.l_series_summable z :=
begin
  by_cases h0 : m = 0,
  { subst h0,
    have hf : f = 0 := arithmetic_function.ext (λ n, complex.abs_eq_zero.1
        (le_antisymm (h n) (complex.abs_nonneg _))),
    simp [hf] },
  refine summable_of_norm_bounded (λ (n : ℕ), m / (n ^ z)) _ _,
  { simp_rw [div_eq_mul_inv],
    exact (summable_mul_left_iff h0).1 (real.summable_nat_rpow_inv.2 hz) },
  { intro n,
    have hm : 0 ≤ m := le_trans (complex.abs_nonneg _) (h 0),
    cases n,
    { simp [hm, real.zero_rpow (ne_of_gt (lt_trans real.zero_lt_one hz))] },
    simp only [complex.abs_div, complex.norm_eq_abs],
    apply div_le_div hm (h _) (real.rpow_pos_of_pos (nat.cast_pos.2 n.succ_pos) _) (le_of_eq _),
    rw [complex.abs_cpow_real, complex.abs_cast_nat] }
end

theorem l_series_summable_iff_of_re_eq_re {f : arithmetic_function ℂ} {w z : ℂ} (h : w.re = z.re) :
  f.l_series_summable w ↔ f.l_series_summable z :=
begin
  suffices h : ∀ n : ℕ, complex.abs (f n) / complex.abs (↑n ^ w) =
    complex.abs (f n) / complex.abs (↑n ^ z),
  { simp [l_series_summable, ← summable_norm_iff, h, complex.norm_eq_abs] },
  intro n,
  cases n, { simp },
  apply congr rfl,
  have h0 : (n.succ : ℂ) ≠ 0,
  { rw [ne.def, nat.cast_eq_zero],
    apply n.succ_ne_zero },
  rw [complex.cpow_def, complex.cpow_def, if_neg h0, if_neg h0, complex.abs_exp_eq_iff_re_eq],
  simp only [h, complex.mul_re, mul_eq_mul_left_iff, sub_right_inj],
  right,
  rw [complex.log_im, ← complex.of_real_nat_cast],
  exact complex.arg_of_real_of_nonneg (le_of_lt (cast_pos.2 n.succ_pos)),
end

theorem l_series_summable_of_bounded_of_one_lt_re {f : arithmetic_function ℂ} {m : ℝ}
  (h : ∀ (n : ℕ), complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) :
  f.l_series_summable z :=
begin
  rw ← l_series_summable_iff_of_re_eq_re (complex.of_real_re z.re),
  apply l_series_summable_of_bounded_of_one_lt_real h,
  exact hz,
end

open_locale arithmetic_function

theorem zeta_l_series_summable_iff_one_lt_re {z : ℂ} :
  l_series_summable ζ z ↔ 1 < z.re :=
begin
  rw [← l_series_summable_iff_of_re_eq_re (complex.of_real_re z.re), l_series_summable,
    ← summable_norm_iff, ← real.summable_one_div_nat_rpow, iff_iff_eq],
  by_cases h0 : z.re = 0,
  { rw [h0, ← summable_nat_add_iff 1],
    swap, { apply_instance },
    apply congr rfl,
    ext n,
    simp [n.succ_ne_zero] },
  { apply congr rfl,
    ext n,
    cases n, { simp [h0] },
    simp only [n.succ_ne_zero, one_div, cast_one, nat_coe_apply, complex.abs_cpow_real, inv_inj',
      complex.abs_inv, if_false, zeta_apply, complex.norm_eq_abs, complex.abs_of_nat] }
end

@[simp] theorem l_series_add {f g : arithmetic_function ℂ} {z : ℂ}
  (hf : f.l_series_summable z) (hg : g.l_series_summable z) :
  (f + g).l_series z = f.l_series z + g.l_series z :=
begin
  simp only [l_series, add_apply],
  rw ← tsum_add hf hg,
  apply congr rfl (funext (λ n, _)),
  apply _root_.add_div,
end

end arithmetic_function
end nat
