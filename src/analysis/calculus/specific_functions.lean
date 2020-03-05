/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.extend_deriv analysis.calculus.iterated_deriv analysis.complex.exponential

/-!
# Smoothness of specific functions

The real function `exp_neg_inv_glue` given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0` is a basic building block to construct smooth partitions of unity. We prove that it
is `C^∞` in `exp_neg_inv_glue_smooth`.
-/

noncomputable theory
open_locale classical topological_space

namespace partition_of_unity
open polynomial real filter set

/-- `exp_neg_inv_glue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`exp_neg_inv_glue_smooth`. -/
def exp_neg_inv_glue (x : ℝ) : ℝ := if x ≤ 0 then 0 else exp (-x⁻¹)

/-- Our goal is to prove that `exp_neg_inv_glue` is `C^∞`. For this, we compute its successive
derivatives for `x > 0`. The `n`-th derivative is of the form `P_n(x) exp(-1/x) / x^(2 n)`,
where `P_n` is computed inductively. We define `exp_neg_inv_aux_poly n` to be this `P_n`. -/
noncomputable def exp_neg_inv_aux_poly : ℕ → polynomial ℝ
| 0 := 1
| (n+1) := X^2 * (exp_neg_inv_aux_poly n).derivative  + (1 - C (2 * n) * X) * (exp_neg_inv_aux_poly n)

/-- Formula for the `n`-th derivative of `exp_neg_inv_glue`. -/
def exp_neg_inv_glue_aux (n : ℕ) (x : ℝ) : ℝ :=
if x ≤ 0 then 0 else (exp_neg_inv_aux_poly n).eval x * exp (-x⁻¹) / x^(2 * n)

/-- The `0`-th auxiliary function `exp_neg_inv_glue_aux 0` coincides with `exp_neg_inv_glue`, by
definition. -/
lemma exp_neg_inv_glue_eq_exp_neg_inv_glue_aux_zero :
  exp_neg_inv_glue = exp_neg_inv_glue_aux 0 :=
begin
   ext x,
   by_cases h : x ≤ 0,
   { simp [exp_neg_inv_glue, exp_neg_inv_glue_aux, h] },
   { simp [h, exp_neg_inv_glue, exp_neg_inv_glue_aux, ne_of_gt (not_le.1 h), exp_neg_inv_aux_poly] }
end

/-- For positive values, the derivative of the `n`-th auxiliary function `exp_neg_inv_glue_aux n`
(given in this auxiliary statement in unfolded form) is the `n+1`-th auxiliary function, since
the polynomial `exp_neg_inv_aux_poly (n+1)` was chosen precisely to ensure this. -/
lemma exp_neg_inv_aux_deriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
  has_deriv_at (λx, (exp_neg_inv_aux_poly n).eval x * exp (-x⁻¹) / x^(2 * n))
    ((exp_neg_inv_aux_poly (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  have A : ∀k:ℕ, 2 * (k + 1) - 1 = 2 * k + 1, by omega,
  convert (((exp_neg_inv_aux_poly n).has_deriv_at x).mul
               (((has_deriv_at_exp _).comp x (has_deriv_at_inv hx).neg))).div
            (has_deriv_at_pow (2 * n) x) (pow_ne_zero _ hx) using 1,
  field_simp [hx, exp_neg_inv_aux_poly],
  cases n; simp [nat.succ_eq_add_one, A]; ring_exp
end

/-- For positive values, the derivative of the `n`-th auxiliary function `exp_neg_inv_glue_aux n`
is the `n+1`-th auxiliary function. -/
lemma exp_neg_inv_glue_aux_deriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
  has_deriv_at (exp_neg_inv_glue_aux n)
    ((exp_neg_inv_aux_poly (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  apply (exp_neg_inv_aux_deriv n x (ne_of_gt hx)).congr_of_mem_nhds,
  have : Ioi (0 : ℝ) ∈ 𝓝 x := lt_mem_nhds hx,
  filter_upwards [this],
  assume y hy,
  have : ¬(y ≤ 0), by simpa using hy,
  simp [exp_neg_inv_glue_aux, this]
end

/-- To get differentiability at `0` of the auxiliary functions, we need to know that their limit
is `0`, to be able to apply general differentiability extension theorems. This limit is checked in
this lemma. -/
lemma exp_neg_inv_aux_limit (n : ℕ) :
  tendsto (λx, (exp_neg_inv_aux_poly n).eval x * exp (-x⁻¹) / x^(2 * n))
    (nhds_within 0 (Ioi 0)) (𝓝 0) :=
begin
  have A : tendsto (λx, (exp_neg_inv_aux_poly n).eval x)
    (nhds_within 0 (Ioi 0)) (𝓝 ((exp_neg_inv_aux_poly n).eval 0)) :=
  (exp_neg_inv_aux_poly n).continuous_within_at,
  have B : tendsto (λx, exp (-x⁻¹) / x^(2 * n)) (nhds_within 0 (Ioi 0)) (𝓝 0),
  { convert (tendsto_pow_mul_exp_neg_at_top_nhds_0 (2 * n)).comp tendsto_inv_zero_at_top,
    ext x,
    field_simp },
  convert A.mul B;
  simp [mul_div_assoc]
end

/-- Deduce from the limiting behavior at `0` of its derivative and general differentiability
extension theorems that the auxiliary function `exp_neg_inv_glue_aux n` is differentiable at `0`,
with derivative `0`. -/
lemma exp_neg_inv_glue_aux_deriv_zero (n : ℕ) :
  has_deriv_at (exp_neg_inv_glue_aux n) 0 0 :=
begin
  -- we check separately differentiability on the left and on the right
  have A : has_deriv_within_at (exp_neg_inv_glue_aux n) (0 : ℝ) (Iic 0) 0,
  { apply (has_deriv_at_const (0 : ℝ) (0 : ℝ)).has_deriv_within_at.congr,
    { assume y hy,
      simp at hy,
      simp [exp_neg_inv_glue_aux, hy] },
    { simp [exp_neg_inv_glue_aux, le_refl] } },
  have B : has_deriv_within_at (exp_neg_inv_glue_aux n) (0 : ℝ) (Ici 0) 0,
  { have diff : differentiable_on ℝ (exp_neg_inv_glue_aux n) (Ioi 0) :=
      λx hx, (exp_neg_inv_glue_aux_deriv_pos n x hx).differentiable_at.differentiable_within_at,
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff _ self_mem_nhds_within,
    { refine (exp_neg_inv_aux_limit (n+1)).congr' _,
      apply mem_sets_of_superset self_mem_nhds_within (λx hx, _),
      simp [(exp_neg_inv_glue_aux_deriv_pos n x hx).deriv] },
    { have : exp_neg_inv_glue_aux n 0 = 0, by simp [exp_neg_inv_glue_aux, le_refl],
      simp only [continuous_within_at, this],
      refine (exp_neg_inv_aux_limit n).congr' _,
      apply mem_sets_of_superset self_mem_nhds_within (λx hx, _),
      have : ¬(x ≤ 0), by simpa using hx,
      simp [exp_neg_inv_glue_aux, this] } },
  simpa using A.union B,
end

/-- At every point, the auxiliary function `exp_neg_inv_glue_aux n` has a derivative which is
equal to `exp_neg_inv_glue_aux (n+1)`. -/
lemma exp_neg_inv_glue_aux_has_deriv_at (n : ℕ) (x : ℝ) :
  has_deriv_at (exp_neg_inv_glue_aux n) (exp_neg_inv_glue_aux (n+1) x) x :=
begin
  -- check separately the result for `x < 0`, where it is trivial, for `x > 0`, where it is done
  -- in `exp_neg_inv_glue_aux_deriv_pos`, and for `x = 0`, done in
  -- `exp_neg_inv_glue_aux_deriv_zero`.
  rcases lt_trichotomy x 0 with hx|hx|hx,
  { have : exp_neg_inv_glue_aux (n+1) x = 0, by simp [exp_neg_inv_glue_aux, le_of_lt hx],
    rw this,
    apply (has_deriv_at_const x (0 : ℝ)).congr_of_mem_nhds,
    have : Iio (0 : ℝ) ∈ 𝓝 x := gt_mem_nhds hx,
    filter_upwards [this],
    assume y hy,
    simp [exp_neg_inv_glue_aux, le_of_lt hy] },
  { have : exp_neg_inv_glue_aux (n + 1) 0 = 0, by simp [exp_neg_inv_glue_aux, le_refl],
    rw [hx, this],
    exact exp_neg_inv_glue_aux_deriv_zero n },
  { have : exp_neg_inv_glue_aux (n+1) x
      = (exp_neg_inv_aux_poly (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n+1)),
      by simp [exp_neg_inv_glue_aux, not_le_of_gt hx],
    rw this,
    exact exp_neg_inv_glue_aux_deriv_pos n x hx },
end

/-- The successive derivatives of the auxiliary function `exp_neg_inv_glue_aux 0` are the
functions `exp_neg_inv_glue_aux n`, by induction. -/
lemma exp_neg_inv_glue_aux_iterated_deriv (n : ℕ) :
  iterated_deriv n (exp_neg_inv_glue_aux 0) = exp_neg_inv_glue_aux n :=
begin
  induction n with n IH,
  { simp },
  { simp [iterated_deriv_succ, IH],
    ext x,
    exact (exp_neg_inv_glue_aux_has_deriv_at n x).deriv }
end

/-- The function `exp_neg_inv_glue` is smooth. -/
theorem exp_neg_inv_glue_smooth : times_cont_diff ℝ ⊤ (exp_neg_inv_glue) :=
begin
  rw exp_neg_inv_glue_eq_exp_neg_inv_glue_aux_zero,
  apply times_cont_diff_of_differentiable_iterated_deriv (λ m hm, _),
  rw exp_neg_inv_glue_aux_iterated_deriv m,
  exact λ x, (exp_neg_inv_glue_aux_has_deriv_at m x).differentiable_at
end

/-- The function `exp_neg_inv_glue` vanishes on `(-∞, 0]`. -/
lemma exp_neg_inv_glue_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : exp_neg_inv_glue x = 0 :=
by simp [exp_neg_inv_glue, hx]

/-- The function `exp_neg_inv_glue` is positive on `(0, +∞)`. -/
lemma exp_neg_inv_glue_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < exp_neg_inv_glue x :=
by simp [exp_neg_inv_glue, not_le.2 hx, exp_pos]

/-- The function exp_neg_inv_glue` is nonnegative. -/
lemma exp_neg_inv_glue_nonneg (x : ℝ) : 0 ≤ exp_neg_inv_glue x :=
begin
  cases le_or_gt x 0,
  { exact ge_of_eq (exp_neg_inv_glue_zero_of_nonpos h) },
  { exact le_of_lt (exp_neg_inv_glue_pos_of_pos h) }
end

end partition_of_unity
