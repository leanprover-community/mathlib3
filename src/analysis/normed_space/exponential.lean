/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.specific_limits
import analysis.analytic.basic
import analysis.complex.basic
import data.nat.choose.cast

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 𝔸`, the exponential map in a normed algebra `𝔸` over a nondiscrete
normed field `𝕂`. Although the definition doesn't require `𝔸` to be complete, we need to assume it
for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_lt_radius` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂 𝔸` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
  for any `x` and `y`

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 𝔸 = exp 𝕂' 𝔸`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topological_space big_operators ennreal

section any_field_any_algebra

variables (𝕂 𝔸 : Type*) [nondiscrete_normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp_series 𝕂 𝔸` is the
`formal_multilinear_series` whose `n`-th term is the map `(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`.
Its sum is the exponential map `exp 𝕂 𝔸 : 𝔸 → 𝔸`. -/
def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
  λ n, (1/n! : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp 𝕂 𝔸 : 𝔸 → 𝔸` is the exponential map
determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂 𝔸}

lemma exp_series_apply_eq (x : 𝔸) (n : ℕ) : exp_series 𝕂 𝔸 n (λ _, x) = (1 / n! : 𝕂) • x^n :=
by simp [exp_series]

lemma exp_series_apply_eq' (x : 𝔸) :
  (λ n, exp_series 𝕂 𝔸 n (λ _, x)) = (λ n, (1 / n! : 𝕂) • x^n) :=
funext (exp_series_apply_eq x)

lemma exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : exp_series 𝕂 𝕂 n (λ _, x) = x^n / n! :=
begin
  rw [div_eq_inv_mul, ←smul_eq_mul, inv_eq_one_div],
  exact exp_series_apply_eq x n,
end

lemma exp_series_apply_eq_field' (x : 𝕂) : (λ n, exp_series 𝕂 𝕂 n (λ _, x)) = (λ n, x^n / n!) :=
funext (exp_series_apply_eq_field x)

lemma exp_series_sum_eq (x : 𝔸) : (exp_series 𝕂 𝔸).sum x = ∑' (n : ℕ), (1 / n! : 𝕂) • x^n :=
tsum_congr (λ n, exp_series_apply_eq x n)

lemma exp_series_sum_eq_field (x : 𝕂) : (exp_series 𝕂 𝕂).sum x = ∑' (n : ℕ), x^n / n! :=
tsum_congr (λ n, exp_series_apply_eq_field x n)

lemma exp_eq_tsum : exp 𝕂 𝔸 = (λ x : 𝔸, ∑' (n : ℕ), (1 / n! : 𝕂) • x^n) :=
funext exp_series_sum_eq

lemma exp_eq_tsum_field : exp 𝕂 𝕂 = (λ x : 𝕂, ∑' (n : ℕ), x^n / n!) :=
funext exp_series_sum_eq_field

lemma exp_zero : exp 𝕂 𝔸 0 = 1 :=
begin
  suffices : (λ x : 𝔸, ∑' (n : ℕ), (1 / n! : 𝕂) • x^n) 0 = ∑' (n : ℕ), if n = 0 then 1 else 0,
  { have key : ∀ n ∉ ({0} : finset ℕ), (if n = 0 then (1 : 𝔸) else 0) = 0,
      from λ n hn, if_neg (finset.not_mem_singleton.mp hn),
    rw [exp_eq_tsum, this, tsum_eq_sum key, finset.sum_singleton],
    simp },
  refine tsum_congr (λ n, _),
  split_ifs with h h;
  simp [h]
end

lemma norm_exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
(exp_series 𝕂 𝔸).summable_norm_apply hx

lemma norm_exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥(1 / n! : 𝕂) • x^n∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq',
  exact norm_exp_series_summable_of_mem_ball x hx
end

lemma norm_exp_series_field_summable_of_mem_ball (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  summable (λ n, ∥x^n / n!∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq_field',
  exact norm_exp_series_summable_of_mem_ball x hx
end

section complete_algebra

variables [complete_space 𝔸]

lemma exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

lemma exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, (1 / n! : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

lemma exp_series_field_summable_of_mem_ball [complete_space 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_field_summable_of_mem_ball x hx)

lemma exp_series_has_sum_exp_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 𝔸 x) :=
formal_multilinear_series.has_sum (exp_series 𝕂 𝔸) hx

lemma exp_series_has_sum_exp_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, (1 / n! : 𝕂) • x^n) (exp 𝕂 𝔸 x):=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma exp_series_field_has_sum_exp_of_mem_ball [complete_space 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) : has_sum (λ n, x^n / n!) (exp 𝕂 𝕂 x) :=
begin
  rw ← exp_series_apply_eq_field',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_on_ball (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 (exp_series 𝕂 𝔸).radius :=
(exp_series 𝕂 𝔸).has_fpower_series_on_ball h

lemma has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_at (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 :=
(has_fpower_series_on_ball_exp_of_radius_pos h).has_fpower_series_at

lemma continuous_on_exp :
  continuous_on (exp 𝕂 𝔸) (emetric.ball 0 (exp_series 𝕂 𝔸).radius) :=
formal_multilinear_series.continuous_on

lemma analytic_at_exp_of_mem_ball (x : 𝔸) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  analytic_at 𝕂 (exp 𝕂 𝔸) x:=
begin
  by_cases h : (exp_series 𝕂 𝔸).radius = 0,
  { rw h at hx, exact (ennreal.not_lt_zero hx).elim },
  { have h := pos_iff_ne_zero.mpr h,
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx }
end

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add_of_commute_of_mem_ball [char_zero 𝕂]
  {x y : 𝔸} (hxy : commute x y) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
begin
  rw [exp_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (norm_exp_series_summable_of_mem_ball' x hx) (norm_exp_series_summable_of_mem_ball' y hy)],
  dsimp only,
  conv_lhs {congr, funext, rw [hxy.add_pow' _, finset.smul_sum]},
  refine tsum_congr (λ n, finset.sum_congr rfl $ λ kl hkl, _),
  rw [nsmul_eq_smul_cast 𝕂, smul_smul, smul_mul_smul, ← (finset.nat.mem_antidiagonal.mp hkl),
      nat.cast_add_choose, (finset.nat.mem_antidiagonal.mp hkl)],
  congr' 1,
  have : (n! : 𝕂) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero,
  field_simp [this]
end

end complete_algebra

end any_field_any_algebra

section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)` for all `x`, `y` in the disk of convergence. -/
lemma exp_add_of_mem_ball [char_zero 𝕂] {x y : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_commute_of_mem_ball (commute.all x y) hx hy

end any_field_comm_algebra

section is_R_or_C

section any_algebra

variables (𝕂 𝔸 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
lemma exp_series_radius_eq_top : (exp_series 𝕂 𝔸).radius = ∞ :=
begin
  refine (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial r) _,
  filter_upwards [eventually_cofinite_ne 0],
  intros n hn,
  rw [norm_mul, norm_norm (exp_series 𝕂 𝔸 n), exp_series, norm_smul, norm_div, norm_one, norm_pow,
      nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ←mul_assoc, ←mul_div_assoc, mul_one],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_radius_pos : 0 < (exp_series 𝕂 𝔸).radius :=
begin
  rw exp_series_radius_eq_top,
  exact with_top.zero_lt_top
end

variables {𝕂 𝔸}

section complete_algebra

lemma norm_exp_series_summable (x : 𝔸) : summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_summable' (x : 𝔸) : summable (λ n, ∥(1 / n! : 𝕂) • x^n∥) :=
norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_field_summable (x : 𝕂) : summable (λ n, ∥x^n / n!∥) :=
norm_exp_series_field_summable_of_mem_ball x
  ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

variables [complete_space 𝔸]

lemma exp_series_summable (x : 𝔸) : summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable x)

lemma exp_series_summable' (x : 𝔸) : summable (λ n, (1 / n! : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable' x)

lemma exp_series_field_summable (x : 𝕂) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_field_summable x)

lemma exp_series_has_sum_exp (x : 𝔸) : has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 𝔸 x) :=
exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_has_sum_exp' (x : 𝔸) : has_sum (λ n, (1 / n! : 𝕂) • x^n) (exp 𝕂 𝔸 x):=
exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_field_has_sum_exp (x : 𝕂) : has_sum (λ n, x^n / n!) (exp 𝕂 𝕂 x):=
exp_series_field_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

lemma exp_has_fpower_series_on_ball :
  has_fpower_series_on_ball (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 ∞ :=
exp_series_radius_eq_top 𝕂 𝔸 ▸
  has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

lemma exp_has_fpower_series_at_zero :
  has_fpower_series_at (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 :=
exp_has_fpower_series_on_ball.has_fpower_series_at

lemma exp_continuous :
  continuous (exp 𝕂 𝔸) :=
begin
  rw [continuous_iff_continuous_on_univ, ← metric.eball_top_eq_univ (0 : 𝔸),
      ← exp_series_radius_eq_top 𝕂 𝔸],
  exact continuous_on_exp
end

lemma exp_analytic (x : 𝔸) :
  analytic_at 𝕂 (exp 𝕂 𝔸) x :=
analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end complete_algebra

local attribute [instance] char_zero_R_or_C

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add_of_commute [complete_space 𝔸]
  {x y : 𝔸} (hxy : commute x y) :
  exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end any_algebra

section comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

local attribute [instance] char_zero_R_or_C

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
lemma exp_add {x y : 𝔸} : exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y) :=
exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end comm_algebra

end is_R_or_C

section scalar_tower

variables (𝕂 𝕂' 𝔸 : Type*) [nondiscrete_normed_field 𝕂] [nondiscrete_normed_field 𝕂']
  [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂' 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
lemma exp_series_eq_exp_series (n : ℕ) (x : 𝔸) :
  (exp_series 𝕂 𝔸 n (λ _, x)) = (exp_series 𝕂' 𝔸 n (λ _, x)) :=
by rw [exp_series, exp_series,
       smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
       smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
       one_div, one_div, inv_nat_cast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
lemma exp_eq_exp : exp 𝕂 𝔸 = exp 𝕂' 𝔸 :=
begin
  ext,
  rw [exp, exp],
  refine tsum_congr (λ n, _),
  rw exp_series_eq_exp_series 𝕂 𝕂' 𝔸 n x
end

lemma exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
exp_eq_exp ℝ ℂ ℂ

end scalar_tower
