/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import analysis.specific_limits.basic
import analysis.analytic.basic
import analysis.complex.basic
import data.nat.choose.cast
import data.finset.noncomm_prod

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 : 𝔸 → 𝔸`, the exponential map in a topological algebra `𝔸` over a
field `𝕂`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `exp` independent of a particular choice of norm. The definition also
does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring, then given an
  element `x` in the disk of convergence, we have `exp 𝕂 (-x) = (exp 𝕂 x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`
  for any `x` and `y`
- `exp_neg` : if `𝔸` is a division ring, then we have `exp 𝕂 (-x) = (exp 𝕂 x)⁻¹`.
- `exp_sum_of_commute` : the analogous result to `exp_add_of_commute` for `finset.sum`.
- `exp_sum` : the analogous result to `exp_add` for `finset.sum`.
- `exp_nsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.
- `exp_zsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 = exp 𝕂' 𝔸`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topological_space big_operators ennreal

section topological_algebra

variables (𝕂 𝔸 : Type*) [field 𝕂] [ring 𝔸] [algebra 𝕂 𝔸] [topological_space 𝔸]
  [topological_ring 𝔸]

/-- `exp_series 𝕂 𝔸` is the `formal_multilinear_series` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `exp 𝕂 : 𝔸 → 𝔸`. -/
def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
λ n, (n!⁻¹ : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

variables {𝔸}

/-- `exp 𝕂 : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`.

Note that when `𝔸 = matrix n n 𝕂`, this is the **Matrix Exponential**; see
[`analysis.normed_space.matrix_exponential`](../matrix_exponential) for lemmas specific to that
case. -/
noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂}

lemma exp_series_apply_eq (x : 𝔸) (n : ℕ) : exp_series 𝕂 𝔸 n (λ _, x) = (n!⁻¹ : 𝕂) • x^n :=
by simp [exp_series]

lemma exp_series_apply_eq' (x : 𝔸) :
  (λ n, exp_series 𝕂 𝔸 n (λ _, x)) = (λ n, (n!⁻¹ : 𝕂) • x^n) :=
funext (exp_series_apply_eq x)

lemma exp_series_sum_eq (x : 𝔸) : (exp_series 𝕂 𝔸).sum x = ∑' (n : ℕ), (n!⁻¹ : 𝕂) • x^n :=
tsum_congr (λ n, exp_series_apply_eq x n)

lemma exp_eq_tsum : exp 𝕂 = (λ x : 𝔸, ∑' (n : ℕ), (n!⁻¹ : 𝕂) • x^n) :=
funext exp_series_sum_eq

@[simp] lemma exp_zero [t2_space 𝔸] : exp 𝕂 (0 : 𝔸) = 1 :=
begin
  suffices : (λ x : 𝔸, ∑' (n : ℕ), (n!⁻¹ : 𝕂) • x^n) 0 = ∑' (n : ℕ), if n = 0 then 1 else 0,
  { have key : ∀ n ∉ ({0} : finset ℕ), (if n = 0 then (1 : 𝔸) else 0) = 0,
      from λ n hn, if_neg (finset.not_mem_singleton.mp hn),
    rw [exp_eq_tsum, this, tsum_eq_sum key, finset.sum_singleton],
    simp },
  refine tsum_congr (λ n, _),
  split_ifs with h h;
  simp [h]
end

@[simp] lemma exp_op [t2_space 𝔸] (x : 𝔸) :
  exp 𝕂 (mul_opposite.op x) = mul_opposite.op (exp 𝕂 x) :=
by simp_rw [exp, exp_series_sum_eq, ←mul_opposite.op_pow, ←mul_opposite.op_smul, tsum_op]

@[simp] lemma exp_unop [t2_space 𝔸] (x : 𝔸ᵐᵒᵖ) :
  exp 𝕂 (mul_opposite.unop x) = mul_opposite.unop (exp 𝕂 x) :=
by simp_rw [exp, exp_series_sum_eq, ←mul_opposite.unop_pow, ←mul_opposite.unop_smul, tsum_unop]

lemma star_exp [t2_space 𝔸] [star_ring 𝔸] [has_continuous_star 𝔸] (x : 𝔸) :
  star (exp 𝕂 x) = exp 𝕂 (star x) :=
by simp_rw [exp_eq_tsum, ←star_pow, ←star_inv_nat_cast_smul, ←tsum_star]

variables (𝕂)

lemma commute.exp_right [t2_space 𝔸] {x y : 𝔸} (h : commute x y) : commute x (exp 𝕂 y) :=
begin
  rw exp_eq_tsum,
  exact commute.tsum_right x (λ n, (h.pow_right n).smul_right _),
end

lemma commute.exp_left [t2_space 𝔸] {x y : 𝔸} (h : commute x y) : commute (exp 𝕂 x) y :=
(h.symm.exp_right 𝕂).symm

lemma commute.exp [t2_space 𝔸] {x y : 𝔸} (h : commute x y) : commute (exp 𝕂 x) (exp 𝕂 y) :=
(h.exp_left _).exp_right _

end topological_algebra

section topological_division_algebra
variables {𝕂 𝔸 : Type*} [field 𝕂] [division_ring 𝔸] [algebra 𝕂 𝔸] [topological_space 𝔸]
  [topological_ring 𝔸]

lemma exp_series_apply_eq_div (x : 𝔸) (n : ℕ) : exp_series 𝕂 𝔸 n (λ _, x) = x^n / n! :=
by rw [div_eq_mul_inv, ←(nat.cast_commute n! (x ^ n)).inv_left₀.eq, ←smul_eq_mul,
    exp_series_apply_eq, inv_nat_cast_smul_eq _ _ _ _]

lemma exp_series_apply_eq_div' (x : 𝔸) : (λ n, exp_series 𝕂 𝔸 n (λ _, x)) = (λ n, x^n / n!) :=
funext (exp_series_apply_eq_div x)

lemma exp_series_sum_eq_div (x : 𝔸) : (exp_series 𝕂 𝔸).sum x = ∑' (n : ℕ), x^n / n! :=
tsum_congr (exp_series_apply_eq_div x)

lemma exp_eq_tsum_div : exp 𝕂 = (λ x : 𝔸, ∑' (n : ℕ), x^n / n!) :=
funext exp_series_sum_eq_div

end topological_division_algebra

section normed

section any_field_any_algebra

variables {𝕂 𝔸 𝔹 : Type*} [nondiscrete_normed_field 𝕂]
variables [normed_ring 𝔸] [normed_ring 𝔹] [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂 𝔹]

lemma norm_exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
(exp_series 𝕂 𝔸).summable_norm_apply hx

lemma norm_exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥(n!⁻¹ : 𝕂) • x^n∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq',
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
  summable (λ n, (n!⁻¹ : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

lemma exp_series_has_sum_exp_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 x) :=
formal_multilinear_series.has_sum (exp_series 𝕂 𝔸) hx

lemma exp_series_has_sum_exp_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_sum (λ n, (n!⁻¹ : 𝕂) • x^n) (exp 𝕂 x):=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_on_ball (exp 𝕂) (exp_series 𝕂 𝔸) 0 (exp_series 𝕂 𝔸).radius :=
(exp_series 𝕂 𝔸).has_fpower_series_on_ball h

lemma has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_at (exp 𝕂) (exp_series 𝕂 𝔸) 0 :=
(has_fpower_series_on_ball_exp_of_radius_pos h).has_fpower_series_at

lemma continuous_on_exp :
  continuous_on (exp 𝕂 : 𝔸 → 𝔸) (emetric.ball 0 (exp_series 𝕂 𝔸).radius) :=
formal_multilinear_series.continuous_on

lemma analytic_at_exp_of_mem_ball (x : 𝔸) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  analytic_at 𝕂 (exp 𝕂) x:=
begin
  by_cases h : (exp_series 𝕂 𝔸).radius = 0,
  { rw h at hx, exact (ennreal.not_lt_zero hx).elim },
  { have h := pos_iff_ne_zero.mpr h,
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx }
end

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
lemma exp_add_of_commute_of_mem_ball [char_zero 𝕂]
  {x y : 𝔸} (hxy : commute x y) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y) :=
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

/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def invertible_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) : invertible (exp 𝕂 x) :=
{ inv_of := exp 𝕂 (-x),
  inv_of_mul_self := begin
    have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius,
    { rw [emetric.mem_ball, ←neg_zero, edist_neg_neg],
      exact hx },
    rw [←exp_add_of_commute_of_mem_ball (commute.neg_left $ commute.refl x) hnx hx, neg_add_self,
      exp_zero],
  end,
  mul_inv_of_self := begin
    have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius,
    { rw [emetric.mem_ball, ←neg_zero, edist_neg_neg],
      exact hx },
    rw [←exp_add_of_commute_of_mem_ball (commute.neg_right $ commute.refl x) hx hnx, add_neg_self,
      exp_zero],
  end }

lemma is_unit_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) : is_unit (exp 𝕂 x) :=
@is_unit_of_invertible _ _ _ (invertible_exp_of_mem_ball hx)

lemma inv_of_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) [invertible (exp 𝕂 x)] :
  ⅟(exp 𝕂 x) = exp 𝕂 (-x) :=
by { letI := invertible_exp_of_mem_ball hx, convert (rfl : ⅟(exp 𝕂 x) = _) }

/-- Any continuous ring homomorphism commutes with `exp`. -/
lemma map_exp_of_mem_ball {F} [ring_hom_class F 𝔸 𝔹] (f : F) (hf : continuous f) (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  f (exp 𝕂 x) = exp 𝕂 (f x) :=
begin
  rw [exp_eq_tsum, exp_eq_tsum],
  refine ((exp_series_summable_of_mem_ball' _ hx).has_sum.map f hf).tsum_eq.symm.trans _,
  dsimp only [function.comp],
  simp_rw [one_div, map_inv_nat_cast_smul f 𝕂 𝕂, map_pow],
end

end complete_algebra

lemma algebra_map_exp_comm_of_mem_ball [complete_space 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  algebra_map 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebra_map 𝕂 𝔸 x) :=
map_exp_of_mem_ball _ (algebra_map_clm _ _).continuous _ hx

end any_field_any_algebra

section any_field_division_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_division_ring 𝔸] [normed_algebra 𝕂 𝔸]

variables (𝕂)

lemma norm_exp_series_div_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  summable (λ n, ∥x^n / n!∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq_div' x,
  exact norm_exp_series_summable_of_mem_ball x hx
end

lemma exp_series_div_summable_of_mem_ball [complete_space 𝔸] (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_div_summable_of_mem_ball 𝕂 x hx)

lemma exp_series_div_has_sum_exp_of_mem_ball [complete_space 𝔸] (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) : has_sum (λ n, x^n / n!) (exp 𝕂 x) :=
begin
  rw ← exp_series_apply_eq_div' x,
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

variables {𝕂}

lemma exp_neg_of_mem_ball [char_zero 𝕂] [complete_space 𝔸] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
begin
  letI := invertible_exp_of_mem_ball hx,
  exact inv_of_eq_inv (exp 𝕂 x),
end

end any_field_division_algebra


section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)` for all `x`, `y` in the disk of convergence. -/
lemma exp_add_of_mem_ball [char_zero 𝕂] {x y : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y) :=
exp_add_of_commute_of_mem_ball (commute.all x y) hx hy

end any_field_comm_algebra

section is_R_or_C

section any_algebra

variables (𝕂 𝔸 𝔹 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
variables [normed_ring 𝔹] [normed_algebra 𝕂 𝔹]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
lemma exp_series_radius_eq_top : (exp_series 𝕂 𝔸).radius = ∞ :=
begin
  refine (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial r) _,
  filter_upwards [eventually_cofinite_ne 0] with n hn,
  rw [norm_mul, norm_norm (exp_series 𝕂 𝔸 n), exp_series, norm_smul, norm_inv, norm_pow,
      nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ←mul_assoc, ←div_eq_mul_inv],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_radius_pos : 0 < (exp_series 𝕂 𝔸).radius :=
begin
  rw exp_series_radius_eq_top,
  exact with_top.zero_lt_top
end

variables {𝕂 𝔸 𝔹}

lemma norm_exp_series_summable (x : 𝔸) : summable (λ n, ∥exp_series 𝕂 𝔸 n (λ _, x)∥) :=
norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_summable' (x : 𝔸) : summable (λ n, ∥(n!⁻¹ : 𝕂) • x^n∥) :=
norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

section complete_algebra

variables [complete_space 𝔸]

lemma exp_series_summable (x : 𝔸) : summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable x)

lemma exp_series_summable' (x : 𝔸) : summable (λ n, (n!⁻¹ : 𝕂) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable' x)

lemma exp_series_has_sum_exp (x : 𝔸) : has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 x) :=
exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_has_sum_exp' (x : 𝔸) : has_sum (λ n, (n!⁻¹ : 𝕂) • x^n) (exp 𝕂 x):=
exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_has_fpower_series_on_ball :
  has_fpower_series_on_ball (exp 𝕂) (exp_series 𝕂 𝔸) 0 ∞ :=
exp_series_radius_eq_top 𝕂 𝔸 ▸
  has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

lemma exp_has_fpower_series_at_zero :
  has_fpower_series_at (exp 𝕂) (exp_series 𝕂 𝔸) 0 :=
exp_has_fpower_series_on_ball.has_fpower_series_at

lemma exp_continuous : continuous (exp 𝕂 : 𝔸 → 𝔸) :=
begin
  rw [continuous_iff_continuous_on_univ, ← metric.eball_top_eq_univ (0 : 𝔸),
      ← exp_series_radius_eq_top 𝕂 𝔸],
  exact continuous_on_exp
end

lemma exp_analytic (x : 𝔸) :
  analytic_at 𝕂 (exp 𝕂) x :=
analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
lemma exp_add_of_commute
  {x y : 𝔸} (hxy : commute x y) :
  exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y) :=
exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

section
variables (𝕂)

/-- `exp 𝕂 x` has explicit two-sided inverse `exp 𝕂 (-x)`. -/
noncomputable def invertible_exp (x : 𝔸) : invertible (exp 𝕂 x) :=
invertible_exp_of_mem_ball $ (exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

lemma is_unit_exp (x : 𝔸) : is_unit (exp 𝕂 x) :=
is_unit_exp_of_mem_ball $ (exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

lemma inv_of_exp (x : 𝔸) [invertible (exp 𝕂 x)] :
  ⅟(exp 𝕂 x) = exp 𝕂 (-x) :=
inv_of_exp_of_mem_ball $ (exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

lemma ring.inverse_exp (x : 𝔸) : ring.inverse (exp 𝕂 x) = exp 𝕂 (-x) :=
begin
  letI := invertible_exp 𝕂 x,
  exact ring.inverse_invertible _,
end

end

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `exp 𝕂 (∑ i, f i) = ∏ i, exp 𝕂 (f i)`. -/
lemma exp_sum_of_commute {ι} (s : finset ι) (f : ι → 𝔸)
  (h : ∀ (i ∈ s) (j ∈ s), commute (f i) (f j)) :
  exp 𝕂 (∑ i in s, f i) = s.noncomm_prod (λ i, exp 𝕂 (f i))
    (λ i hi j hj, (h i hi j hj).exp 𝕂) :=
begin
  classical,
  induction s using finset.induction_on with a s ha ih,
  { simp },
  rw [finset.noncomm_prod_insert_of_not_mem _ _ _ _ ha, finset.sum_insert ha,
      exp_add_of_commute, ih],
  refine commute.sum_right _ _ _ _,
  intros i hi,
  exact h _ (finset.mem_insert_self _ _) _ (finset.mem_insert_of_mem hi),
end

lemma exp_nsmul (n : ℕ) (x : 𝔸) :
  exp 𝕂 (n • x) = exp 𝕂 x ^ n :=
begin
  induction n with n ih,
  { rw [zero_smul, pow_zero, exp_zero], },
  { rw [succ_nsmul, pow_succ, exp_add_of_commute ((commute.refl x).smul_right n), ih] }
end

variables (𝕂)

/-- Any continuous ring homomorphism commutes with `exp`. -/
lemma map_exp {F} [ring_hom_class F 𝔸 𝔹] (f : F) (hf : continuous f) (x : 𝔸) :
  f (exp 𝕂 x) = exp 𝕂 (f x) :=
map_exp_of_mem_ball f hf x $ (exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

lemma exp_smul {G} [monoid G] [mul_semiring_action G 𝔸] [has_continuous_const_smul G 𝔸]
  (g : G) (x : 𝔸) :
  exp 𝕂 (g • x) = g • exp 𝕂 x :=
(map_exp 𝕂 (mul_semiring_action.to_ring_hom G 𝔸 g) (continuous_const_smul _) x).symm

lemma exp_units_conj (y : 𝔸ˣ) (x : 𝔸)  :
  exp 𝕂 (y * x * ↑(y⁻¹) : 𝔸) = y * exp 𝕂 x * ↑(y⁻¹) :=
exp_smul _ (conj_act.to_conj_act y) x

lemma exp_units_conj' (y : 𝔸ˣ) (x : 𝔸)  :
  exp 𝕂 (↑(y⁻¹) * x * y) = ↑(y⁻¹) * exp 𝕂 x * y :=
exp_units_conj _ _ _

@[simp] lemma prod.fst_exp [complete_space 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).fst = exp 𝕂 x.fst :=
map_exp _ (ring_hom.fst 𝔸 𝔹) continuous_fst x

@[simp] lemma prod.snd_exp [complete_space 𝔹] (x : 𝔸 × 𝔹) : (exp 𝕂 x).snd = exp 𝕂 x.snd :=
map_exp _ (ring_hom.snd 𝔸 𝔹) continuous_snd x

@[simp] lemma pi.exp_apply {ι : Type*} {𝔸 : ι → Type*} [fintype ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra 𝕂 (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) (i : ι) :
  exp 𝕂 x i = exp 𝕂 (x i) :=
begin
  -- Lean struggles to infer this instance due to it wanting `[Π i, semi_normed_ring (𝔸 i)]`
  letI : normed_algebra 𝕂 (Π i, 𝔸 i) := pi.normed_algebra _,
  exact map_exp _ (pi.eval_ring_hom 𝔸 i) (continuous_apply _) x
end

lemma pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [fintype ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra 𝕂 (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) :
  exp 𝕂 x = λ i, exp 𝕂 (x i) :=
funext $ pi.exp_apply 𝕂 x

lemma function.update_exp {ι : Type*} {𝔸 : ι → Type*} [fintype ι] [decidable_eq ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra 𝕂 (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) (j : ι) (xj : 𝔸 j) :
  function.update (exp 𝕂 x) j (exp 𝕂 xj) = exp 𝕂 (function.update x j xj) :=
begin
  ext i,
  simp_rw [pi.exp_def],
  exact (function.apply_update (λ i, exp 𝕂) x j xj i).symm,
end

end complete_algebra

lemma algebra_map_exp_comm (x : 𝕂) :
  algebra_map 𝕂 𝔸 (exp 𝕂 x) = exp 𝕂 (algebra_map 𝕂 𝔸 x) :=
algebra_map_exp_comm_of_mem_ball x $
  (exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

end any_algebra

section division_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_division_ring 𝔸] [normed_algebra 𝕂 𝔸]

variables (𝕂)

lemma norm_exp_series_div_summable (x : 𝔸) : summable (λ n, ∥x^n / n!∥) :=
norm_exp_series_div_summable_of_mem_ball 𝕂 x
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

variables [complete_space 𝔸]

lemma exp_series_div_summable (x : 𝔸) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_div_summable 𝕂 x)

lemma exp_series_div_has_sum_exp (x : 𝔸) : has_sum (λ n, x^n / n!) (exp 𝕂 x):=
exp_series_div_has_sum_exp_of_mem_ball 𝕂 x
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

variables {𝕂}

lemma exp_neg (x : 𝔸) : exp 𝕂 (-x) = (exp 𝕂 x)⁻¹ :=
exp_neg_of_mem_ball $ (exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

lemma exp_zsmul (z : ℤ) (x : 𝔸) : exp 𝕂 (z • x) = (exp 𝕂 x) ^ z :=
begin
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
  { rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul] },
  { rw [zpow_neg₀, zpow_coe_nat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul] },
end

lemma exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) :
  exp 𝕂 (y * x * y⁻¹) = y * exp 𝕂 x * y⁻¹ :=
exp_units_conj _ (units.mk0 y hy) x

lemma exp_conj' (y : 𝔸) (x : 𝔸)  (hy : y ≠ 0) :
  exp 𝕂 (y⁻¹ * x * y) = y⁻¹ * exp 𝕂 x * y :=
exp_units_conj' _ (units.mk0 y hy) x

end division_algebra

section comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 (x+y) = (exp 𝕂 x) * (exp 𝕂 y)`. -/
lemma exp_add {x y : 𝔸} : exp 𝕂 (x + y) = (exp 𝕂 x) * (exp 𝕂 y) :=
exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- A version of `exp_sum_of_commute` for a commutative Banach-algebra. -/
lemma exp_sum {ι} (s : finset ι) (f : ι → 𝔸) :
  exp 𝕂 (∑ i in s, f i) = ∏ i in s, exp 𝕂 (f i) :=
begin
  rw [exp_sum_of_commute, finset.noncomm_prod_eq_prod],
  exact λ i hi j hj, commute.all _ _,
end

end comm_algebra

end is_R_or_C

end normed

section scalar_tower

variables (𝕂 𝕂' 𝔸 : Type*) [field 𝕂] [field 𝕂'] [ring 𝔸] [algebra 𝕂 𝔸] [algebra 𝕂' 𝔸]
  [topological_space 𝔸] [topological_ring 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
lemma exp_series_eq_exp_series (n : ℕ) (x : 𝔸) :
  (exp_series 𝕂 𝔸 n (λ _, x)) = (exp_series 𝕂' 𝔸 n (λ _, x)) :=
by rw [exp_series_apply_eq, exp_series_apply_eq, inv_nat_cast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
lemma exp_eq_exp : (exp 𝕂 : 𝔸 → 𝔸) = exp 𝕂' :=
begin
  ext,
  rw [exp, exp],
  refine tsum_congr (λ n, _),
  rw exp_series_eq_exp_series 𝕂 𝕂' 𝔸 n x
end

lemma exp_ℝ_ℂ_eq_exp_ℂ_ℂ : (exp ℝ : ℂ → ℂ) = exp ℂ :=
exp_eq_exp ℝ ℂ ℂ

end scalar_tower
