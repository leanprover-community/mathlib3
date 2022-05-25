/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.polynomial.algebra_map
import data.nat.choose.cast
import number_theory.bernoulli

/-!
# Bernoulli polynomials

The Bernoulli polynomials (defined here : https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k * B_k * X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ t * e^{tX} / (e^t - 1) = ∑_{n = 0}^{\infty} B_n(X) * \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to n is `(n + 1) * X^n`.
- `bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

## TODO

- `bernoulli_eval_one_neg` : $$ B_n(1 - x) = (-1)^n*B_n(x) $$

-/

noncomputable theory
open_locale big_operators
open_locale nat polynomial

open nat finset

namespace polynomial

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i in range (n + 1), polynomial.monomial (n - i) ((_root_.bernoulli i) * (choose n i))

lemma bernoulli_def (n : ℕ) : bernoulli n =
  ∑ i in range (n + 1), polynomial.monomial i ((_root_.bernoulli (n - i)) * (choose n i)) :=
begin
  rw [←sum_range_reflect, add_succ_sub_one, add_zero, bernoulli],
  apply sum_congr rfl,
  rintros x hx,
  rw mem_range_succ_iff at hx, rw [choose_symm hx, tsub_tsub_cancel_of_le hx],
end

/-
### examples
-/

section examples

@[simp] lemma bernoulli_zero : bernoulli 0 = 1 :=
by simp [bernoulli]

@[simp] lemma bernoulli_eval_zero (n : ℕ) : (bernoulli n).eval 0 = _root_.bernoulli n :=
begin
 rw [bernoulli, polynomial.eval_finset_sum, sum_range_succ],
  have : ∑ (x : ℕ) in range n, _root_.bernoulli x * (n.choose x) * 0 ^ (n - x) = 0,
  { apply sum_eq_zero (λ x hx, _),
    have h : 0 < n - x := tsub_pos_of_lt (mem_range.1 hx),
    simp [h] },
  simp [this],
end

@[simp] lemma bernoulli_eval_one (n : ℕ) : (bernoulli n).eval 1 = _root_.bernoulli' n :=
begin
  simp only [bernoulli, polynomial.eval_finset_sum],
  simp only [←succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, polynomial.eval_C,
    polynomial.eval_monomial],
  by_cases h : n = 1,
  { norm_num [h], },
  { simp [h],
    exact bernoulli_eq_bernoulli'_of_ne_one h, }
end

end examples

@[simp] theorem sum_bernoulli (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli k =
    polynomial.monomial n (n + 1 : ℚ) :=
begin
 simp_rw [bernoulli_def, finset.smul_sum, finset.range_eq_Ico, ←finset.sum_Ico_Ico_comm,
    finset.sum_Ico_eq_sum_range],
  simp only [cast_succ, add_tsub_cancel_left, tsub_zero, zero_add, linear_map.map_add],
  simp_rw [polynomial.smul_monomial, mul_comm (_root_.bernoulli _) _, smul_eq_mul, ←mul_assoc],
  conv_lhs { apply_congr, skip, conv
    { apply_congr, skip,
      rw [← nat.cast_mul, choose_mul ((le_tsub_iff_left $ mem_range_le H).1
        $ mem_range_le H_1) (le.intro rfl), nat.cast_mul, add_comm x x_1, add_tsub_cancel_right,
        mul_assoc, mul_comm, ←smul_eq_mul, ←polynomial.smul_monomial] },
    rw [←sum_smul], },
  rw [sum_range_succ_comm],
  simp only [add_right_eq_self, cast_succ, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_zero, sum_singleton, zero_add,
    linear_map.map_add, range_one],
  apply sum_eq_zero (λ x hx, _),
  have f : ∀ x ∈ range n, ¬ n + 1 - x = 1,
  { rintros x H, rw [mem_range] at H,
    rw [eq_comm],
    exact ne_of_lt (nat.lt_of_lt_of_le one_lt_two (le_tsub_of_add_le_left (succ_le_succ H))) },
  rw [sum_bernoulli],
  have g : (ite (n + 1 - x = 1) (1 : ℚ) 0) = 0,
  { simp only [ite_eq_right_iff, one_ne_zero],
    intro h₁,
    exact (f x hx) h₁, },
  rw [g, zero_smul],
end

/-- Another version of `polynomial.sum_bernoulli`. -/
lemma bernoulli_eq_sub_sum (n : ℕ) : (n.succ : ℚ) • bernoulli n =
  polynomial.monomial n (n.succ : ℚ) -
  ∑ k in finset.range n, ((n + 1).choose k : ℚ) • bernoulli k :=
begin
  change _ = (polynomial.monomial n) ((n : ℚ) + 1) - ∑ (k : ℕ) in range n,
    ↑((n + 1).choose k) • bernoulli k,
  rw [←sum_bernoulli n, sum_range_succ, add_comm],
  simp only [cast_succ, choose_succ_self_right, add_sub_cancel],
end

/-- Another version of `bernoulli.sum_range_pow`. -/
lemma sum_range_pow_eq_bernoulli_sub (n p : ℕ) :
  (p  + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p = (bernoulli p.succ).eval n -
  (_root_.bernoulli p.succ) :=
begin
  rw [sum_range_pow, bernoulli_def, polynomial.eval_finset_sum, ←sum_div,
    mul_div_cancel' _ _],
  { simp_rw [polynomial.eval_monomial],
    symmetry,
    rw [←sum_flip _, sum_range_succ],
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, pow_zero,
      add_tsub_cancel_right],
    apply sum_congr rfl (λ x hx, _),
    apply congr_arg2 _ (congr_arg2 _ _ _) rfl,
    { rw nat.sub_sub_self (mem_range_le hx), },
    { rw ←choose_symm (mem_range_le hx), }, },
  { norm_cast, apply succ_ne_zero _, },
end

/-- Rearrangement of `polynomial.sum_range_pow_eq_bernoulli_sub`. -/
lemma bernoulli_succ_eval (n p : ℕ) : (bernoulli p.succ).eval n =
  _root_.bernoulli (p.succ) + (p  + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p :=
by { apply eq_add_of_sub_eq', rw sum_range_pow_eq_bernoulli_sub, }

lemma monomial_eval_one_add_sub (d : ℕ) (x : ℚ) :
  eval (1 + x) ((polynomial.monomial d) (succ d : ℚ)) -
  eval x ((polynomial.monomial d) (succ d : ℚ)) =
  ∑ (x_1 : ℕ) in range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * x ^ (x_1 - 1)) :=
begin
  rw [eval_monomial, eval_monomial, add_comm, add_pow],
  conv_lhs { congr, congr, skip, apply_congr, skip, rw [one_pow, mul_one, mul_comm], },
  rw [sum_range_succ, mul_add, choose_self, cast_one, one_mul, add_sub_cancel, mul_sum,
    sum_range_succ', cast_zero, zero_mul, mul_zero, add_zero],
  apply sum_congr rfl (λ y hy, _),
  rw [←mul_assoc, ←mul_assoc, ←cast_mul, succ_mul_choose_eq, cast_mul, nat.add_sub_cancel],
end

lemma bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (bernoulli n).eval (1 + x) = (bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n (λ d hd, _),
  apply (mul_right_inj' _).1,
  swap 3, exact d.succ,
  swap 3, { norm_cast, exact d.succ_ne_zero, },
  rw [← smul_eq_mul, ←polynomial.eval_smul, bernoulli_eq_sub_sum, mul_add, ←smul_eq_mul,
    ←polynomial.eval_smul, bernoulli_eq_sub_sum, polynomial.eval_sub, polynomial.eval_finset_sum],
  conv_lhs { congr, skip, apply_congr, skip, rw [polynomial.eval_smul, hd x_1 (mem_range.1 H)], },
  rw [polynomial.eval_sub, polynomial.eval_finset_sum],
  simp_rw [polynomial.eval_smul, smul_add],
  rw [sum_add_distrib, sub_add, sub_eq_sub_iff_sub_eq_sub, _root_.add_sub_sub_cancel],
  conv_rhs { congr, skip, congr, rw [succ_eq_add_one, ←choose_succ_self_right d], },
  rw [← smul_eq_mul, ←sum_range_succ _ d, polynomial.monomial_eval_one_add_sub],
  simp_rw [smul_eq_mul],
end

open power_series
variables {A : Type*} [comm_ring A] [algebra ℚ A]

-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
theorem bernoulli_generating_function (t : A) :
  mk (λ n, aeval t ((1 / n! : ℚ) • bernoulli n)) * (exp A - 1) =
    power_series.X * rescale t (exp A) :=
begin
  -- check equality of power series by checking coefficients of X^n
  ext n,
  -- n = 0 case solved by `simp`
  cases n, { simp },
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, power_series.coeff_mul,
    nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ],
  -- last term is zero so kill with `add_zero`
  simp only [ring_hom.map_sub, tsub_self, constant_coeff_one, constant_coeff_exp,
    coeff_zero_eq_constant_coeff, mul_zero, sub_self, add_zero],
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  set u : units ℚ := ⟨(n+1)!, (n+1)!⁻¹,
    mul_inv_cancel (by exact_mod_cast factorial_ne_zero (n+1)),
      inv_mul_cancel (by exact_mod_cast factorial_ne_zero (n+1))⟩ with hu,
  rw ←units.mul_right_inj (units.map (algebra_map ℚ A).to_monoid_hom u),
  -- now tidy up unit mess and generally do trivial rearrangements
  -- to make RHS (n+1)*t^n
  rw [units.coe_map, mul_left_comm, ring_hom.to_monoid_hom_eq_coe,
      ring_hom.coe_monoid_hom, ←ring_hom.map_mul, hu, units.coe_mk],
  change _ = t^n * algebra_map ℚ A (((n+1)*n! : ℕ)*(1/n!)),
  rw [cast_mul, mul_assoc, mul_one_div_cancel
    (show (n! : ℚ) ≠ 0, from cast_ne_zero.2 (factorial_ne_zero n)), mul_one, mul_comm (t^n),
    ← polynomial.aeval_monomial, cast_add, cast_one],
  -- But this is the RHS of `sum_bernoulli_poly`
  rw [← sum_bernoulli, finset.mul_sum, alg_hom.map_sum],
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply finset.sum_congr rfl,
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intros i hi,
  -- deal with coefficients of e^X-1
  simp only [nat.cast_choose ℚ (mem_range_le hi), coeff_mk,
    if_neg (mem_range_sub_ne_zero hi), one_div, alg_hom.map_smul, power_series.coeff_one,
    units.coe_mk, coeff_exp, sub_zero, linear_map.map_sub, algebra.smul_mul_assoc, algebra.smul_def,
    mul_right_comm _ ((aeval t) _), ←mul_assoc, ← ring_hom.map_mul, succ_eq_add_one],
  -- finally cancel the Bernoulli polynomial and the algebra_map
  congr',
  apply congr_arg,
  rw [mul_assoc, div_eq_mul_inv, ← mul_inv],
end

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`, using eval instead of aeval. -/
theorem bernoulli_generating_function' (t : ℚ) :
  mk (λ n, polynomial.eval t ((1 / n! : ℚ) • bernoulli n)) * (exp ℚ - 1) =
    power_series.X * rescale t (exp ℚ) :=
begin
  convert bernoulli_generating_function t,
  simp_rw [aeval_def, eval₂_eq_eval_map],
  simp,
end

lemma exp_sub_one_ne_zero : exp ℚ - 1 ≠ 0 :=
begin
  intro this,
  rw power_series.ext_iff at this, specialize this 1,
  simp only [map_sub, coeff_exp, algebra_map_rat_rat, factorial_one, cast_one, div_self, ne.def,
    one_ne_zero, not_false_iff, ring_hom.id_apply, power_series.coeff_one, if_false, sub_zero,
    map_zero] at this,
  assumption,
end

lemma function.smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ, a * (f n)) = a • (λ n : ℕ, f n) :=
by { ext, simp only [smul_eq_mul, pi.smul_apply], }

lemma power_series.mk_smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f :=
by { ext, rw [coeff_mk, power_series.coeff_smul, coeff_mk],
  simp only [smul_eq_mul, pi.smul_apply], }

lemma rescale_mk {R : Type*} [comm_semiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ, a^n * (f n)) :=
by { ext, rw [coeff_rescale, coeff_mk, coeff_mk], }

lemma rescale_comp_eq_mul {R : Type*} [comm_semiring R] (f : power_series R) (a b : R) :
  rescale b (rescale a f) = rescale (a * b) f :=
begin
  ext,
  repeat { rw coeff_rescale, },
  rw [mul_pow, mul_comm _ (b^n), mul_assoc],
end

/-- Bernoulli polynomials multiplication theorem :
  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).  -/
theorem bernoulli_eval_mul' (m : ℕ) {k : ℕ} (hk : k ≠ 0) (x : ℚ) :
  (bernoulli m).eval ((k : ℚ) * x) =
  k^(m - 1 : ℤ) * ∑ i in range k, (bernoulli m).eval (x + i / k) :=
begin
  have coe_hk : (k : ℚ) ≠ 0,
  { simp only [hk, cast_eq_zero, ne.def, not_false_iff], },
  suffices : (∑ i in range k, (power_series.mk (λ n, (k^(n - 1 : ℤ) : ℚ) *
    (polynomial.eval (x + i / k) ((1 / n! : ℚ) • (bernoulli n))) ))) * ((exp ℚ - 1)  *
    (rescale (k : ℚ) (exp ℚ - 1))) = (power_series.mk (λ n, polynomial.eval ((k : ℚ) * x)
    ((1 / n! : ℚ) • bernoulli n))) * ((exp ℚ - 1) * (rescale (k : ℚ) (exp ℚ - 1))),
  { rw mul_eq_mul_right_iff at this, cases this,
    { rw power_series.ext_iff at this,
      simp only [one_div, coeff_mk, polynomial.eval_smul, factorial, linear_map.map_sum] at this,
      specialize this m,
      have symm := this.symm,
      rw inv_smul_eq_iff₀ _ at symm,
      { rw [symm, ←mul_sum, ←smul_mul_assoc, ←smul_sum, smul_eq_mul, smul_eq_mul, ←mul_assoc,
          mul_comm _ (m! : ℚ)⁻¹, ←mul_assoc, inv_mul_cancel _, one_mul],
        { norm_cast, apply factorial_ne_zero _, }, },
      { norm_cast, apply factorial_ne_zero _, }, },
    { exfalso, rw mul_eq_zero at this, cases this,
      { apply exp_sub_one_ne_zero this, },
      { apply exp_sub_one_ne_zero,
        rw ←(rescale (k : ℚ)).map_zero at this,
        apply rescale_injective coe_hk this, }, }, },
  { symmetry, rw [←mul_assoc, bernoulli_generating_function'],
    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n,
    { intro n, rw [zpow_sub_one₀ coe_hk, inv_eq_one_div, mul_comm, zpow_coe_nat], },
    conv_rhs { congr, apply_congr, skip, conv { congr, funext, rw [this, mul_assoc], }, },
    conv_rhs { congr, apply_congr, skip, rw [function.smul, power_series.mk_smul, ←rescale_mk], },
    rw [mul_comm (exp ℚ - 1) _, ←mul_assoc, sum_mul],
    conv_rhs { congr, apply_congr, skip, rw [smul_mul_assoc, ←ring_hom.map_mul,
      bernoulli_generating_function', ring_hom.map_mul, rescale_comp_eq_mul,
      add_div_eq_mul_add_div _ _ coe_hk, div_mul_cancel _ coe_hk, ←exp_mul_exp_eq_exp_add,
      ←mul_assoc, ←smul_mul_assoc, ←exp_pow_eq_rescale_exp], },
    rw [←mul_sum, mul_assoc _ _ (exp ℚ - 1), geom_sum_mul, ←smul_mul_assoc],
    apply congr_arg2, apply congr_arg2,
    { apply power_series.ext (λ n, _), { apply_instance, },
      rw [power_series.coeff_smul, coeff_rescale, power_series.coeff_X],
      rw smul_eq_mul,
      by_cases n = 1,
      { rw [if_pos h, h, mul_one, pow_one, div_mul_cancel _ coe_hk], },
      { rw [if_neg h, mul_zero, mul_zero], }, },
    { rw mul_comm, },
    { rw [ring_hom.map_sub, exp_pow_eq_rescale_exp], congr, apply (rescale (k : ℚ)).map_one', }, },
end

end polynomial
