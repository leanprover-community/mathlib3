/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.hasse_deriv

/-!
# Taylor expansions of polynomials

## Main declarations

* `polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(polynomial.hasse_deriv k f).eval r`
* `polynomial.eq_zero_of_hasse_deriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/

noncomputable theory

namespace polynomial

variables {R : Type*} [semiring R] (r : R) (f : polynomial R)

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : polynomial R →ₗ[R] polynomial R :=
{ to_fun := λ f, f.comp (X + C r),
  map_add' := λ f g, add_comp,
  map_smul' := λ c f, by simp only [smul_eq_C_mul, C_mul_comp, ring_hom.id_apply] }

lemma taylor_apply : taylor r f = f.comp (X + C r) := rfl

@[simp] lemma taylor_X : taylor r X = X + C r :=
by simp only [taylor_apply, X_comp]

@[simp] lemma taylor_C (x : R) : taylor r (C x) = C x :=
by simp only [taylor_apply, C_comp]

@[simp] lemma taylor_one : taylor r (1 : polynomial R) = C 1 :=
by rw [← C_1, taylor_C]

@[simp] lemma taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i :=
by simp [taylor_apply]

/-- The `k`th coefficient of `polynomial.taylor r f` is `(polynomial.hasse_deriv k f).eval r`. -/
lemma taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasse_deriv n f).eval r :=
show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasse_deriv n) f,
begin
  congr' 1, clear f, ext i,
  simp only [leval_apply, mul_one, one_mul, eval_monomial, linear_map.comp_apply, coeff_C_mul,
    hasse_deriv_monomial, taylor_apply, monomial_comp, C_1,
    (commute_X (C r)).add_pow i, linear_map.map_sum],
  simp only [lcoeff_apply, ← C_eq_nat_cast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
    (nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, finset.sum_ite_eq, finset.mem_range],
  split_ifs with h, { refl },
  push_neg at h, rw [nat.choose_eq_zero_of_lt h, nat.cast_zero, mul_zero],
end

@[simp] lemma taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r :=
by rw [taylor_coeff, hasse_deriv_zero, linear_map.id_apply]

@[simp] lemma taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r :=
by rw [taylor_coeff, hasse_deriv_one]

lemma nat_degree_taylor_le (p : polynomial R) (r : R) :
  nat_degree (taylor r p) ≤ nat_degree p :=
begin
  rw nat_degree_le_iff_coeff_eq_zero,
  intros y hy,
  rw [taylor_coeff, hasse_deriv_eq_zero_of_lt_nat_degree _ _ hy, eval_zero]
end

@[simp] lemma nat_degree_taylor (p : polynomial R) (r : R) :
  nat_degree (taylor r p) = nat_degree p :=
begin
  refine le_antisymm (nat_degree_taylor_le _ _) _,
  rcases eq_or_ne p 0 with rfl|hp,
  { simp },
  nontriviality R,
  classical,
  rw [taylor_apply, comp_eq_sum_left, nat_degree_le_iff_coeff_eq_zero, sum_def,
      nat_degree_sum_eq_of_disjoint],
  { rintros (_|y) hy,
    { simpa using hy },
    rw finset.sup_lt_iff (nat.zero_lt_succ _) at hy,
    specialize hy (p.nat_degree) (nat_degree_mem_support_of_nonzero hp),
    rw [nat_degree_mul', nat_degree_pow', nat_degree_C, zero_add, nat_degree_X_add_C,
        mul_one] at hy,
    { exact coeff_eq_zero_of_nat_degree_lt hy },
    { simp },
    { simp [hp] } },
  { intros x hx y hy h hxy,
    simp only [set.mem_sep_eq, mem_support_iff, ne.def, finset.mem_coe,
               finset.coe_filter] at hx hy,
    simp only [function.comp_app] at hxy,
    rw [nat_degree_C_mul_eq_of_mul_ne_zero, nat_degree_C_mul_eq_of_mul_ne_zero,
        nat_degree_pow', nat_degree_pow',
        nat_degree_add_eq_left_of_nat_degree_lt] at hxy,
    { simpa [h] using hxy },
    { simp },
    { simp },
    { simp },
    { simpa using hy.left },
    { simpa using hx.left } }
end

@[simp] lemma taylor_mul {R} [comm_semiring R] (r : R) (p q : polynomial R) :
  taylor r (p * q) = taylor r p * taylor r q :=
by simp only [taylor_apply, mul_comp]

lemma taylor_eval {R} [comm_semiring R] (r : R) (f : polynomial R) (s : R) :
  (taylor r f).eval s = f.eval (s + r) :=
by simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

lemma taylor_eval_sub {R} [comm_ring R] (r : R) (f : polynomial R) (s : R) :
  (taylor r f).eval (s - r) = f.eval s :=
by rw [taylor_eval, sub_add_cancel]

lemma taylor_injective {R} [comm_ring R] (r : R) : function.injective (taylor r) :=
begin
  intros f g h,
  apply_fun taylor (-r) at h,
  simpa only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, C_neg,
    neg_add_cancel_right, comp_X] using h,
end

lemma eq_zero_of_hasse_deriv_eq_zero {R} [comm_ring R] (f : polynomial R) (r : R)
  (h : ∀ k, (hasse_deriv k f).eval r = 0) :
  f = 0 :=
begin
  apply taylor_injective r,
  rw linear_map.map_zero,
  ext k,
  simp only [taylor_coeff, h, coeff_zero],
end

lemma sum_taylor_X_pow {R} [comm_ring R] (r : R) (n : ℕ) :
  (taylor r (X ^ n)).sum (λ i a, C a * (X - C r) ^ i) = X ^ n :=
begin
  nontriviality R,
  rw sum_over_range,
  { rw nat_degree_taylor,
    nth_rewrite_rhs 0 ←sub_add_cancel X (C r),
    rw add_pow,
    refine finset.sum_congr _ _,
    { simp },
    { intros x hx,
      rw taylor_coeff,
      simp [X_pow_eq_monomial, mul_comm, mul_assoc, mul_left_comm] } },
  { simp }
end

/-- Taylor's formula. -/
lemma sum_taylor_eq {R} [comm_ring R] (f : polynomial R) (r : R) :
  (taylor r f).sum (λ i a, C a * (X - C r) ^ i) = f :=
begin
  -- we induct over the polynomial because juggling sums via the linearity of the functions
  -- requires constructing and destructing over lsum, lcoeff, which is too much work
  induction f using polynomial.induction_on with k f g hf hg n k IH,
  { simp },
  { rw [linear_map.map_add, sum_add_index, hf, hg];
    simp [add_mul] },
  { rw [←smul_eq_C_mul, linear_map.map_smul, sum_smul_index],
    { nth_rewrite_rhs 0 ←sum_taylor_X_pow r,
      rw [sum_def, sum_def, finset.smul_sum],
      simp [smul_eq_C_mul, mul_assoc] },
    { simp } }
end

end polynomial
