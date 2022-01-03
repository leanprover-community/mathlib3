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

end polynomial
