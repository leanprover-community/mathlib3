/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.hasse_deriv
import data.polynomial.algebra_map

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
open_locale big_operators polynomial

variables {R : Type*}

section semiring
variables [semiring R] {a : R} (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : R[X] →ₗ[R] R[X] :=
{ to_fun := λ f, f.comp (X + C r),
  map_add' := λ f g, add_comp,
  map_smul' := λ c f, by simp only [smul_eq_C_mul, C_mul_comp, ring_hom.id_apply] }

lemma taylor_apply : taylor r f = f.comp (X + C r) := rfl

@[simp] lemma taylor_X : taylor r X = X + C r :=
by simp only [taylor_apply, X_comp]

@[simp] lemma taylor_C (x : R) : taylor r (C x) = C x :=
by simp only [taylor_apply, C_comp]

@[simp] lemma taylor_zero' : taylor (0 : R) = linear_map.id :=
begin
  ext,
  simp only [taylor_apply, add_zero, comp_X, _root_.map_zero, linear_map.id_comp, function.comp_app,
             linear_map.coe_comp]
end

lemma taylor_zero (f : R[X]) : taylor 0 f = f :=
by rw [taylor_zero', linear_map.id_apply]

@[simp] lemma taylor_one : taylor r (1 : R[X]) = C 1 :=
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

@[simp] lemma nat_degree_taylor (p : R[X]) (r : R) :
  nat_degree (taylor r p) = nat_degree p :=
begin
  refine map_nat_degree_eq_nat_degree _ _,
  nontriviality R,
  intros n c c0,
  simp [taylor_monomial, nat_degree_C_mul_eq_of_mul_ne_zero, nat_degree_pow_X_add_C, c0]
end

@[simp] lemma taylor_add {p q : R[X]} :
  taylor r (p + q) = taylor r p + taylor r q :=
by simp only [taylor_apply, add_comp]

@[simp] lemma taylor_mul_X {p : R[X]} : taylor r (p * X) = taylor r p * (X + C r) :=
by simp only [taylor_apply, mul_X_comp]

@[simp] lemma taylor_X_pow {k : ℕ} : taylor r (X^k) = (X + C r)^k :=
by simp only [taylor_apply, X_pow_comp]

@[simp] lemma taylor_mul_X_pow {p : R[X]} {k : ℕ} : taylor r (p * X^k) = taylor r p * (X + C r)^k :=
by simp only [taylor_apply, mul_X_pow_comp]

@[simp] lemma taylor_C_mul {p : R[X]} : taylor r (C a * p) = C a * taylor r p :=
by simp only [taylor_apply, C_mul_comp]

@[simp] lemma taylor_nat_cast_mul {p : R[X]} {n : ℕ} : taylor r ((n : R[X]) * p) = n * taylor r p :=
by simp only [taylor_apply, nat_cast_mul_comp]

end semiring

section comm_semiring
variables [comm_semiring R]

@[simp] lemma taylor_mul (r : R) (p q : R[X]) :
  taylor r (p * q) = taylor r p * taylor r q :=
by simp only [taylor_apply, mul_comp]

@[simp] lemma taylor_pow (r : R) (p : R[X]) (n : ℕ) :
  taylor r (p^n) = (taylor r p)^n :=
by simp only [taylor_apply, pow_comp]

lemma taylor_taylor (f : R[X]) (r s : R) :
  taylor r (taylor s f) = taylor (r + s) f :=
by simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, C_add, add_assoc]

lemma taylor_eval (r : R) (f : R[X]) (s : R) :
  (taylor r f).eval s = f.eval (s + r) :=
by simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

/-- `taylor r`, regarded as a ring homomorphism from `polynomial R` to itself. -/
def taylor_ring_hom (r : R) : R[X] →+* R[X] := comp_ring_hom (X + C r)

lemma taylor_list_prod (r : R) (l : list R[X]) :
  taylor r l.prod = (l.map (λ q : R[X], taylor r q)).prod :=
(taylor_ring_hom r).map_list_prod l

lemma taylor_multiset_prod (r : R) (s : multiset R[X]) :
  taylor r s.prod = (s.map (λ q : R[X], taylor r q)).prod :=
(taylor_ring_hom r).map_multiset_prod s

lemma taylor_prod (r : R) {ι : Type*} (s : finset ι) (q : ι → R[X]) :
  taylor r (∏ j in s, q j) = ∏ j in s, taylor r (q j) :=
(taylor_ring_hom r).map_prod _ _

end comm_semiring

section ring
variables [ring R]

@[simp] lemma taylor_int_cast_mul (r : R) {p : R[X]} {n : ℤ} :
  taylor r ((n : R[X]) * p) = n * taylor r p :=
by simp only [taylor_apply, int_cast_mul_comp]

end ring

section comm_ring
variables [comm_ring R]

lemma taylor_eval_sub (r : R) (f : R[X]) (s : R) :
  (taylor r f).eval (s - r) = f.eval s :=
by rw [taylor_eval, sub_add_cancel]

lemma taylor_injective (r : R) : function.injective (taylor r) :=
begin
  intros f g h,
  apply_fun taylor (-r) at h,
  simpa only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, C_neg,
    neg_add_cancel_right, comp_X] using h,
end

lemma eq_zero_of_hasse_deriv_eq_zero (f : R[X]) (r : R)
  (h : ∀ k, (hasse_deriv k f).eval r = 0) :
  f = 0 :=
begin
  apply taylor_injective r,
  rw linear_map.map_zero,
  ext k,
  simp only [taylor_coeff, h, coeff_zero],
end

/-- Taylor's formula. -/
lemma sum_taylor_eq (f : R[X]) (r : R) :
  (taylor r f).sum (λ i a, C a * (X - C r) ^ i) = f :=
by rw [←comp_eq_sum_left, sub_eq_add_neg, ←C_neg, ←taylor_apply, taylor_taylor, neg_add_self,
       taylor_zero]

end comm_ring

end polynomial
