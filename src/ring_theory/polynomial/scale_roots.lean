/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/

import ring_theory.polynomial.basic
import ring_theory.non_zero_divisors

/-!
# Scaling the roots of a polynomial

This file defines `scale_roots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/

section scale_roots

variables {A K R S : Type*} [comm_ring A] [is_domain A] [field K] [comm_ring R] [comm_ring S]
variables {M : submonoid A}

open polynomial
open_locale big_operators

/-- `scale_roots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
noncomputable def scale_roots (p : polynomial R) (s : R) : polynomial R :=
∑ i in p.support, monomial i (p.coeff i * s ^ (p.nat_degree - i))

@[simp] lemma coeff_scale_roots (p : polynomial R) (s : R) (i : ℕ) :
  (scale_roots p s).coeff i = coeff p i * s ^ (p.nat_degree - i) :=
by simp [scale_roots, coeff_monomial] {contextual := tt}

lemma coeff_scale_roots_nat_degree (p : polynomial R) (s : R) :
  (scale_roots p s).coeff p.nat_degree = p.leading_coeff :=
by rw [leading_coeff, coeff_scale_roots, tsub_self, pow_zero, mul_one]

@[simp] lemma zero_scale_roots (s : R) : scale_roots 0 s = 0 := by { ext, simp }

lemma scale_roots_ne_zero {p : polynomial R} (hp : p ≠ 0) (s : R) :
  scale_roots p s ≠ 0 :=
begin
  intro h,
  have : p.coeff p.nat_degree ≠ 0 := mt leading_coeff_eq_zero.mp hp,
  have : (scale_roots p s).coeff p.nat_degree = 0 :=
    congr_fun (congr_arg (coeff : polynomial R → ℕ → R) h) p.nat_degree,
  rw [coeff_scale_roots_nat_degree] at this,
  contradiction
end

lemma support_scale_roots_le (p : polynomial R) (s : R) :
  (scale_roots p s).support ≤ p.support :=
by { intro, simpa using left_ne_zero_of_mul }

lemma support_scale_roots_eq (p : polynomial R) {s : R} (hs : s ∈ non_zero_divisors R) :
  (scale_roots p s).support = p.support :=
le_antisymm (support_scale_roots_le p s)
  begin
    intro i,
    simp only [coeff_scale_roots, polynomial.mem_support_iff],
    intros p_ne_zero ps_zero,
    have := ((non_zero_divisors R).pow_mem hs (p.nat_degree - i)) _ ps_zero,
    contradiction
  end

@[simp] lemma degree_scale_roots (p : polynomial R) {s : R} :
  degree (scale_roots p s) = degree p :=
begin
  haveI := classical.prop_decidable,
  by_cases hp : p = 0,
  { rw [hp, zero_scale_roots] },
  have := scale_roots_ne_zero hp s,
  refine le_antisymm (finset.sup_mono (support_scale_roots_le p s)) (degree_le_degree _),
  rw coeff_scale_roots_nat_degree,
  intro h,
  have := leading_coeff_eq_zero.mp h,
  contradiction,
end

@[simp] lemma nat_degree_scale_roots (p : polynomial R) (s : R) :
  nat_degree (scale_roots p s) = nat_degree p :=
by simp only [nat_degree, degree_scale_roots]

lemma monic_scale_roots_iff {p : polynomial R} (s : R) :
  monic (scale_roots p s) ↔ monic p :=
by simp only [monic, leading_coeff, nat_degree_scale_roots, coeff_scale_roots_nat_degree]

lemma scale_roots_eval₂_eq_zero {p : polynomial S} (f : S →+* R)
  {r : R} {s : S} (hr : eval₂ f r p = 0) :
  eval₂ f (f s * r) (scale_roots p s) = 0 :=
calc eval₂ f (f s * r) (scale_roots p s) =
  (scale_roots p s).support.sum (λ i, f (coeff p i * s ^ (p.nat_degree - i)) * (f s * r) ^ i) :
  by simp [eval₂_eq_sum, sum_def]
... = p.support.sum (λ i, f (coeff p i * s ^ (p.nat_degree - i)) * (f s * r) ^ i) :
  finset.sum_subset (support_scale_roots_le p s)
  (λ i hi hi', let this : coeff p i * s ^ (p.nat_degree - i) = 0 :=
  by simpa using hi' in by simp [this])
... = p.support.sum (λ (i : ℕ), f (p.coeff i) * f s ^ (p.nat_degree - i + i) * r ^ i) :
  finset.sum_congr rfl
  (λ i hi, by simp_rw [f.map_mul, f.map_pow, pow_add, mul_pow, mul_assoc])
... = p.support.sum (λ (i : ℕ), f s ^ p.nat_degree * (f (p.coeff i) * r ^ i)) :
  finset.sum_congr rfl
  (λ i hi, by { rw [mul_assoc, mul_left_comm, tsub_add_cancel_of_le],
                exact le_nat_degree_of_ne_zero (polynomial.mem_support_iff.mp hi) })
... = f s ^ p.nat_degree * p.support.sum (λ (i : ℕ), (f (p.coeff i) * r ^ i)) : finset.mul_sum.symm
... = f s ^ p.nat_degree * eval₂ f r p : by { simp [eval₂_eq_sum, sum_def] }
... = 0 : by rw [hr, _root_.mul_zero]

lemma scale_roots_aeval_eq_zero [algebra S R] {p : polynomial S}
  {r : R} {s : S} (hr : aeval r p = 0) :
  aeval (algebra_map S R s * r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero (algebra_map S R) hr

lemma scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
  {p : polynomial A} {f : A →+* K} (hf : function.injective f)
  {r s : A} (hr : eval₂ f (f r / f s) p = 0) (hs : s ∈ non_zero_divisors A) :
  eval₂ f (f r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero f hr,
  rw [←mul_div_assoc, mul_comm, mul_div_cancel],
  exact f.map_ne_zero_of_mem_non_zero_divisors hf hs
end

lemma scale_roots_aeval_eq_zero_of_aeval_div_eq_zero [algebra A K]
  (inj : function.injective (algebra_map A K)) {p : polynomial A} {r s : A}
  (hr : aeval (algebra_map A K r / algebra_map A K s) p = 0) (hs : s ∈ non_zero_divisors A) :
  aeval (algebra_map A K r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

end scale_roots
