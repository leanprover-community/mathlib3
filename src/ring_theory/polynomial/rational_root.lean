/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.polynomial.basic
import ring_theory.localization

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem for a unique factorization domain `A`
with localization `S`, states that the roots of `p : polynomial A` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leading_coeff`.
The corollary is the integral root theorem `is_integer_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/

section scale_roots

variables {A K R S : Type*} [integral_domain A] [field K] [comm_ring R] [comm_ring S]
variables {M : submonoid A} {f : localization_map M S} {g : fraction_map A K}

open finsupp polynomial

/-- `scale_roots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
noncomputable def scale_roots (p : polynomial R) (s : R) : polynomial R :=
on_finset p.support
  (λ i, coeff p i * s ^ (p.nat_degree - i))
  (λ i h, mem_support_iff.mpr (left_ne_zero_of_mul h))

@[simp] lemma coeff_scale_roots (p : polynomial R) (s : R) (i : ℕ) :
  (scale_roots p s).coeff i = coeff p i * s ^ (p.nat_degree - i) :=
rfl

lemma coeff_scale_roots_nat_degree (p : polynomial R) (s : R) :
  (scale_roots p s).coeff p.nat_degree = p.leading_coeff :=
by rw [leading_coeff, coeff_scale_roots, nat.sub_self, pow_zero, mul_one]

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
begin
  intros i,
  simp only [mem_support_iff, scale_roots, on_finset_apply],
  exact left_ne_zero_of_mul
end

lemma support_scale_roots_eq (p : polynomial R) {s : R} (hs : s ∈ non_zero_divisors R) :
  (scale_roots p s).support = p.support :=
le_antisymm (support_scale_roots_le p s)
  begin
    intro i,
    simp only [mem_support_iff, scale_roots, on_finset_apply],
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
by simp [monic, leading_coeff]

lemma scale_roots_eval₂_eq_zero {p : polynomial S} (f : S →+* R)
  {r : R} {s : S} (hr : eval₂ f r p = 0) (hs : s ∈ non_zero_divisors S) :
  eval₂ f (f s * r) (scale_roots p s) = 0 :=
calc (scale_roots p s).support.sum (λ i, f (coeff p i * s ^ (p.nat_degree - i)) * (f s * r) ^ i)
    = p.support.sum (λ (i : ℕ), f (p.coeff i) * f s ^ (p.nat_degree - i + i) * r ^ i) :
  finset.sum_congr (support_scale_roots_eq p hs)
    (λ i hi, by simp_rw [f.map_mul, f.map_pow, pow_add, mul_pow, mul_assoc])
... = p.support.sum (λ (i : ℕ), f s ^ p.nat_degree * (f (p.coeff i) * r ^ i)) :
  finset.sum_congr rfl
  (λ i hi, by { rw [mul_assoc, mul_left_comm, nat.sub_add_cancel],
                exact le_nat_degree_of_ne_zero (mem_support_iff.mp hi) })
... = f s ^ p.nat_degree * eval₂ f r p : finset.mul_sum.symm
... = 0 : by rw [hr, _root_.mul_zero]

lemma scale_roots_aeval_eq_zero [algebra S R] {p : polynomial S}
  {r : R} {s : S} (hr : aeval r p = 0) (hs : s ∈ non_zero_divisors S) :
  aeval (algebra_map S R s * r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero (algebra_map S R) hr hs

lemma scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero
  {p : polynomial A} {f : A →+* K} (hf : function.injective f)
  {r s : A} (hr : eval₂ f (f r / f s) p = 0) (hs : s ∈ non_zero_divisors A) :
  eval₂ f (f r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero f hr hs,
  rw [←mul_div_assoc, mul_comm, mul_div_cancel],
  exact @map_ne_zero_of_mem_non_zero_divisors _ _ _ _ _ hf ⟨s, hs⟩
end

lemma scale_roots_aeval_eq_zero_of_aeval_div_eq_zero [algebra A K]
  (inj : function.injective (algebra_map A K)) {p : polynomial A} {r s : A}
  (hr : aeval (algebra_map A K r / algebra_map A K s) p = 0) (hs : s ∈ non_zero_divisors A) :
  aeval (algebra_map A K r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

lemma scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : polynomial A} {r : A} {s : M}
  (hr : @aeval A f.codomain _ _ _ (f.mk' r s) p = 0) (hM : M ≤ non_zero_divisors A) :
  @aeval A f.codomain _ _ _ (f.to_map r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero f.to_map hr (hM s.2),
  rw aeval_def,
  congr,
  apply (f.mk'_spec' r s).symm
end

lemma num_is_root_scale_roots_of_aeval_eq_zero
  [unique_factorization_domain A] (g : fraction_map A K)
  {p : polynomial A} {x : g.codomain} (hr : aeval x p = 0) :
  is_root (scale_roots p (g.denom x)) (g.num x) :=
begin
  apply is_root_of_eval₂_map_eq_zero g.injective,
  refine scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero _ (le_refl (non_zero_divisors A)),
  rw g.mk'_num_denom,
  exact hr
end

end scale_roots

section rational_root_theorem

variables {A K : Type*} [integral_domain A] [unique_factorization_domain A] [field K]
variables {f : fraction_map A K}

open polynomial unique_factorization_domain

/-- Rational root theorem part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {p : polynomial A} {r : f.codomain} (hr : aeval r p = 0) :
  f.num r ∣ p.coeff 0 :=
begin
  suffices : f.num r ∣ (scale_roots p (f.denom r)).coeff 0,
  { simp only [coeff_scale_roots, nat.sub_zero] at this,
    haveI := classical.prop_decidable,
    by_cases hr : f.num r = 0,
    { obtain ⟨u, hu⟩ := is_unit_pow p.nat_degree (f.is_unit_denom_of_num_eq_zero hr),
      rw ←hu at this,
      exact dvd_mul_unit_iff.mp this },
    { refine dvd_of_dvd_mul_left_of_no_prime_factors hr _ this,
      intros q dvd_num dvd_denom_pow hq,
      apply hq.not_unit,
      exact f.num_denom_reduced r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow) } },
  convert dvd_term_of_is_root_of_dvd_terms 0 (num_is_root_scale_roots_of_aeval_eq_zero f hr) _,
  { rw [pow_zero, mul_one] },
  intros j hj,
  apply dvd_mul_of_dvd_right,
  convert pow_dvd_pow (f.num r) (nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj)),
  exact (pow_one _).symm
end

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem denom_dvd_of_is_root {p : polynomial A} {r : f.codomain} (hr : aeval r p = 0) :
  (f.denom r : A) ∣ p.leading_coeff :=
begin
  suffices : (f.denom r : A) ∣ p.leading_coeff * f.num r ^ p.nat_degree,
  { refine dvd_of_dvd_mul_left_of_no_prime_factors
      (mem_non_zero_divisors_iff_ne_zero.mp (f.denom r).2) _ this,
    intros q dvd_denom dvd_num_pow hq,
    apply hq.not_unit,
    exact f.num_denom_reduced r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_denom },
  rw ←coeff_scale_roots_nat_degree,
  apply dvd_term_of_is_root_of_dvd_terms _ (num_is_root_scale_roots_of_aeval_eq_zero f hr),
  intros j hj,
  by_cases h : j < p.nat_degree,
  { refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right _ _) _,
    convert pow_dvd_pow _ (nat.succ_le_iff.mpr (nat.lt_sub_left_of_add_lt _)),
    { exact (pow_one _).symm },
    simpa using h },
  rw [←nat_degree_scale_roots p (f.denom r)] at *,
  rw [coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_ne (le_of_not_gt h) hj.symm), zero_mul],
  exact dvd_zero _
end

/-- Integral root theorem:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem is_integer_of_is_root_of_monic {p : polynomial A} (hp : monic p) {r : f.codomain}
  (hr : aeval r p = 0) : f.is_integer r :=
f.is_integer_of_is_unit_denom (is_unit_of_dvd_one _ (hp ▸ denom_dvd_of_is_root hr))

namespace unique_factorization_domain

lemma integer_of_integral {x : f.codomain} :
  is_integral A x → f.is_integer x :=
λ ⟨p, hp, hx⟩, is_integer_of_is_root_of_monic hp hx

lemma integrally_closed : integral_closure A f.codomain = ⊥ :=
eq_bot_iff.mpr (λ x hx, algebra.mem_bot.mpr (integer_of_integral hx))

end unique_factorization_domain

end rational_root_theorem
