/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.ring_division
import algebra.big_operators.nat_antidiagonal

/-!
# Reverse of a univariate polynomial
In this file we define an alternate version of `reverse`.
The difference between the old `reverse` and the new `reverse'` is that the old
`reverse` will decrease the degree if the polynomial is divisible by `X`.
We also define `norm2`, which is the sum of the squares of the coefficients of a polynomial.
It is also a coefficient of `p * p.reverse'`.
## Main definitions
- `p.reverse'`
- `p.norm2`
## Main results
- `reverse'_mul_of_domain`: `reverse'` preserves multiplication.
- `reverse'_irreducible_test`: an irreducibility criterion involving `reverse'`
- `norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.reverse'`
-/

namespace polynomial

variables {R : Type*} [semiring R] (p : polynomial R)

section reverse'

/-- reverse of a polynomial -/
noncomputable def reverse' := p.reverse * X ^ p.nat_trailing_degree

lemma reverse'_zero : (0 : polynomial R).reverse' = 0 := rfl

lemma reverse'_monomial (n : ℕ) (a : R) : (monomial n a).reverse' = (monomial n a) :=
begin
  by_cases ha : a = 0,
  { rw [ha, monomial_zero_right, reverse'_zero] },
  { rw [reverse', reverse, nat_degree_monomial n a ha, nat_trailing_degree_monomial ha,
        ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, rev_at_le (le_refl n),
        nat.sub_self, pow_zero, mul_one] },
end

lemma reverse'_C (a : R) : (C a).reverse' = C a :=
reverse'_monomial 0 a

lemma reverse'_X : X.reverse' = (X : polynomial R) :=
reverse'_monomial 1 (1 : R)

lemma reverse'_nat_degree : p.reverse'.nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  by_cases hR : nontrivial R,
  { haveI := hR,
    rw [reverse', nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        nat.sub_add_cancel p.nat_trailing_degree_le_nat_degree],
    rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, ne, trailing_coeff_eq_zero] },
  { haveI := not_nontrivial_iff_subsingleton.mp hR,
    exact congr_arg nat_degree (subsingleton.elim p.reverse' p) },
end

lemma reverse'_nat_trailing_degree : p.reverse'.nat_trailing_degree = p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  { rw [reverse', nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
        reverse_nat_trailing_degree, zero_add] },
end

lemma coeff_reverse' (n : ℕ) :
  p.reverse'.coeff n = p.coeff (rev_at (p.nat_degree + p.nat_trailing_degree) n) :=
begin
  by_cases h2 : p.nat_degree < n,
  { rw [coeff_eq_zero_of_nat_degree_lt (by rwa reverse'_nat_degree)],
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree,
    { rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree],
      exact (nat.sub_lt_left_iff_lt_add h1).mpr (nat.add_lt_add_right h2 _) },
    { rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2] } },
  rw not_lt at h2,
  rw [rev_at_le (h2.trans (nat.le_add_right _ _))],
  by_cases h3 : p.nat_trailing_degree ≤ n,
  { rw [←nat.sub_add_eq_add_sub h2, ←nat.sub_sub_assoc h2 h3, reverse', coeff_mul_X_pow',
        if_pos h3, coeff_reverse, rev_at_le ((nat.sub_le_self _ _).trans h2)] },
  rw not_le at h3,
  rw coeff_eq_zero_of_nat_degree_lt (nat.lt_sub_right_iff_add_lt.mpr (nat.add_lt_add_left h3 _)),
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa reverse'_nat_trailing_degree),
end

lemma reverse'_eval_one : p.reverse'.eval 1 = p.eval 1 :=
begin
  simp_rw [eval_eq_finset_sum, one_pow, mul_one, reverse'_nat_degree],
  refine finset.sum_bij_ne_zero _ _ _ _ _,
  { exact λ n hn hp, rev_at (p.nat_degree + p.nat_trailing_degree) n },
  { intros n hn hp,
    rw finset.mem_range_succ_iff at *,
    rw rev_at_le (hn.trans (nat.le_add_right _ _)),
    rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel, ←reverse'_nat_trailing_degree],
    exact nat_trailing_degree_le_of_ne_zero hp },
  { exact λ n₁ n₂ hn₁ hp₁ hn₂ hp₂ h, by rw [←@rev_at_invol _ n₁, h, rev_at_invol] },
  { intros n hn hp,
    use rev_at (p.nat_degree + p.nat_trailing_degree) n,
    refine ⟨_, _, rev_at_invol.symm⟩,
    { rw finset.mem_range_succ_iff at *,
      rw rev_at_le (hn.trans (nat.le_add_right _ _)),
      rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel],
      exact nat_trailing_degree_le_of_ne_zero hp },
    { change p.reverse'.coeff _ ≠ 0,
      rwa [coeff_reverse', rev_at_invol] } },
  { exact λ n hn hp, p.coeff_reverse' n },
end

lemma reverse'_reverse' : p.reverse'.reverse' = p :=
polynomial.ext (λ n, by rw [coeff_reverse', coeff_reverse',
  reverse'_nat_degree, reverse'_nat_trailing_degree, rev_at_invol])

lemma reverse'_eq_zero : p.reverse' = 0 ↔ p = 0 :=
⟨λ h, by rw [←p.reverse'_reverse', h, reverse'_zero], λ h, by rw [h, reverse'_zero]⟩

lemma reverse'_trailing_coeff : p.reverse'.trailing_coeff = p.leading_coeff :=
by rw [leading_coeff, trailing_coeff, reverse'_nat_trailing_degree, coeff_reverse',
  rev_at_le (nat.le_add_left _ _), nat.add_sub_cancel]

lemma reverse'_leading_coeff : p.reverse'.leading_coeff = p.trailing_coeff :=
by rw [←p.reverse'_reverse', reverse'_trailing_coeff, p.reverse'_reverse']

lemma reverse'_mul_of_domain {R : Type*} [integral_domain R] (p q : polynomial R) :
  (p * q).reverse' = p.reverse' * q.reverse' :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, reverse'_zero, zero_mul] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, reverse'_zero, mul_zero] },
  rw [reverse', reverse', reverse', reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add],
  ring,
end

lemma reverse'_smul {R : Type*} [integral_domain R] (p : polynomial R) (a : R) :
  (a • p).reverse' = a • p.reverse' :=
by rw [←C_mul', ←C_mul', reverse'_mul_of_domain, reverse'_C]

lemma reverse'_neg {R : Type*} [ring R] (p : polynomial R) : (-p).reverse' = -(p.reverse') :=
by rw [reverse', reverse', reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

lemma reverse'_irreducible_test {R : Type*} [integral_domain R] {f : polynomial R}
  (h1 : ¬ is_unit f)
  (h2 : ∀ k, f * f.reverse' = k * k.reverse' → k = f ∨ k = -f ∨ k = f.reverse' ∨ k = -f.reverse')
  (h3 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  split,
  { exact h1 },
  { intros g h fgh,
    let k := g * h.reverse',
    have key : f * f.reverse' = k * k.reverse',
    { rw [fgh, reverse'_mul_of_domain, reverse'_mul_of_domain, reverse'_reverse',
          mul_assoc, mul_comm h, mul_comm g.reverse', mul_assoc, ←mul_assoc] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.reverse' },
    have h_dvd_k_rev : h ∣ k.reverse',
    { rw [reverse'_mul_of_domain, reverse'_reverse'],
      exact dvd_mul_left h g.reverse' },
    have hk := h2 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h3 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h3 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, reverse'_neg, dvd_neg])) },
    { exact or.inl (h3 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h3 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

end reverse'

end polynomial
