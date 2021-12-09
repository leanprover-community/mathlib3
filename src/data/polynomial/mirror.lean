/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.ring_division

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`. We also define `polynomial.norm2`, which is the sum of the squares of the
coefficients of a polynomial. It is also a coefficient of `p * p.mirror`.

## Main definitions

- `polynomial.mirror`
- `polynomial.norm2`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`
- `polynomial.norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.mirror`

-/

namespace polynomial

variables {R : Type*} [semiring R] (p : polynomial R)

section mirror

/-- mirror of a polynomial: reverses the coefficients while preserving `polynomial.nat_degree` -/
noncomputable def mirror := p.reverse * X ^ p.nat_trailing_degree

@[simp] lemma mirror_zero : (0 : polynomial R).mirror = 0 := by simp [mirror]

lemma mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = (monomial n a) :=
begin
  by_cases ha : a = 0,
  { rw [ha, monomial_zero_right, mirror_zero] },
  { rw [mirror, reverse, nat_degree_monomial n a ha, nat_trailing_degree_monomial ha,
        ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, rev_at_le (le_refl n),
        tsub_self, pow_zero, mul_one] },
end

lemma mirror_C (a : R) : (C a).mirror = C a :=
mirror_monomial 0 a

lemma mirror_X : X.mirror = (X : polynomial R) :=
mirror_monomial 1 (1 : R)

lemma mirror_nat_degree : p.mirror.nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, mirror_zero] },
  by_cases hR : nontrivial R,
  { haveI := hR,
    rw [mirror, nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        tsub_add_cancel_of_le p.nat_trailing_degree_le_nat_degree],
    rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, ne, trailing_coeff_eq_zero] },
  { haveI := not_nontrivial_iff_subsingleton.mp hR,
    exact congr_arg nat_degree (subsingleton.elim p.mirror p) },
end

lemma mirror_nat_trailing_degree : p.mirror.nat_trailing_degree = p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, mirror_zero] },
  { rw [mirror, nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
        reverse_nat_trailing_degree, zero_add] },
end

lemma coeff_mirror (n : ℕ) :
  p.mirror.coeff n = p.coeff (rev_at (p.nat_degree + p.nat_trailing_degree) n) :=
begin
  by_cases h2 : p.nat_degree < n,
  { rw [coeff_eq_zero_of_nat_degree_lt (by rwa mirror_nat_degree)],
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree,
    { rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree],
      exact (tsub_lt_iff_left h1).mpr (nat.add_lt_add_right h2 _) },
    { rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2] } },
  rw not_lt at h2,
  rw [rev_at_le (h2.trans (nat.le_add_right _ _))],
  by_cases h3 : p.nat_trailing_degree ≤ n,
  { rw [←tsub_add_eq_add_tsub h2, ←tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow',
        if_pos h3, coeff_reverse, rev_at_le (tsub_le_self.trans h2)] },
  rw not_le at h3,
  rw coeff_eq_zero_of_nat_degree_lt (lt_tsub_iff_right.mpr (nat.add_lt_add_left h3 _)),
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa mirror_nat_trailing_degree),
end

--TODO: Extract `finset.sum_range_rev_at` lemma.
lemma mirror_eval_one : p.mirror.eval 1 = p.eval 1 :=
begin
  simp_rw [eval_eq_finset_sum, one_pow, mul_one, mirror_nat_degree],
  refine finset.sum_bij_ne_zero _ _ _ _ _,
  { exact λ n hn hp, rev_at (p.nat_degree + p.nat_trailing_degree) n },
  { intros n hn hp,
    rw finset.mem_range_succ_iff at *,
    rw rev_at_le (hn.trans (nat.le_add_right _ _)),
    rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right, ←mirror_nat_trailing_degree],
    exact nat_trailing_degree_le_of_ne_zero hp },
  { exact λ n₁ n₂ hn₁ hp₁ hn₂ hp₂ h, by rw [←@rev_at_invol _ n₁, h, rev_at_invol] },
  { intros n hn hp,
    use rev_at (p.nat_degree + p.nat_trailing_degree) n,
    refine ⟨_, _, rev_at_invol.symm⟩,
    { rw finset.mem_range_succ_iff at *,
      rw rev_at_le (hn.trans (nat.le_add_right _ _)),
      rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right],
      exact nat_trailing_degree_le_of_ne_zero hp },
    { change p.mirror.coeff _ ≠ 0,
      rwa [coeff_mirror, rev_at_invol] } },
  { exact λ n hn hp, p.coeff_mirror n },
end

lemma mirror_mirror : p.mirror.mirror = p :=
polynomial.ext (λ n, by rw [coeff_mirror, coeff_mirror,
  mirror_nat_degree, mirror_nat_trailing_degree, rev_at_invol])

lemma mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
⟨λ h, by rw [←p.mirror_mirror, h, mirror_zero], λ h, by rw [h, mirror_zero]⟩

lemma mirror_trailing_coeff : p.mirror.trailing_coeff = p.leading_coeff :=
by rw [leading_coeff, trailing_coeff, mirror_nat_trailing_degree, coeff_mirror,
  rev_at_le (nat.le_add_left _ _), add_tsub_cancel_right]

lemma mirror_leading_coeff : p.mirror.leading_coeff = p.trailing_coeff :=
by rw [←p.mirror_mirror, mirror_trailing_coeff, p.mirror_mirror]

lemma mirror_mul_of_domain {R : Type*} [ring R] [is_domain R] (p q : polynomial R) :
  (p * q).mirror = p.mirror * q.mirror :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, mirror_zero, zero_mul] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, mirror_zero, mul_zero] },
  rw [mirror, mirror, mirror, reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add],
  rw [mul_assoc, ←mul_assoc q.reverse],
  conv_lhs { congr, skip, congr, rw [←X_pow_mul] },
  repeat { rw [mul_assoc], },
end

lemma mirror_smul {R : Type*} [ring R] [is_domain R] (p : polynomial R) (a : R) :
  (a • p).mirror = a • p.mirror :=
by rw [←C_mul', ←C_mul', mirror_mul_of_domain, mirror_C]

lemma mirror_neg {R : Type*} [ring R] (p : polynomial R) : (-p).mirror = -(p.mirror) :=
by rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

lemma irreducible_of_mirror {R : Type*} [comm_ring R] [is_domain R] {f : polynomial R}
  (h1 : ¬ is_unit f)
  (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
  (h3 : ∀ g, g ∣ f → g ∣ f.mirror → is_unit g) : irreducible f :=
begin
  split,
  { exact h1 },
  { intros g h fgh,
    let k := g * h.mirror,
    have key : f * f.mirror = k * k.mirror,
    { rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror,
          mul_assoc, mul_comm h, mul_comm g.mirror, mul_assoc, ←mul_assoc] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.mirror },
    have h_dvd_k_rev : h ∣ k.mirror,
    { rw [mirror_mul_of_domain, mirror_mirror],
      exact dvd_mul_left h g.mirror },
    have hk := h2 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h3 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h3 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, mirror_neg, dvd_neg])) },
    { exact or.inl (h3 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h3 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

end mirror

end polynomial
