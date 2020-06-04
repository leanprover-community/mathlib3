/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.ideal_operations
import data.polynomial
import tactic.apply_fun
import ring_theory.prime
/-!
# Eisenstein's criterion

A proof of a slight generalisation of Eisenstein's criterion for the irreducibility of
a polynomial over an integral domain.
-/

open polynomial ideal.quotient
variables {R : Type*} [integral_domain R]

/-- If `f` is a non constant polynomial with coefficients in `R`, and `P` is a prime ideal in `R`,
then if every coefficient in `R` except the leading coefficient is in `P`, and
the trailing coefficient is not in `P^2` and no non units in `R` divide `f`, then `f` is
irreducible. -/
theorem irreducible_of_eisenstein_criterion {f : polynomial R} {P : ideal R} (hP : P.is_prime)
  (hfl : f.leading_coeff ∉ P)
  (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P)
  (hfd0 : 0 < degree f) (h0 : f.coeff 0 ∉ P^2)
  (hu : ∀ x : R, C x ∣ f → is_unit x) : irreducible f :=
have hf0 : f ≠ 0, from λ _, by simp * at *,
have hf : f.map (mk_hom P) =
    C (mk_hom P (leading_coeff f)) * X ^ nat_degree f,
  from polynomial.ext (λ n, begin
    rcases lt_trichotomy ↑n (degree f) with h | h | h,
    { erw [coeff_map, ← mk_eq_mk_hom, eq_zero_iff_mem.2 (hfP n h),
        coeff_C_mul, coeff_X_pow, if_neg, mul_zero],
      rintro rfl, exact not_lt_of_ge degree_le_nat_degree h },
    { have : nat_degree f = n, from nat_degree_eq_of_degree_eq_some h.symm,
      rw [coeff_C_mul, coeff_X_pow, if_pos this.symm, mul_one, leading_coeff, this, coeff_map] },
    { rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt],
      { refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) _,
        rwa ← degree_eq_nat_degree hf0 },
      { exact lt_of_le_of_lt (degree_map_le _) h } }
  end),
have hfd0 : 0 < f.nat_degree, from with_bot.coe_lt_coe.1
  (lt_of_lt_of_le hfd0 degree_le_nat_degree),
⟨mt degree_eq_zero_of_is_unit (λ h, by simp [*, lt_irrefl] at *),
begin
  rintros p q rfl,
  rw [map_mul] at hf,
  have : map (mk_hom P) p ∣ C (mk_hom P (p * q).leading_coeff) * X ^ (p * q).nat_degree,
    from ⟨map (mk_hom P) q, hf.symm⟩,
  rcases mul_eq_mul_prime_pow (show prime (X : polynomial (ideal.quotient P)),
    from prime_of_degree_eq_one_of_monic degree_X monic_X) hf with
      ⟨m, n, b, c, hmnd, hbc, hp, hq⟩,
  have hmn : 0 < m → 0 < n → false,
  { assume hm0 hn0,
    have hp0 : p.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [← hp, coeff_zero_eq_eval_zero, zero_pow hm0] },
    have hq0 : q.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [← hq, coeff_zero_eq_eval_zero, zero_pow hn0] },
    apply h0,
    rw [coeff_zero_eq_eval_zero, eval_mul, pow_two],
    exact ideal.mul_mem_mul hp0 hq0 },
  have hpql0 : (mk_hom P) (p * q).leading_coeff ≠ 0,
  { rwa [← mk_eq_mk_hom, ne.def, eq_zero_iff_mem] },
  have hp0 : p ≠ 0, from λ h, by simp * at *,
  have hq0 : q ≠ 0, from λ h, by simp * at *,
  have hbc0 : degree b = 0 ∧ degree c = 0,
  { apply_fun degree at hbc,
    rwa [degree_C hpql0, degree_mul_eq, nat.with_bot.add_eq_zero_iff] at hbc },
  have hmp : m ≤ nat_degree p,
    from with_bot.coe_le_coe.1
      (calc ↑m = degree (p.map (mk_hom P)) : by simp [← hp, hbc0.1]
         ... ≤ degree p : degree_map_le _
         ... ≤ nat_degree p : degree_le_nat_degree),
  have hmp : n ≤ nat_degree q,
    from with_bot.coe_le_coe.1
      (calc ↑n = degree (q.map (mk_hom P)) : by simp [← hq, hbc0.2]
         ... ≤ degree q : degree_map_le _
         ... ≤ nat_degree q : degree_le_nat_degree),
  have hpmqn : p.nat_degree = m ∧ q.nat_degree = n,
  { rw [nat_degree_mul_eq hp0 hq0] at hmnd, omega },
  obtain rfl | rfl : m = 0 ∨ n = 0,
  { rwa [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero, imp_false, not_not,
      ← or_iff_not_imp_left] at hmn },
  { left,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1)],
    exact dvd_mul_right _ _ },
  { right,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2)],
    exact dvd_mul_left _ _ }
end⟩
