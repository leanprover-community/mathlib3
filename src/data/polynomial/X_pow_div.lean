/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.reverse

open polynomial finset

variables {R : Type*} [integral_domain R] {f : polynomial R}

/-
lemma nonzero_iff_card_support_pos : f ≠ 0 ↔ f.support.card ≠ 0 :=
begin
  sorry,
end
-/

lemma nat_trailing_degree_lt_of_card_gt (h : 1 < f.support.card) :
  f.nat_trailing_degree < f.nat_degree :=
begin
  sorry,
end

lemma X_pow_nat_degree (n : ℕ) : ((X : polynomial R) ^ n).nat_degree = n :=
by { rw [← one_mul (X ^ n), ← C_1, nat_degree_C_mul_X_pow_of_nonzero], exact one_ne_zero, }

lemma X_pow_leading_coeff (n : ℕ) : ((X : polynomial R) ^ n).leading_coeff = 1 :=
by { rw [← one_mul (X ^ n), ← C_1, leading_coeff_mul_X_pow, C_1, leading_coeff_one], }

lemma X_pow_div {n : ℕ} (H : f ∣ (X ^ n)) : ∃ r : R, ∃ k : ℕ, k ≤ n ∧ is_unit r ∧ f = C r * X ^ k :=
begin
  refine ⟨leading_coeff f, nat_degree f, _⟩,
  rcases H with ⟨g, hg⟩,
  refine ⟨_, _, _⟩,
  { apply (@nat.le.intro _ _ g.nat_degree),
    rw [← nat_degree_mul', ← hg, X_pow_nat_degree],
    rw [← leading_coeff_mul, ← hg, leading_coeff_X_pow],
    exact one_ne_zero, },
  { apply is_unit_of_mul_eq_one _ g.leading_coeff,
    convert (congr_arg leading_coeff hg).symm,
    { exact (leading_coeff_mul f g).symm, },
    { exact (X_pow_leading_coeff n).symm, }, },
  {
    rw C_mul_X_pow_eq_self,
    by_contra fs,
    rw not_le at fs,
    have : f.nat_trailing_degree < f.nat_degree,
      rw [nat_trailing_degree_eq_support_min', nat_degree_eq_support_max'],
      exact min'_lt_max'_of_card _ fs,
      rw ← nonempty_support_iff,
      refine ⟨f.nat_degree, nat_degree_mem_support_of_nonzero _⟩,
      repeat { rintro rfl, rw [support_zero, card_empty] at fs, exact nat.not_lt_zero _ fs, },



      apply nonzero_iff_card_support_pos.mpr,

      rintros j,

    sorry,
  },
end
