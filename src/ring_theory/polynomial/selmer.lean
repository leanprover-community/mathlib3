/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.unit_trinomial
import tactic.linear_combination

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `polynomial.selmer_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/

namespace polynomial
open_locale polynomial

lemma selmer_irreducible_aux (n : ℕ) (z : ℂ) : ¬ (z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) :=
begin
  rintros ⟨h1, h2⟩,
  replace h3 : z ^ 3 = 1,
  { linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2 }, -- thanks polyrith!
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2,
  { rw [←nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one],
    have : n % 3 < 3 := nat.mod_lt n zero_lt_three,
    interval_cases n % 3; simp only [h, pow_zero, pow_one, eq_self_iff_true, or_true, true_or] },
  have z_ne_zero : z ≠ 0 :=
  λ h, zero_ne_one ((zero_pow zero_lt_three).symm.trans (show (0 : ℂ) ^ 3 = 1, from h ▸ h3)),
  rcases key with key | key | key,
  { exact z_ne_zero (by rwa [key, self_eq_add_left] at h1) },
  { exact one_ne_zero (by rwa [key, self_eq_add_right] at h1) },
  { exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2)) },
end

lemma selmer_irreducible {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℤ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  have hp : (X ^ n - X - 1 : polynomial ℤ) = trinomial 0 1 n (-1) (-1) 1 :=
    by simp only [trinomial, C_neg, C_1]; ring,
  rw hp,
  apply is_unit_trinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩,
  rintros z ⟨h1, h2⟩,
  apply selmer_irreducible_aux n z,
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2,
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C] at h1 h2,
  simp_rw [units.coe_neg, units.coe_one, map_neg, map_one] at h1 h2,
  replace h1 : z ^ n = z + 1 := by linear_combination h1,
  replace h2 := mul_eq_zero_of_left h2 z,
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ←pow_succ', nat.sub_add_cancel hn.le] at h2,
  rw h1 at h2 ⊢,
  exact ⟨rfl, by linear_combination -h2⟩,
end

lemma selmer_irreducible' {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℚ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hp : (X ^ n - X - 1 : polynomial ℤ) = trinomial 0 1 n (-1) (-1) 1 :=
  by simp only [trinomial, C_neg, C_1]; ring,
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  have h := (is_primitive.int.irreducible_iff_irreducible_map_cast _).mp (selmer_irreducible hn1),
  { rwa [polynomial.map_sub, polynomial.map_sub, polynomial.map_pow, polynomial.map_one,
      polynomial.map_X] at h },
  { exact hp.symm ▸ (trinomial_monic zero_lt_one hn).is_primitive },
end

end polynomial
