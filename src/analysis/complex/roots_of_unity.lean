/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.roots_of_unity
import analysis.special_functions.trigonometric
import analysis.special_functions.pow

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `roots_of_unity_eq`: the complex `n`-th roots of unity are equal to the multiset of
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.
* `card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/

namespace complex

open polynomial real

/-- The complex `n`-th roots of unity are equal to the multiset of
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`. -/
lemma roots_of_unity_eq (n : ℕ) :
  roots_of_unity n ℂ =
  multiset.map (λ (i : ℕ), exp (2 * pi * I * (i / n))) (multiset.range n) :=
begin
  by_cases hn : n = 0,
  { simp only [hn, div_zero, roots_of_unity_zero, multiset.card_zero, nat.cast_zero,
      multiset.map_const, multiset.range_zero, multiset.repeat_zero] },
  have hn0 : (n : ℂ) ≠ 0, by assumption_mod_cast,
  symmetry,
  rw eq_iff_le_not_lt,
  split,
  { rw multiset.le_iff_subset,
    { intro x,
      simp only [multiset.mem_map, multiset.mem_range, mem_roots_of_unity (nat.pos_of_ne_zero hn)],
      rintro ⟨i, hi, rfl⟩,
      rw [← complex.exp_nat_mul, complex.exp_eq_one_iff],
      use i,
      field_simp [hn0, mul_comm (n : ℂ), mul_comm (i : ℂ)] },
    { apply multiset.nodup_map_on _ (multiset.nodup_range n),
      intros i hi j hj H,
      rw [multiset.mem_range] at hi hj,
      rw exp_eq_exp_iff_exists_int at H,
      rcases H with ⟨k, hk⟩,
      rw [mul_comm (k : ℂ), ← mul_add, mul_right_inj' two_pi_I_ne_zero] at hk,
      field_simp [hn0, mul_left_inj'] at hk,
      zify,
      norm_cast at hk,
      rw hk,
      simp only [hn, add_right_eq_self, int.coe_nat_eq_zero, or_false, mul_eq_zero],
      suffices : ∀ {i j : ℕ} {k : ℤ}, i < n → 0 < k → (i : ℤ) = j + k * n → false,
      { rcases lt_trichotomy k 0 with hk0|rfl|hk0;
        [skip, refl, exact (this hi hk0 hk).elim],
        rw [← sub_eq_iff_eq_add, eq_comm, sub_eq_add_neg, ← neg_mul_eq_neg_mul_symm] at hk,
        refine (this hj _ hk).elim,
        exact neg_pos.mpr hk0 },
      clear_dependent i j k,
      intros i j k hi hk0 hk,
      apply not_le.mpr hi,
      zify,
      rw [hk],
      calc (n : ℤ) ≤ k * n : le_mul_of_one_le_left (int.coe_zero_le n) (int.add_one_le_of_lt hk0)
               ... ≤ 0 + k * n : by rw [zero_add]
               ... ≤ j + k * n : add_le_add_right (int.coe_zero_le j) _ } },
  { intro h,
    replace h := multiset.card_lt_of_lt h,
    rw [multiset.card_map, multiset.card_range, ← not_le] at h,
    apply h,
    exact card_roots_of_unity n }
end

lemma mem_roots_of_unity (n : ℕ) (x : ℂ) :
  x ∈ roots_of_unity n ℂ ↔ (∃ i < n, exp (2 * pi * I * (i / n)) = x) :=
by simp only [roots_of_unity_eq, multiset.mem_map, exists_prop, multiset.mem_range]

lemma card_roots_of_unity (n : ℕ) : (roots_of_unity n ℂ).card = n :=
by simp only [roots_of_unity_eq, multiset.card_map, multiset.card_range]

end complex
