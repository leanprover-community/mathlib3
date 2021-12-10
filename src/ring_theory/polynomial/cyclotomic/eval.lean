/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import ring_theory.polynomial.cyclotomic.basic
import tactic.by_contra
import topology.algebra.polynomial
import number_theory.padics.padic_norm

/-!
# Evaluating cyclotomic polynomials
This file states some results about evaluating cyclotomic polynomials in various different ways.
## Main definitions
* `polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/

namespace polynomial

open finset nat
open_locale big_operators

@[simp] lemma eval_one_cyclotomic_prime {R : Type*} [comm_ring R] {p : ℕ} [hn : fact p.prime] :
  eval 1 (cyclotomic p R) = p :=
by simp only [cyclotomic_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const, eval_pow,
              eval_finset_sum, card_range, smul_one_eq_coe]

@[simp] lemma eval₂_one_cyclotomic_prime {R S : Type*} [comm_ring R] [semiring S] (f : R →+* S)
  {p : ℕ} [fact p.prime] : eval₂ f 1 (cyclotomic p R) = p :=
by simp

@[simp] lemma eval_one_cyclotomic_prime_pow {R : Type*} [comm_ring R] {p : ℕ} (k : ℕ)
  [hn : fact p.prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p :=
by simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const,
              eval_pow, eval_finset_sum, card_range, smul_one_eq_coe]

@[simp] lemma eval₂_one_cyclotomic_prime_pow {R S : Type*} [comm_ring R] [semiring S] (f : R →+* S)
  {p : ℕ} (k : ℕ) [fact p.prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p :=
by simp

-- TODO show that `eval 1 (cyclotomic n R) = 1` when `n` is not a power of a prime

private lemma cyclotomic_neg_one_pos {n : ℕ} (hn : 2 < n) {R} [linear_ordered_comm_ring R] :
  0 < eval (-1 : R) (cyclotomic n R) :=
begin
  rw [←map_cyclotomic_int, ←int.cast_one, ←int.cast_neg, eval_int_cast_map,
      int.coe_cast_ring_hom, int.cast_pos],
  suffices : 0 < eval ↑(-1 : ℤ) (cyclotomic n ℝ),
  { rw [←map_cyclotomic_int n ℝ, eval_int_cast_map, int.coe_cast_ring_hom] at this,
    exact_mod_cast this },
  simp only [int.cast_one, int.cast_neg],
  have h0 := cyclotomic_coeff_zero ℝ hn.le,
  rw coeff_zero_eq_eval_zero at h0,
  by_contra' hx,
  have := intermediate_value_univ (-1) 0 (cyclotomic n ℝ).continuous,
  obtain ⟨y, hy : is_root _ y⟩ := this (show (0 : ℝ) ∈ set.Icc _ _, by simpa [h0] using hx),
  rw [is_root_cyclotomic_iff $ show (n : ℝ) ≠ 0, by exact_mod_cast (pos_of_gt hn).ne'] at hy,
  rw hy.eq_order_of at hn,
  exact hn.not_le linear_ordered_ring.order_of_le_two,
end

lemma cyclotomic_pos {n : ℕ} (hn : 2 < n) {R} [linear_ordered_comm_ring R] (x : R) :
  0 < eval x (cyclotomic n R) :=
begin
  induction n using nat.strong_induction_on with k ih,
  have hn'  : 0 < k := pos_of_gt hn,
  have hn'' : 1 < k := one_lt_two.trans hn,
  dsimp at ih,
  have := prod_cyclotomic_eq_geom_sum hn' R,
  apply_fun eval x at this,
  rw [divisors_eq_proper_divisors_insert_self_of_pos hn', insert_sdiff_of_not_mem,
      prod_insert, eval_mul, eval_geom_sum] at this,
  rotate,
  { simp only [lt_self_iff_false, mem_sdiff, not_false_iff, mem_proper_divisors, and_false,
      false_and]},
  { simpa only [mem_singleton] using hn''.ne' },
  rcases lt_trichotomy 0 (geom_sum x k) with h | h | h,
  { apply pos_of_mul_pos_right,
    { rwa this },
    rw eval_prod,
    refine prod_nonneg (λ i hi, _),
    simp only [mem_sdiff, mem_proper_divisors, mem_singleton] at hi,
    rw geom_sum_pos_iff hn'' at h,
    cases h with hk hx,
    { refine (ih _ hi.1.2 (nat.two_lt_of_ne _ hi.2 _)).le; rintro rfl,
      { exact hn'.ne' (zero_dvd_iff.mp hi.1.1) },
      { exact even_iff_not_odd.mp (even_iff_two_dvd.mpr hi.1.1) hk } },
    { rcases eq_or_ne i 2 with rfl | hk,
      { simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using hx.le },
      refine (ih _ hi.1.2 (nat.two_lt_of_ne _ hi.2 hk)).le,
      rintro rfl,
      exact (hn'.ne' $ zero_dvd_iff.mp hi.1.1) } },
  { rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn''] at h,
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn },
  { apply pos_of_mul_neg_left,
    { rwa this },
    rw [geom_sum_neg_iff hn''] at h,
    have h2 : {2} ⊆ k.proper_divisors \ {1},
    { rw [singleton_subset_iff, mem_sdiff, mem_proper_divisors, not_mem_singleton],
      exact ⟨⟨h.1, hn⟩, (nat.one_lt_bit0 one_ne_zero).ne'⟩ },
    rw [eval_prod, ←prod_sdiff h2, prod_singleton]; try { apply_instance },
    apply mul_nonpos_of_nonneg_of_nonpos,
    { refine prod_nonneg (λ i hi, le_of_lt _),
      simp only [mem_sdiff, mem_proper_divisors, mem_singleton] at hi,
      refine ih _ hi.1.1.2 (nat.two_lt_of_ne _ hi.1.2 hi.2),
      rintro rfl,
      rw zero_dvd_iff at hi,
      exact hn'.ne' hi.1.1.1 },
    { simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using h.right.le } }
end

end polynomial
