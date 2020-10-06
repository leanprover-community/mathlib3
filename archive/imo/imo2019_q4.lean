/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.padics.padic_norm ring_theory.multiplicity algebra.big_operators.intervals data.nat.log
import data.nat.parity
import tactic.interval_cases

open_locale nat big_operators
open multiplicity

lemma not_dvd_iff (n m : ℕ) : ¬ n ∣ m ↔ ∃ k, n * k < m ∧ m < n * (k + 1) :=
begin
  sorry
end

open finset

lemma multiplicity_factorial_mul_succ {n p : ℕ} (hp : prime p) :
  multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 :=
begin
  have h0 : 2 ≤ p := (nat.prime_iff_prime.mpr hp).two_le,
  have h1 : 1 ≤ p * n + 1 := nat.le_add_left _ _,
  have h2 : p * n + 1 ≤ p * (n + 1), linarith,
  have h3 : p * n + 1 ≤ p * (n + 1) + 1, linarith,
  have hm : multiplicity p (p * n)! ≠ ⊤,
  { rw [ne.def, eq_top_iff_not_finite, not_not, finite_nat_iff],
    exact ⟨(nat.prime_iff_prime.mpr hp).ne_one, nat.factorial_pos _⟩ },
  revert hm,
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), multiplicity p m = 0,
  { intros m hm, apply multiplicity_eq_zero_of_not_dvd,
    rw [not_dvd_iff], rw [Ico.mem] at hm,
    exact ⟨n, nat.lt_of_succ_le hm.1, hm.2⟩,  },
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.finset.prod hp, ← sum_Ico_consecutive _ h1 h3,
    add_assoc], intro h,
  rw [enat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp,
    multiplicity_self hp.not_unit hp.ne_zero, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm (1 : enat)]
end

lemma multiplicity_factorial_mul {n p : ℕ} (hp : prime p) :
  multiplicity p (p * n)! = multiplicity p n! + n :=
begin
  induction n with n ih,
  { simp },
  { simp [nat.succ_eq_add_one, multiplicity.mul, hp, ih, multiplicity_factorial_mul_succ,
      add_assoc, add_left_comm] }
end

@[simp] lemma bit_ff_val (n : ℕ) : n.bit ff = 2 * n := n.bit0_val

@[simp] lemma bit_tt_val (n : ℕ) : n.bit tt = 2 * n + 1 := n.bit1_val

@[simp] lemma bit_eq_zero {n : ℕ} {b : bool} : n.bit b = 0 ↔ n = 0 ∧ b = ff :=
by { cases b; norm_num }

namespace enat

protected lemma zero_lt_one : (0 : enat) < 1 :=
by { norm_cast, norm_num }

end enat

lemma multiplicity_two_factorial_lt : ∀ (n : ℕ) (h : n ≠ 0), multiplicity 2 n! < n :=
begin
  have h2 := nat.prime_iff_prime.mp nat.prime_two,
  refine nat.binary_rec _ _,
  { contradiction },
  { intros b n ih h,
    by_cases hn : n = 0,
    { subst hn, simp at h, simp [h, one_right h2.not_unit, enat.zero_lt_one] },
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ),
    { rw [multiplicity_factorial_mul h2],
      refine (enat.add_lt_add_right (ih hn) (enat.coe_ne_top _)).trans_le _,
      rw [two_mul], norm_cast },
    cases b,
    { simpa },
    { simp [nat.succ_eq_add_one, multiplicity.mul, h2],
      rw [multiplicity_eq_zero_of_not_dvd (nat.two_not_dvd_two_mul_add_one n), zero_add],
      refine this.trans _,
      exact_mod_cast nat.lt_succ_self _ }}
end

namespace nat

lemma ne_of_eq_monotone {α} [preorder α] {f : ℕ → α} (hf : monotone f)
  (x x' : ℕ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y :=
by { rintro rfl, apply not_le_of_lt (reflect_lt hf h1), exact le_of_lt_succ (reflect_lt hf h2) }

end nat

namespace finset

variables {α : Type*}

protected lemma sum_nat_coe_enat (s : finset α) (f : α → ℕ) :
  (∑ x in s, (f x : enat)) = (∑ x  in s, f x : ℕ) :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has, ih] }
end

end finset

namespace multiplicity

variables {p : ℕ}

lemma multiplicity_two_factorial_int_lt {n : ℕ} (hn : n > 0) : multiplicity 2 (n! : ℤ) < n :=
by { change multiplicity ((2 : ℕ) : ℤ) (n! : ℤ) < _,
  simp_rw [int.coe_nat_multiplicity, multiplicity_two_factorial_lt n (hn.lt.ne.symm)] }

end multiplicity
open multiplicity

theorem IMO2019_4_upper_bound {k n : ℕ} (hk : k > 0)
  (h : (k! : ℤ) = (range n).prod (λ i, 2 ^ n - 2 ^ i)) : n < 6 :=
begin
  have prime_2 : prime (2 : ℤ),
  { show prime ((2:ℕ) : ℤ), rw [← nat.prime_iff_prime_int], exact nat.prime_two },
  have h2 : n * (n - 1) / 2 < k,
  { rw [← enat.coe_lt_coe], convert multiplicity_two_factorial_int_lt hk, symmetry,
    rw [h, multiplicity.finset.prod prime_2, ← sum_range_id, ← finset.sum_nat_coe_enat],
    apply sum_congr rfl, intros i hi,
    rw [multiplicity_sub_of_gt, multiplicity_pow_self_of_prime prime_2],
    rwa [multiplicity_pow_self_of_prime prime_2, multiplicity_pow_self_of_prime prime_2,
      enat.coe_lt_coe, ←mem_range] },
  rw [←not_le], intro hn,
  apply ne_of_lt _ h.symm,
  suffices : ((range n).prod (λ i, 2 ^ n) : ℤ) < ↑k!,
  { apply lt_of_le_of_lt _ this, apply prod_le_prod,
    { intros, rw [sub_nonneg], apply pow_le_pow, norm_num, apply le_of_lt, rwa [← mem_range] },
    { intros, apply sub_le_self, apply pow_nonneg, norm_num }},
  suffices : 2 ^ (n * n) < (n * (n - 1) / 2)!,
  { rw [prod_const, card_range, ← pow_mul], rw [← int.coe_nat_lt_coe_nat_iff] at this,
    convert lt_trans this _, norm_cast, rwa [int.coe_nat_lt_coe_nat_iff, nat.factorial_lt],
    refine nat.div_pos _ (by norm_num),
    refine le_trans _ (mul_le_mul hn (nat.pred_le_pred hn) (zero_le _) (zero_le _)),
    norm_num },
  refine nat.le_induction _ _ n hn, { norm_num },
  intros n' hn' ih,
  have h5 : 1 ≤ 2 * n',
  { apply nat.succ_le_of_lt, apply mul_pos, norm_num,
    exact lt_of_lt_of_le (by norm_num) hn' },
  have : 2 ^ (2 + 2) ≤ (n' * (n' - 1) / 2).succ,
  { change nat.succ (6 * (6 - 1) / 2) ≤ _,
    apply nat.succ_le_succ, apply nat.div_le_div_right,
    exact mul_le_mul hn' (nat.pred_le_pred hn') (zero_le _) (zero_le _) },
  rw [nat.triangle_succ], apply lt_of_lt_of_le _ nat.factorial_mul_pow_le_factorial,
  refine lt_of_le_of_lt _ (mul_lt_mul ih (nat.pow_le_pow_of_le_left this _)
    (pow_pos (by norm_num) _) (zero_le _)),
  rw [← pow_mul, ← pow_add], apply nat.pow_le_pow_of_le_right, norm_num,
  rw [add_mul 2 2],
  convert (add_le_add_left (add_le_add_left h5 (2 * n')) (n' * n')) using 1, ring
end

theorem IMO2019_4 {k n : ℕ} : k > 0 → n > 0 →
  ((k! : ℤ) = (range n).prod (λ i, 2 ^ n - 2 ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2)) :=
begin
  intros hk hn, split, swap,
  { rintro (h|h); simp [prod.ext_iff] at h; rcases h with ⟨rfl, rfl⟩;
    norm_num [prod_range_succ, nat.succ_mul] },
  intro h,
  have := IMO2019_4_upper_bound hk h,
  interval_cases n,
  { left, congr, norm_num at h, norm_cast at h, rw [nat.factorial_eq_one] at h, apply antisymm h,
    apply nat.succ_le_of_lt hk },
  { right, congr, norm_num [prod_range_succ] at h, norm_cast at h, rw [← nat.factorial_inj],
    exact h, rw [h], norm_num },
  all_goals { exfalso, norm_num [prod_range_succ] at h, norm_cast at h, },
  { refine nat.ne_of_eq_monotone nat.monotone_factorial 5 _ _ _ h; norm_num },
  { refine nat.ne_of_eq_monotone nat.monotone_factorial 7 _ _ _ h; norm_num },
  { refine nat.ne_of_eq_monotone nat.monotone_factorial 10 _ _ _ h; norm_num },
end
