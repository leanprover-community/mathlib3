/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import data.nat.parity

/-!
# Parity of integers

This file contains theorems about the `even` and `odd` predicates on the integers.

## Tags

even, odd
-/

namespace int

variables {m n : ℤ}

@[simp] theorem mod_two_ne_one : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

local attribute [simp] -- euclidean_domain.mod_eq_zero uses (2 ∣ n) as normal form
theorem mod_two_ne_zero : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

theorem even_iff : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

theorem odd_iff : odd n ↔ n % 2 = 1 :=
⟨λ ⟨m, hm⟩, by { rw [hm, add_mod], norm_num },
 λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by { rw h, abel })⟩⟩

lemma not_even_iff : ¬ even n ↔ n % 2 = 1 :=
by rw [even_iff, mod_two_ne_zero]

lemma not_odd_iff : ¬ odd n ↔ n % 2 = 0 :=
by rw [odd_iff, mod_two_ne_one]

lemma even_iff_not_odd : even n ↔ ¬ odd n :=
by rw [not_odd_iff, even_iff]

@[simp] lemma odd_iff_not_even : odd n ↔ ¬ even n :=
by rw [not_even_iff, odd_iff]

lemma is_compl_even_odd : is_compl {n : ℤ | even n} {n | odd n} :=
by simp [← set.compl_set_of, is_compl_compl]

lemma even_or_odd (n : ℤ) : even n ∨ odd n :=
or.imp_right odd_iff_not_even.2 $ em $ even n

lemma even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 :=
by simpa only [exists_or_distrib, ← odd, ← even] using even_or_odd n

lemma even_xor_odd (n : ℤ) : xor (even n) (odd n) :=
begin
  cases even_or_odd n with h,
  { exact or.inl ⟨h, even_iff_not_odd.mp h⟩ },
  { exact or.inr ⟨h, odd_iff_not_even.mp h⟩ },
end

lemma even_xor_odd' (n : ℤ) : ∃ k, xor (n = 2 * k) (n = 2 * k + 1) :=
begin
  rcases even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩;
  use k,
  { simpa only [xor, true_and, eq_self_iff_true, not_true, or_false, and_false]
      using (succ_ne_self (2*k)).symm },
  { simp only [xor, add_right_eq_self, false_or, eq_self_iff_true, not_true, not_false_iff,
               one_ne_zero, and_self] },
end

@[simp] theorem two_dvd_ne_zero : ¬ 2 ∣ n ↔ n % 2 = 1 :=
not_even_iff

instance : decidable_pred (even : ℤ → Prop) :=
λ n, decidable_of_decidable_of_iff (by apply_instance) even_iff.symm

instance decidable_pred_odd : decidable_pred (odd : ℤ → Prop) :=
λ n, decidable_of_decidable_of_iff (by apply_instance) odd_iff_not_even.symm

@[simp] theorem even_zero : even (0 : ℤ) := ⟨0, dec_trivial⟩

@[simp] theorem not_even_one : ¬ even (1 : ℤ) :=
by rw even_iff; norm_num

@[simp] theorem even_bit0 (n : ℤ) : even (bit0 n) :=
⟨n, by rw [bit0, two_mul]⟩

@[parity_simps] theorem even_add : even (m + n) ↔ (even m ↔ even n) :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, int.add_mod];
   norm_num

theorem even.add_even (hm : even m) (hn : even n) : even (m + n) :=
even_add.2 $ iff_of_true hm hn

theorem even_add' : even (m + n) ↔ (odd m ↔ odd n) :=
by rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.add_odd (hm : odd m) (hn : odd n) : even (m + n) :=
even_add'.2 $ iff_of_true hm hn

@[simp] theorem not_even_bit1 (n : ℤ) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

lemma two_not_dvd_two_mul_add_one (n : ℤ) : ¬(2 ∣ 2 * n + 1) :=
by convert not_even_bit1 n; exact two_mul n

@[parity_simps] theorem even_sub : even (m - n) ↔ (even m ↔ even n) :=
by simp [sub_eq_add_neg] with parity_simps

theorem even.sub_even (hm : even m) (hn : even n) : even (m - n) :=
even_sub.2 $ iff_of_true hm hn

theorem even_sub' : even (m - n) ↔ (odd m ↔ odd n) :=
by rw [even_sub, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.sub_odd (hm : odd m) (hn : odd n) : even (m - n) :=
even_sub'.2 $ iff_of_true hm hn

@[parity_simps] theorem even_add_one : even (n + 1) ↔ ¬ even n :=
by simp [even_add]

@[parity_simps] theorem even_mul : even (m * n) ↔ even m ∨ even n :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, int.mul_mod];
   norm_num

theorem odd_mul : odd (m * n) ↔ odd m ∧ odd n :=
by simp [not_or_distrib] with parity_simps

theorem even.mul_left (hm : even m) (n : ℤ) : even (m * n) :=
even_mul.mpr $ or.inl hm

theorem even.mul_right (m : ℤ) (hn : even n) : even (m * n) :=
even_mul.mpr $ or.inr hn

theorem odd.mul (hm : odd m) (hn : odd n) : odd (m * n) :=
odd_mul.mpr ⟨hm, hn⟩

theorem odd.of_mul_left (h : odd (m * n)) : odd m :=
(odd_mul.mp h).1

theorem odd.of_mul_right (h : odd (m * n)) : odd n :=
(odd_mul.mp h).2

@[parity_simps] theorem even_pow {n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, even_mul, pow_succ], tauto }

theorem even_pow' {n : ℕ} (h : n ≠ 0) : even (m ^ n) ↔ even m :=
even_pow.trans $ and_iff_left h

@[parity_simps] theorem odd_add : odd (m + n) ↔ (odd m ↔ even n) :=
by rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]

theorem odd.add_even (hm : odd m) (hn : even n) : odd (m + n) :=
odd_add.2 $ iff_of_true hm hn

theorem odd_add' : odd (m + n) ↔ (odd n ↔ even m) :=
by rw [add_comm, odd_add]

theorem even.add_odd (hm : even m) (hn : odd n) : odd (m + n) :=
odd_add'.2 $ iff_of_true hn hm

lemma ne_of_odd_add (h : odd (m + n)) : m ≠ n :=
λ hnot, by simpa [hnot] with parity_simps using h

@[parity_simps] theorem odd_sub : odd (m - n) ↔ (odd m ↔ even n) :=
by rw [odd_iff_not_even, even_sub, not_iff, odd_iff_not_even]

theorem odd.sub_even (hm : odd m) (hn : even n) : odd (m - n) :=
odd_sub.2 $ iff_of_true hm hn

theorem odd_sub' : odd (m - n) ↔ (odd n ↔ even m) :=
by rw [odd_iff_not_even, even_sub, not_iff, not_iff_comm, odd_iff_not_even]

theorem even.sub_odd (hm : even m) (hn : odd n) : odd (m - n) :=
odd_sub'.2 $ iff_of_true hn hm

lemma even_mul_succ_self (n : ℤ) : even (n * (n + 1)) :=
begin
  rw even_mul,
  convert n.even_or_odd,
  simp with parity_simps
end

@[simp, norm_cast] theorem even_coe_nat (n : ℕ) : even (n : ℤ) ↔ even n :=
by rw_mod_cast [even_iff, nat.even_iff]

@[simp, norm_cast] theorem odd_coe_nat (n : ℕ) : odd (n : ℤ) ↔ odd n :=
by rw [odd_iff_not_even, nat.odd_iff_not_even, even_coe_nat]

@[simp] theorem nat_abs_even : even n.nat_abs ↔ even n :=
coe_nat_dvd_left.symm

@[simp] theorem nat_abs_odd : odd n.nat_abs ↔ odd n :=
by rw [odd_iff_not_even, nat.odd_iff_not_even, nat_abs_even]

lemma four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : odd a) (hb : odd b) : 4 ∣ a + b ∨ 4 ∣ a - b :=
begin
  obtain ⟨m, rfl⟩ := ha,
  obtain ⟨n, rfl⟩ := hb,
  obtain h|h := int.even_or_odd (m + n),
  { right,
    rw [int.even_add, ←int.even_sub] at h,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 k,
    rw [eq_add_of_sub_eq hk, mul_add, add_assoc, add_sub_cancel, ←mul_assoc],
    norm_num },
  { left,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 (k + 1),
    rw [eq_sub_of_add_eq hk, add_right_comm, ←add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ←sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ←mul_assoc,
      mul_add],
    norm_num },
end

-- Here are examples of how `parity_simps` can be used with `int`.

example (m n : ℤ) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even (25394535 : ℤ) :=
by simp

end int
