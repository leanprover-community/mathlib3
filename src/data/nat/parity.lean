/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import data.nat.modeq

/-!
# Parity of natural numbers

This file contains theorems about the `even` and `odd` predicates on the natural numbers.

## Tags

even, odd
-/

namespace nat

variables {m n : ℕ}

@[simp] theorem mod_two_ne_one : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

@[simp] theorem mod_two_ne_zero : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

theorem even_iff : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

theorem odd_iff : odd n ↔ n % 2 = 1 :=
⟨λ ⟨m, hm⟩, by norm_num [hm, add_mod],
 λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩⟩

lemma not_even_iff : ¬ even n ↔ n % 2 = 1 :=
by rw [even_iff, mod_two_ne_zero]

lemma not_odd_iff : ¬ odd n ↔ n % 2 = 0 :=
by rw [odd_iff, mod_two_ne_one]

lemma even_iff_not_odd : even n ↔ ¬ odd n :=
by rw [not_odd_iff, even_iff]

@[simp] lemma odd_iff_not_even : odd n ↔ ¬ even n :=
by rw [not_even_iff, odd_iff]

lemma is_compl_even_odd : is_compl {n : ℕ | even n} {n | odd n} :=
by simp [← set.compl_set_of, is_compl_compl]

lemma even_or_odd (n : ℕ) : even n ∨ odd n :=
or.imp_right odd_iff_not_even.2 $ em $ even n

lemma even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 :=
by simpa only [exists_or_distrib, ← odd, ← even] using even_or_odd n

lemma even_xor_odd (n : ℕ) : xor (even n) (odd n) :=
begin
  cases even_or_odd n with h,
  { exact or.inl ⟨h, even_iff_not_odd.mp h⟩ },
  { exact or.inr ⟨h, odd_iff_not_even.mp h⟩ },
end

lemma even_xor_odd' (n : ℕ) : ∃ k, xor (n = 2 * k) (n = 2 * k + 1) :=
begin
  rcases even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩;
  use k,
  { simpa only [xor, true_and, eq_self_iff_true, not_true, or_false, and_false]
      using (succ_ne_self (2*k)).symm },
  { simp only [xor, add_right_eq_self, false_or, eq_self_iff_true, not_true, not_false_iff,
              one_ne_zero, and_self] },
end

lemma odd_gt_zero (h : odd n) : 0 < n :=
by { obtain ⟨k, rfl⟩ := h, exact succ_pos' }

@[simp] theorem two_dvd_ne_zero : ¬ 2 ∣ n ↔ n % 2 = 1 :=
not_even_iff

instance : decidable_pred (even : ℕ → Prop) :=
λ n, decidable_of_decidable_of_iff (by apply_instance) even_iff.symm

instance decidable_pred_odd : decidable_pred (odd : ℕ → Prop) :=
λ n, decidable_of_decidable_of_iff (by apply_instance) odd_iff_not_even.symm

mk_simp_attribute parity_simps "Simp attribute for lemmas about `even`"

@[simp] theorem even_zero : even 0 := ⟨0, dec_trivial⟩

@[simp] theorem not_even_one : ¬ even 1 :=
by rw even_iff; norm_num

@[simp] theorem even_bit0 (n : ℕ) : even (bit0 n) :=
⟨n, by rw [bit0, two_mul]⟩

@[parity_simps] theorem even_add : even (m + n) ↔ (even m ↔ even n) :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, nat.add_mod];
   norm_num

theorem even.add_even (hm : even m) (hn : even n) : even (m + n) :=
even_add.2 $ iff_of_true hm hn

theorem even_add' : even (m + n) ↔ (odd m ↔ odd n) :=
by rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.add_odd (hm : odd m) (hn : odd n) : even (m + n) :=
even_add'.2 $ iff_of_true hm hn

@[simp] theorem not_even_bit1 (n : ℕ) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

lemma two_not_dvd_two_mul_add_one (n : ℕ) : ¬(2 ∣ 2 * n + 1) :=
by convert not_even_bit1 n; exact two_mul n

lemma two_not_dvd_two_mul_sub_one : Π {n} (w : 0 < n), ¬(2 ∣ 2 * n - 1)
| (n + 1) _ := two_not_dvd_two_mul_add_one n

@[parity_simps] theorem even_sub (h : n ≤ m) : even (m - n) ↔ (even m ↔ even n) :=
begin
  conv { to_rhs, rw [←nat.sub_add_cancel h, even_add] },
  by_cases h : even n; simp [h]
end

theorem even.sub_even (hm : even m) (hn : even n) : even (m - n) :=
(le_total n m).elim
  (λ h, by simp only [even_sub h, *])
  (λ h, by simp only [nat.sub_eq_zero_of_le h, even_zero])

theorem even_sub' (h : n ≤ m) : even (m - n) ↔ (odd m ↔ odd n) :=
by rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.sub_odd (hm : odd m) (hn : odd n) : even (m - n) :=
(le_total n m).elim
  (λ h, by simp only [even_sub' h, *])
  (λ h, by simp only [nat.sub_eq_zero_of_le h, even_zero])

@[parity_simps] theorem even_succ : even (succ n) ↔ ¬ even n :=
by rw [succ_eq_add_one, even_add]; simp [not_even_one]

@[parity_simps] theorem even_mul : even (m * n) ↔ even m ∨ even n :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, nat.mul_mod];
   norm_num

theorem odd_mul : odd (m * n) ↔ odd m ∧ odd n :=
by simp [not_or_distrib] with parity_simps

theorem even.mul_left (hm : even m) (n) : even (m * n) :=
even_mul.mpr $ or.inl hm

theorem even.mul_right (m) (hn : even n) : even (m * n) :=
even_mul.mpr $ or.inr hn

theorem odd.mul (hm : odd m) (hn : odd n) : odd (m * n) :=
odd_mul.mpr ⟨hm, hn⟩

theorem odd.of_mul_left (h : odd (m * n)) : odd m :=
(odd_mul.mp h).1

theorem odd.of_mul_right (h : odd (m * n)) : odd n :=
(odd_mul.mp h).2

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
@[parity_simps] theorem even_pow : even (m ^ n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, pow_succ', even_mul], tauto }

theorem even_pow' (h : n ≠ 0) : even (m ^ n) ↔ even m :=
even_pow.trans $ and_iff_left h

theorem even_div : even (m / n) ↔ m % (2 * n) / n = 0 :=
by rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, nat.div_mod_eq_mod_mul_div, mul_comm]

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

@[parity_simps] theorem odd_sub (h : n ≤ m) : odd (m - n) ↔ (odd m ↔ even n) :=
by rw [odd_iff_not_even, even_sub h, not_iff, odd_iff_not_even]

theorem odd.sub_even (h : n ≤ m) (hm : odd m) (hn : even n) : odd (m - n) :=
(odd_sub h).mpr $ iff_of_true hm hn

theorem odd_sub' (h : n ≤ m) : odd (m - n) ↔ (odd n ↔ even m) :=
by rw [odd_iff_not_even, even_sub h, not_iff, not_iff_comm, odd_iff_not_even]

theorem even.sub_odd (h : n ≤ m) (hm : even m) (hn : odd n) : odd (m - n) :=
(odd_sub' h).mpr $ iff_of_true hn hm

lemma even_mul_succ_self (n : ℕ) : even (n * (n + 1)) :=
begin
  rw even_mul,
  convert n.even_or_odd,
  simp with parity_simps
end

variables {R : Type*} [ring R]

theorem neg_one_pow_eq_one_iff_even (h1 : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ even n :=
⟨λ h, n.mod_two_eq_zero_or_one.elim (dvd_iff_mod_eq_zero _ _).2
  (λ hn, by rw [neg_one_pow_eq_pow_mod_two, hn, pow_one] at h; exact (h1 h).elim),
  λ ⟨m, hm⟩, by rw [neg_one_pow_eq_pow_mod_two, hm]; simp⟩

@[simp] theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by simp

alias nat.neg_one_sq ← nat.neg_one_pow_two

theorem neg_one_pow_of_even : even n → (-1 : R) ^ n = 1 :=
by { rintro ⟨c, rfl⟩, simp [pow_mul] }

theorem neg_one_pow_of_odd : odd n → (-1 : R) ^ n = -1 :=
by { rintro ⟨c, rfl⟩, simp [pow_add, pow_mul] }

-- Here are examples of how `parity_simps` can be used with `nat`.

example (m n : ℕ) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even 25394535 :=
by simp

end nat
