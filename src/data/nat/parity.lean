/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import data.nat.modeq
import algebra.parity

/-!
# Parity of natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
⟨λ ⟨m, hm⟩, by simp [← two_mul, hm],
  λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [← two_mul, h])⟩⟩

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
by simp only [←set.compl_set_of, is_compl_compl, odd_iff_not_even]

lemma even_or_odd (n : ℕ) : even n ∨ odd n :=
or.imp_right odd_iff_not_even.2 $ em $ even n

lemma even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 :=
by simpa only [← two_mul, exists_or_distrib, ← odd, ← even] using even_or_odd n

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
  { simpa only [← two_mul, xor, true_and, eq_self_iff_true, not_true, or_false, and_false]
      using (succ_ne_self (2*k)).symm },
  { simp only [xor, add_right_eq_self, false_or, eq_self_iff_true, not_true, not_false_iff,
              one_ne_zero, and_self] },
end

@[simp] theorem two_dvd_ne_zero : ¬ 2 ∣ n ↔ n % 2 = 1 :=
even_iff_two_dvd.symm.not.trans not_even_iff

instance : decidable_pred (even : ℕ → Prop) := λ n, decidable_of_iff _ even_iff.symm
instance : decidable_pred (odd : ℕ → Prop) := λ n, decidable_of_iff _ odd_iff_not_even.symm

theorem mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : odd n) : m % 2 + (m + n) % 2 = 1 :=
(even_or_odd m).elim (λ hm, by rw [even_iff.1 hm, odd_iff.1 (hm.add_odd hn)]) $
  λ hm, by rw [odd_iff.1 hm, even_iff.1 (hm.add_odd hn)]

@[simp] theorem mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 :=
mod_two_add_add_odd_mod_two m odd_one

@[simp] theorem succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 :=
by rw [add_comm, mod_two_add_succ_mod_two]

mk_simp_attribute parity_simps "Simp attribute for lemmas about `even`"

@[simp] theorem not_even_one : ¬ even 1 :=
by rw even_iff; norm_num

@[parity_simps] theorem even_add : even (m + n) ↔ (even m ↔ even n) :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, nat.add_mod];
   norm_num

theorem even_add' : even (m + n) ↔ (odd m ↔ odd n) :=
by rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

@[parity_simps] theorem even_add_one : even (n + 1) ↔ ¬ even n :=
by simp [even_add]

@[simp] theorem not_even_bit1 (n : ℕ) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

lemma two_not_dvd_two_mul_add_one (n : ℕ) : ¬(2 ∣ 2 * n + 1) :=
by simp [add_mod]

lemma two_not_dvd_two_mul_sub_one : Π {n} (w : 0 < n), ¬(2 ∣ 2 * n - 1)
| (n + 1) _ := two_not_dvd_two_mul_add_one n

@[parity_simps] theorem even_sub (h : n ≤ m) : even (m - n) ↔ (even m ↔ even n) :=
begin
  conv { to_rhs, rw [←tsub_add_cancel_of_le h, even_add] },
  by_cases h : even n; simp [h]
end

theorem even_sub' (h : n ≤ m) : even (m - n) ↔ (odd m ↔ odd n) :=
by rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.sub_odd (hm : odd m) (hn : odd n) : even (m - n) :=
(le_total n m).elim
  (λ h, by simp only [even_sub' h, *])
  (λ h, by simp only [tsub_eq_zero_iff_le.mpr h, even_zero])

@[parity_simps] theorem even_mul : even (m * n) ↔ even m ∨ even n :=
by cases mod_two_eq_zero_or_one m with h₁ h₁;
   cases mod_two_eq_zero_or_one n with h₂ h₂;
   simp [even_iff, h₁, h₂, nat.mul_mod];
   norm_num

theorem odd_mul : odd (m * n) ↔ odd m ∧ odd n :=
by simp [not_or_distrib] with parity_simps

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

theorem odd_add' : odd (m + n) ↔ (odd n ↔ even m) :=
by rw [add_comm, odd_add]

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

lemma even_mul_self_pred (n : ℕ) : even (n * (n - 1)) :=
begin
  cases n,
  { exact even_zero },
  { rw mul_comm,
    apply even_mul_succ_self }
end

lemma two_mul_div_two_of_even : even n → 2 * (n / 2) = n :=
 λ h, nat.mul_div_cancel_left' (even_iff_two_dvd.mp h)

lemma div_two_mul_two_of_even : even n → n / 2 * 2 = n :=
λ h, nat.div_mul_cancel (even_iff_two_dvd.mp h)

lemma two_mul_div_two_add_one_of_odd (h : odd n) : 2 * (n / 2) + 1 = n :=
by { rw mul_comm, convert nat.div_add_mod' n 2, rw odd_iff.mp h }

lemma div_two_mul_two_add_one_of_odd (h : odd n) : n / 2 * 2 + 1 = n :=
by { convert nat.div_add_mod' n 2, rw odd_iff.mp h }

lemma one_add_div_two_mul_two_of_odd (h : odd n) : 1 + n / 2 * 2 = n :=
by { rw add_comm, convert nat.div_add_mod' n 2, rw odd_iff.mp h }

lemma bit0_div_two : bit0 n / 2 = n :=
by rw [←nat.bit0_eq_bit0, bit0_eq_two_mul, two_mul_div_two_of_even (even_bit0 n)]

lemma bit1_div_two : bit1 n / 2 = n :=
by rw [←nat.bit1_eq_bit1, bit1, bit0_eq_two_mul, nat.two_mul_div_two_add_one_of_odd (odd_bit1 n)]

@[simp] lemma bit0_div_bit0 : bit0 n / bit0 m = n / m :=
by rw [bit0_eq_two_mul m, ←nat.div_div_eq_div_mul, bit0_div_two]

@[simp] lemma bit1_div_bit0 : bit1 n / bit0 m = n / m :=
by rw [bit0_eq_two_mul, ←nat.div_div_eq_div_mul, bit1_div_two]

@[simp] lemma bit0_mod_bit0 : bit0 n % bit0 m = bit0 (n % m) :=
by rw [bit0_eq_two_mul n, bit0_eq_two_mul m, bit0_eq_two_mul (n % m), nat.mul_mod_mul_left]

@[simp] lemma bit1_mod_bit0 : bit1 n % bit0 m = bit1 (n % m) :=
begin
  have h₁ := congr_arg bit1 (nat.div_add_mod n m),
  -- `∀ m n : ℕ, bit0 m * n = bit0 (m * n)` seems to be missing...
  rw [bit1_add, bit0_eq_two_mul, ← mul_assoc, ← bit0_eq_two_mul] at h₁,
  have h₂ := nat.div_add_mod (bit1 n) (bit0 m),
  rw [bit1_div_bit0] at h₂,
  exact add_left_cancel (h₂.trans h₁.symm),
end

-- Here are examples of how `parity_simps` can be used with `nat`.

example (m n : ℕ) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even 25394535 :=
by simp

end nat

open nat

namespace function
namespace involutive

variables {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_bit0 (hf : involutive f) (n : ℕ) : f^[bit0 n] = id :=
by rw [bit0, ← two_mul, iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

theorem iterate_bit1 (hf : involutive f) (n : ℕ) : f^[bit1 n] = f :=
by rw [bit1, iterate_succ, hf.iterate_bit0, comp.left_id]

theorem iterate_even (hf : involutive f) (hn : even n) : f^[n] = id :=
let ⟨m, hm⟩ := hn in hm.symm ▸ hf.iterate_bit0 m

theorem iterate_odd (hf : involutive f) (hn : odd n) : f^[n] = f :=
let ⟨m, hm⟩ := odd_iff_exists_bit1.mp hn in hm.symm ▸ hf.iterate_bit1 m

theorem iterate_eq_self (hf : involutive f) (hne : f ≠ id) : f^[n] = f ↔ odd n :=
⟨λ H, odd_iff_not_even.2 $ λ hn, hne $ by rwa [hf.iterate_even hn, eq_comm] at H, hf.iterate_odd⟩

theorem iterate_eq_id (hf : involutive f) (hne : f ≠ id) : f^[n] = id ↔ even n :=
⟨λ H, even_iff_not_odd.2 $ λ hn, hne $ by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

end involutive
end function

variables {R : Type*} [monoid R] [has_distrib_neg R] {n : ℕ}

lemma neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ even n :=
⟨λ h', of_not_not $ λ hn, h $ (odd.neg_one_pow $ odd_iff_not_even.mpr hn).symm.trans h',
  even.neg_one_pow⟩

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
lemma odd.mod_even_iff {n a : ℕ} (ha : even a) : odd (n % a) ↔ odd n :=
((even_sub' $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $
   dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
lemma even.mod_even_iff {n a : ℕ} (ha : even a) : even (n % a) ↔ even n :=
((even_sub $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $
   dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma odd.mod_even {n a : ℕ} (hn : odd n) (ha : even a) : odd (n % a) :=
(odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
lemma even.mod_even {n a : ℕ} (hn : even n) (ha : even a) : even (n % a) :=
(even.mod_even_iff ha).mpr hn

theorem odd.of_dvd_nat {m n : ℕ} (hn : odd n) (hm : m ∣ n) : odd m :=
odd_iff_not_even.2 $ mt hm.even (odd_iff_not_even.1 hn)

/-- `2` is not a factor of an odd natural number. -/
theorem odd.ne_two_of_dvd_nat {m n : ℕ} (hn : odd n) (hm : m ∣ n) : m ≠ 2 :=
begin
  rintro rfl,
  exact absurd (hn.of_dvd_nat hm) dec_trivial
end
