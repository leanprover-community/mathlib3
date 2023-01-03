/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.pow
import data.nat.bits

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 Lemmas about `size`. -/

namespace nat

/-! ### `shiftl` and `shiftr` -/

lemma shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
| 0     := (nat.mul_one _).symm
| (k+1) := show bit0 (shiftl m k) = m * (2 * 2 ^ k),
  by rw [bit0_val, shiftl_eq_mul_pow, mul_left_comm, mul_comm 2]

lemma shiftl'_tt_eq_mul_pow (m) : ∀ n, shiftl' tt m n + 1 = (m + 1) * 2 ^ n
| 0     := by simp [shiftl, shiftl', pow_zero, nat.one_mul]
| (k+1) :=
begin
  change bit1 (shiftl' tt m k) + 1 = (m + 1) * (2 * 2 ^ k),
  rw bit1_val,
  change 2 * (shiftl' tt m k + 1) = _,
  rw [shiftl'_tt_eq_mul_pow, mul_left_comm, mul_comm 2],
end

lemma one_shiftl (n) : shiftl 1 n = 2 ^ n :=
(shiftl_eq_mul_pow _ _).trans (nat.one_mul _)

@[simp] lemma zero_shiftl (n) : shiftl 0 n = 0 :=
(shiftl_eq_mul_pow _ _).trans (nat.zero_mul _)

lemma shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
| 0     := (nat.div_one _).symm
| (k+1) := (congr_arg div2 (shiftr_eq_div_pow k)).trans $
           by rw [div2_val, nat.div_div_eq_div_mul, mul_comm]; refl

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 :=
(shiftr_eq_div_pow _ _).trans (nat.zero_div _)

theorem shiftl'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftl' b m n ≠ 0 :=
by induction n; simp [bit_ne_zero, shiftl', *]

theorem shiftl'_tt_ne_zero (m) : ∀ {n} (h : n ≠ 0), shiftl' tt m n ≠ 0
| 0        h := absurd rfl h
| (succ n) _ := nat.bit1_ne_zero _

/-! ### `size` -/

@[simp] theorem size_zero : size 0 = 0 := by simp [size]

@[simp] theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) :=
begin
  rw size,
  conv { to_lhs, rw [binary_rec], simp [h] },
  rw div2_bit,
end

@[simp] theorem size_bit0 {n} (h : n ≠ 0) : size (bit0 n) = succ (size n) :=
@size_bit ff n (nat.bit0_ne_zero h)

@[simp] theorem size_bit1 (n) : size (bit1 n) = succ (size n) :=
@size_bit tt n (nat.bit1_ne_zero n)

@[simp] theorem size_one : size 1 = 1 :=
show size (bit1 0) = 1, by rw [size_bit1, size_zero]

@[simp] theorem size_shiftl' {b m n} (h : shiftl' b m n ≠ 0) :
  size (shiftl' b m n) = size m + n :=
begin
  induction n with n IH; simp [shiftl'] at h ⊢,
  rw [size_bit h, nat.add_succ],
  by_cases s0 : shiftl' b m n = 0; [skip, rw [IH s0]],
  rw s0 at h ⊢,
  cases b, {exact absurd rfl h},
  have : shiftl' tt m n + 1 = 1 := congr_arg (+1) s0,
  rw [shiftl'_tt_eq_mul_pow] at this,
  obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩),
  rw one_mul at this,
  obtain rfl : n = 0 := nat.eq_zero_of_le_zero (le_of_not_gt $ λ hn,
    ne_of_gt (pow_lt_pow_of_lt_right dec_trivial hn) this),
  refl
end

@[simp] theorem size_shiftl {m} (h : m ≠ 0) (n) :
  size (shiftl m n) = size m + n :=
size_shiftl' (shiftl'_ne_zero_left _ h _)

theorem lt_size_self (n : ℕ) : n < 2^size n :=
begin
  rw [← one_shiftl],
  have : ∀ {n}, n = 0 → n < shiftl 1 (size n), { simp },
  apply binary_rec _ _ n, {apply this rfl},
  intros b n IH,
  by_cases bit b n = 0, {apply this h},
  rw [size_bit h, shiftl_succ],
  exact bit_lt_bit0 _ IH
end

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2^n :=
⟨λ h, lt_of_lt_of_le (lt_size_self _) (pow_le_pow_of_le_right dec_trivial h),
begin
  rw [← one_shiftl], revert n,
  apply binary_rec _ _ m,
  { intros n h, simp },
  { intros b m IH n h,
    by_cases e : bit b m = 0, { simp [e] },
    rw [size_bit e],
    cases n with n,
    { exact e.elim (nat.eq_zero_of_le_zero (le_of_lt_succ h)) },
    { apply succ_le_succ (IH _),
      apply lt_imp_lt_of_le_imp_le (λ h', bit0_le_bit _ h') h } }
end⟩

theorem lt_size {m n : ℕ} : m < size n ↔ 2^m ≤ n :=
by rw [← not_lt, decidable.iff_not_comm, not_lt, size_le]

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n :=
by rw lt_size; refl

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 :=
by have := @size_pos n; simp [pos_iff_ne_zero] at this;
   exact decidable.not_iff_not.1 this

theorem size_pow {n : ℕ} : size (2^n) = n+1 :=
le_antisymm
  (size_le.2 $ pow_lt_pow_of_lt_right dec_trivial (lt_succ_self _))
  (lt_size.2 $ le_rfl)

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
size_le.2 $ lt_of_le_of_lt h (lt_size_self _)

lemma size_eq_bits_len (n : ℕ) : n.bits.length = n.size :=
begin
  induction n using nat.binary_rec' with b n h ih, { simp, },
  rw [size_bit, bits_append_bit _ _ h],
  { simp [ih], },
  { simpa [bit_eq_zero_iff], }
end

end nat
