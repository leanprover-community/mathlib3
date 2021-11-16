/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic.linarith

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `lxor`, which are defined in core.

## Main results
* `eq_of_test_bit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_test_bit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/

open function

namespace nat

@[simp] lemma bit_ff : bit ff = bit0 := rfl
@[simp] lemma bit_tt : bit tt = bit1 := rfl

@[simp] lemma bit_eq_zero {n : ℕ} {b : bool} : n.bit b = 0 ↔ n = 0 ∧ b = ff :=
by { cases b; norm_num [bit0_eq_zero, nat.bit1_ne_zero] }

lemma zero_of_test_bit_eq_ff {n : ℕ} (h : ∀ i, test_bit n i = ff) : n = 0 :=
begin
  induction n using nat.binary_rec with b n hn,
  { refl },
  { have : b = ff := by simpa using h 0,
    rw [this, bit_ff, bit0_val, hn (λ i, by rw [←h (i + 1), test_bit_succ]), mul_zero] }
end

@[simp] lemma zero_test_bit (i : ℕ) : test_bit 0 i = ff :=
by simp [test_bit]

/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
lemma eq_of_test_bit_eq {n m : ℕ} (h : ∀ i, test_bit n i = test_bit m i) : n = m :=
begin
  induction n using nat.binary_rec with b n hn generalizing m,
  { simp only [zero_test_bit] at h,
    exact (zero_of_test_bit_eq_ff (λ i, (h i).symm)).symm },
  induction m using nat.binary_rec with b' m hm,
  { simp only [zero_test_bit] at h,
    exact zero_of_test_bit_eq_ff h },
  suffices h' : n = m,
  { rw [h', show b = b', by simpa using h 0] },
  exact hn (λ i, by convert h (i + 1) using 1; rw test_bit_succ)
end

lemma exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
  ∃ i, test_bit n i = tt ∧ ∀ j, i < j → test_bit n j = ff :=
begin
  induction n using nat.binary_rec with b n hn,
  { exact false.elim (h rfl) },
  by_cases h' : n = 0,
  { subst h',
    rw (show b = tt, by { revert h, cases b; simp }),
    refine ⟨0, ⟨by rw [test_bit_zero], λ j hj, _⟩⟩,
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj),
    rw [test_bit_succ, zero_test_bit] },
  { obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h',
    refine ⟨k + 1, ⟨by rw [test_bit_succ, hk], λ j hj, _⟩⟩,
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0, by linarith),
    exact (test_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj)) }
end

lemma lt_of_test_bit {n m : ℕ} (i : ℕ) (hn : test_bit n i = ff) (hm : test_bit m i = tt)
  (hnm : ∀ j, i < j → test_bit n j = test_bit m j) : n < m :=
begin
  induction n using nat.binary_rec with b n hn' generalizing i m,
  { contrapose! hm,
    rw le_zero_iff at hm,
    simp [hm] },
  induction m using nat.binary_rec with b' m hm' generalizing i,
  { exact false.elim (bool.ff_ne_tt ((zero_test_bit i).symm.trans hm)) },
  by_cases hi : i = 0,
  { subst hi,
    simp only [test_bit_zero] at hn hm,
    have : n = m,
    { exact eq_of_test_bit_eq (λ i, by convert hnm (i + 1) dec_trivial using 1; rw test_bit_succ) },
    rw [hn, hm, this, bit_ff, bit_tt, bit0_val, bit1_val],
    exact lt_add_one _ },
  { obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi,
    simp only [test_bit_succ] at hn hm,
    have := hn' _ hn hm (λ j hj, by convert hnm j.succ (succ_lt_succ hj) using 1; rw test_bit_succ),
    cases b; cases b';
    simp only [bit_ff, bit_tt, bit0_val n, bit1_val n, bit0_val m, bit1_val m];
    linarith }
end

@[simp]
lemma test_bit_two_pow_self (n : ℕ) : test_bit (2 ^ n) n = tt :=
by rw [test_bit, shiftr_eq_div_pow, nat.div_self (pow_pos zero_lt_two n), bodd_one]

lemma test_bit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : test_bit (2 ^ n) m = ff :=
begin
  rw [test_bit, shiftr_eq_div_pow],
  cases hm.lt_or_lt with hm hm,
  { rw [nat.div_eq_zero, bodd_zero],
    exact nat.pow_lt_pow_of_lt_right one_lt_two hm },
  { rw [pow_div hm.le zero_lt_two, ← tsub_add_cancel_of_le (succ_le_of_lt $ tsub_pos_of_lt hm)],
    simp [pow_succ] }
end

lemma test_bit_two_pow (n m : ℕ) : test_bit (2 ^ n) m = (n = m) :=
begin
  by_cases n = m,
  { cases h,
    simp },
  { rw test_bit_two_pow_of_ne h,
    simp [h] }
end

/-- If `f` is a commutative operation on bools such that `f ff ff = ff`, then `bitwise f` is also
    commutative. -/
lemma bitwise_comm {f : bool → bool → bool} (hf : ∀ b b', f b b' = f b' b)
  (hf' : f ff ff = ff) (n m : ℕ) : bitwise f n m = bitwise f m n :=
suffices bitwise f = swap (bitwise f), by conv_lhs { rw this },
calc bitwise f = bitwise (swap f) : congr_arg _ $ funext $ λ _, funext $ hf _
     ...       = swap (bitwise f) : bitwise_swap hf'

lemma lor_comm (n m : ℕ) : lor n m = lor m n := bitwise_comm bool.bor_comm rfl n m
lemma land_comm (n m : ℕ) : land n m = land m n := bitwise_comm bool.band_comm rfl n m
lemma lxor_comm (n m : ℕ) : lxor n m = lxor m n := bitwise_comm bool.bxor_comm rfl n m

@[simp] lemma zero_lxor (n : ℕ) : lxor 0 n = n := by simp [lxor]
@[simp] lemma lxor_zero (n : ℕ) : lxor n 0 = n := by simp [lxor]

@[simp] lemma zero_land (n : ℕ) : land 0 n = 0 := by simp [land]
@[simp] lemma land_zero (n : ℕ) : land n 0 = 0 := by simp [land]

@[simp] lemma zero_lor (n : ℕ) : lor 0 n = n := by simp [lor]
@[simp] lemma lor_zero (n : ℕ) : lor n 0 = n := by simp [lor]

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
meta def bitwise_assoc_tac : tactic unit :=
`[induction n using nat.binary_rec with b n hn generalizing m k,
  { simp },
  induction m using nat.binary_rec with b' m hm,
  { simp },
  induction k using nat.binary_rec with b'' k hk;
  simp [hn]]

lemma lxor_assoc (n m k : ℕ) : lxor (lxor n m) k = lxor n (lxor m k) := by bitwise_assoc_tac
lemma land_assoc (n m k : ℕ) : land (land n m) k = land n (land m k) := by bitwise_assoc_tac
lemma lor_assoc (n m k : ℕ) : lor (lor n m) k = lor n (lor m k) := by bitwise_assoc_tac

@[simp] lemma lxor_self (n : ℕ) : lxor n n = 0 :=
zero_of_test_bit_eq_ff $ λ i, by simp

lemma lxor_right_inj {n m m' : ℕ} (h : lxor n m = lxor n m') : m = m' :=
calc m = lxor n (lxor n m') : by simp [←lxor_assoc, ←h]
   ... = m' : by simp [←lxor_assoc]

lemma lxor_left_inj {n n' m : ℕ} (h : lxor n m = lxor n' m) : n = n' :=
by { rw [lxor_comm n m, lxor_comm n' m] at h, exact lxor_right_inj h }

lemma lxor_eq_zero {n m : ℕ} : lxor n m = 0 ↔ n = m :=
⟨by { rw ←lxor_self m, exact lxor_left_inj }, by { rintro rfl, exact lxor_self _ }⟩

lemma lxor_trichotomy {a b c : ℕ} (h : lxor a (lxor b c) ≠ 0) :
  lxor b c < a ∨ lxor a c < b ∨ lxor a b < c :=
begin
  set v := lxor a (lxor b c) with hv,

  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : lxor a b = lxor c v,
  { rw hv, conv_rhs { rw lxor_comm, simp [lxor_assoc] } },
  have hac : lxor a c = lxor b v,
  { rw hv,
    conv_rhs { congr, skip, rw lxor_comm },
    rw [←lxor_assoc, ←lxor_assoc, lxor_self, zero_lxor, lxor_comm] },
  have hbc : lxor b c = lxor a v,
  { simp [hv, ←lxor_assoc] },

  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit h,
  have : test_bit a i = tt ∨ test_bit b i = tt ∨ test_bit c i = tt,
  { contrapose! hi,
    simp only [eq_ff_eq_not_eq_tt, ne, test_bit_lxor] at ⊢ hi,
    rw [hi.1, hi.2.1, hi.2.2, bxor_ff, bxor_ff] },

  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
  -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
  rcases this with h|h|h;
  [{ left, rw hbc }, { right, left, rw hac }, { right, right, rw hab }];
  exact lt_of_test_bit i (by simp [h, hi]) h (λ j hj, by simp [hi' _ hj])
end

end nat
