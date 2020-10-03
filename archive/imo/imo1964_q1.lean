/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa
-/

import field_theory.finite.basic

lemma modfact (n : ℕ) : (2^n : zmod 7) = 2 ^ (n : zmod 3).val :=
begin
  have h1 : ∀ (k : ℕ), k < 6 → (2^k : zmod 7) = 2 ^ (k : zmod 3).val := by dec_trivial,
  haveI : fact (nat.prime 7) := by { delta fact, norm_num },
  have h2 : (2 : zmod 7) ≠ 0 := dec_trivial,
  rw ← nat.mod_add_div n 6,
  simp only [h2, pow_add, pow_mul, bit0_zero, one_pow, add_zero, mul_one, zmod.cast_self,
    zmod.pow_bit0, nat.cast_bit0, zero_mul, ne.def, nat.cast_add, not_false_iff, nat.cast_mul],
  apply h1,
  apply nat.mod_lt,
  norm_num,
end

/- TODO(?) : Refactor to only use `%` -/
lemma modfact' (n : ℕ) : (2^n : ℕ) % 7 = 2^(n % 3) % 7 :=
begin
  have h1 : ∀(k : ℕ), k < 6 → ((2^k : ℕ) % 7) = 2^(k % 3) % 7 := by dec_trivial,
  haveI : fact (nat.prime 7) := by { delta fact, norm_num },
  have h2 : (2 % 7) ≠ 0 := dec_trivial,
  rw ← nat.mod_add_div n 6,
  have : 6 * (n / 6) % 3 = 0, sorry,
  --simp similar to above
  sorry,
end


/-!
# IMO 1964 Q1

* (a) Find all positive integers `n` for which `2^n-1` is divisible by `7`.
* (b) Prove that there is no positive integer `n` for which `2^n+1` is divisible by `7`.
-/

lemma nonneg (n : ℕ) (gt_zero : 0 < n) : 1 ≤ (2^n : ℤ) :=
begin
    { induction gt_zero with k h1 h2,
      simp only [nat.succ_pos', pow_one, nat.one_le_bit0_iff],
      rw [pow_succ,mul_comm],
      suffices : 1 * (1 : ℤ) ≤ 2^k * 2, rwa mul_one (1 : ℤ) at this,
      apply int.mul_le_mul h2;
      linarith, }
end

lemma modcoe (n : ℕ) (gt_zero : 0 < n) : (↑(2^n-1) : zmod 7) = 2^n-1 :=
begin
  have nonne := nonneg n gt_zero,
  suffices : ((2^n-1) : ℕ) = 2^n-1,
  have h1 : 1 ≤ 2^n := by linarith,
  sorry,
  exact ⟨_⟩,
end


example (n : ℕ) (gt_zero : 0 < n) : 7 ∣ 2^(n : ℕ) -1 ↔ 3 ∣ n :=
begin
  repeat {rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd]},
  split,
  { intro hn,
    rw [(modcoe n gt_zero), modfact] at hn,
    have h1 := zmod.val_lt (n : zmod 3),
    have h2 : (n : zmod 3).val = 0 ∨ (n : zmod 3).val = 1 ∨ (n : zmod 3).val = 2 := by omega,
    cases h2,
    exact fin.ext h2,
    cases h2;
    rw h2 at hn;
    exfalso;
    norm_num at hn,
    contrapose! hn,
    dec_trivial,},
  { intro hn,
    rw [(modcoe n gt_zero), modfact, hn],
    norm_num,}
end

example (n : ℕ) (gt_zero : 0 < n) : ¬(7 ∣ (2^n + 1)) :=
begin
  intro hn,
  rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd] at hn,
  simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_pow] at hn,
  have h1 := zmod.val_lt (n : zmod 3),
  have h2 : (n : zmod 3).val = 0 ∨ (n : zmod 3).val = 1 ∨ (n : zmod 3).val = 2 := by omega,
  rw [modfact] at hn,
  repeat {cases h2};
  rw h2 at hn; ring at hn; contrapose! hn; dec_trivial,
end
