/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import field_theory.finite.basic

/-!
# IMO 2005 Q4

Problem: Determine all positive integers relatively prime to all the terms of the infinite sequence
`a n = 2 ^ n + 3 ^ n + 6 ^ n − 1`, for `n ≥ 1`.

This is quite an easy problem, in which the key point is a modular arithmetic calculation with
the sequence `a n` relative to an arbitrary prime.
-/

/-- The sequence considered in the problem, `2 ^ n + 3 ^ n + 6 ^ n - 1`. -/
def a (n : ℕ) : ℤ := 2 ^ n + 3 ^ n + 6 ^ n - 1

/-- Key lemma (a modular arithmetic calculation):  Given a prime `p` other than `2` or `3`, the
`p - 2`th term of the sequence has `p` as a factor. -/
lemma find_specified_factor {p : ℕ} (hp : nat.prime p) (hp' : is_coprime (6:ℤ) p) :
  ↑p ∣ a (p - 2) :=
begin
  rw [← int.modeq_zero_iff_dvd],
  -- Since `p` and `6` are coprime, `6` has an inverse mod `p`
  obtain ⟨b, hb⟩ : ∃ (b : ℤ), 6 * b ≡ 1 [ZMOD p],
  { refine int.mod_coprime _,
    exact nat.is_coprime_iff_coprime.mp hp' },
  -- Also since `p` is coprime to `6`, it's coprime to `2` and `3`
  have hp₂ : is_coprime (2:ℤ) p := (id hp' : is_coprime (3 * 2 : ℤ) p).of_mul_left_right,
  have hp₃ : is_coprime (3:ℤ) p := (id hp' : is_coprime (2 * 3 : ℤ) p).of_mul_left_right,
  -- Slightly painful nat-subtraction calculation
  have hp_sub_one : p - 1 = (p - 2) + 1,
  { have : 1 ≤ p - 1 := le_tsub_of_add_le_right hp.two_le,
    conv_lhs { rw ← nat.sub_add_cancel this },
    refl },
  -- Main calculation: `6 * a (p - 2)` is a multiple of `p`
  have H : (6:ℤ) * a (p - 2) ≡ 0 [ZMOD p],
  calc (6:ℤ) * a (p - 2)
      = 3 * 2 ^ (p - 1) + 2 * 3 ^ (p - 1) + 6 ^ (p - 1) - 6 :
  by { simp only [a, mul_add, mul_sub, hp_sub_one, pow_succ], ring, }
  ... ≡ 3 * 1 + 2 * 1 + 1 - 6 [ZMOD p] : -- At this step we use Fermat's little theorem
  by { apply_rules [int.modeq.sub_right, int.modeq.add, int.modeq.mul_left,
    int.modeq.pow_card_sub_one_eq_one hp] }
  ... = 0 : by norm_num,
  -- Since `6` has an inverse mod `p`, `a (p - 2)` itself is a multiple of `p`
  calc (a (p - 2) : ℤ) = 1 * a (p - 2) : by ring
  ... ≡ (6 * b) * a (p - 2) [ZMOD p] : int.modeq.mul_right _ hb.symm
  ... = b * (6 * a (p - 2)) : by ring
  ... ≡ b * 0 [ZMOD p] : int.modeq.mul_left _ H
  ... = 0 : by ring,
end

/-- Main statement:  The only positive integer coprime to all terms of the sequence `a` is `1`. -/
example {k : ℕ} (hk : 0 < k) : (∀ n : ℕ, 1 ≤ n → is_coprime (a n) k) ↔ k = 1 :=
begin
  split, rotate,
  { -- The property is clearly true for `k = 1`
    rintros rfl n hn,
    exact is_coprime_one_right },
  intros h,
  -- Conversely, suppose `k` is a number with the property, and let `p` be `k.min_fac` (by
  -- definition this is the minimal prime factor of `k` if `k ≠ 1`, and otherwise `1`.
  let p := k.min_fac,
  -- Testing the special property of `k` for `48`, the second term of the sequence, we see that `p`
  -- is coprime to `6`.
  have hp₆ : is_coprime (6:ℤ) p,
  { refine is_coprime.of_coprime_of_dvd_right _ (int.coe_nat_dvd.mpr k.min_fac_dvd),
    exact (id (h 2 one_le_two) : is_coprime (8 * 6 : ℤ) k).of_mul_left_right, },
  -- In particular `p` is coprime to `2` (we record the `nat.coprime` version since that's what's
  -- needed later).
  have hp₂ : nat.coprime 2 p,
  { rw ← nat.is_coprime_iff_coprime,
    exact (id hp₆ : is_coprime (3 * 2 : ℤ) p).of_mul_left_right },
  -- Suppose for the sake of contradiction that `k ≠ 1`.  Then `p` is genuinely a prime factor of
  -- `k`.
  by_contra hk',
  have hp : nat.prime p := nat.min_fac_prime hk',
  -- So `3 ≤ p`
  have hp₃ : 3 ≤ p,
  { have : 2 ≠ p := by rwa nat.coprime_primes (by norm_num : nat.prime 2) hp at hp₂,
    apply nat.lt_of_le_and_ne hp.two_le this, },
  -- Testing the special property of `k` for the `p - 2`th term of the sequence, we see that `p` is
  -- coprime to `a (p - 2)`.
  have : is_coprime ↑p (a (p - 2)),
  { refine ((h (p - 2) _).of_coprime_of_dvd_right (int.coe_nat_dvd.mpr k.min_fac_dvd)).symm,
    exact le_tsub_of_add_le_right hp₃ },
  rw (nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd at this,
  -- But also, by our previous lemma, `p` divides `a (p - 2)`.
  have : ↑p ∣ a (p - 2) := find_specified_factor hp hp₆,
  -- Contradiction!
  contradiction,
end
