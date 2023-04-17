/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import algebra.group_power.order

/-! # `nat.pow`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Results on the power operation on natural numbers.
-/

namespace nat

/-! ### `pow` -/

-- This is redundant with `pow_le_pow_of_le_left'`,
-- We leave a version in the `nat` namespace as well.
-- (The global `pow_le_pow_of_le_left` needs an extra hypothesis `0 ≤ x`.)
protected theorem pow_le_pow_of_le_left {x y : ℕ} (H : x ≤ y) : ∀ i : ℕ, x^i ≤ y^i :=
pow_le_pow_of_le_left' H

theorem pow_le_pow_of_le_right {x : ℕ} (H : 0 < x) {i j : ℕ} (h : i ≤ j) : x ^ i ≤ x ^ j :=
pow_le_pow' H h

theorem pow_lt_pow_of_lt_left {x y : ℕ} (H : x < y) {i} (h : 0 < i) : x^i < y^i :=
pow_lt_pow_of_lt_left H (zero_le _) h

theorem pow_lt_pow_of_lt_right {x : ℕ} (H : 1 < x) {i j : ℕ} (h : i < j) : x^i < x^j :=
pow_lt_pow H h

lemma pow_lt_pow_succ {p : ℕ} (h : 1 < p) (n : ℕ) : p^n < p^(n+1) :=
pow_lt_pow_of_lt_right h n.lt_succ_self

lemma le_self_pow {n : ℕ} (hn : n ≠ 0) : ∀ m : ℕ, m ≤ m ^ n
| 0 := zero_le _
| (m + 1) := _root_.le_self_pow dec_trivial hn

lemma lt_pow_self {p : ℕ} (h : 1 < p) : ∀ n : ℕ, n < p ^ n
| 0 := by simp [zero_lt_one]
| (n+1) := calc
  n + 1 < p^n + 1 : nat.add_lt_add_right (lt_pow_self _) _
    ... ≤ p ^ (n+1) : pow_lt_pow_succ h _

lemma lt_two_pow (n : ℕ) : n < 2^n :=
lt_pow_self dec_trivial n

lemma one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m^n :=
by { rw ←one_pow n, exact nat.pow_le_pow_of_le_left h n }
lemma one_le_pow' (n m : ℕ) : 1 ≤ (m+1)^n := one_le_pow n (m+1) (succ_pos m)

lemma one_le_two_pow (n : ℕ) : 1 ≤ 2^n := one_le_pow n 2 dec_trivial

lemma one_lt_pow (n m : ℕ) (h₀ : 0 < n) (h₁ : 1 < m) : 1 < m^n :=
by { rw ←one_pow n, exact pow_lt_pow_of_lt_left h₁ h₀ }
lemma one_lt_pow' (n m : ℕ) : 1 < (m+2)^(n+1) :=
one_lt_pow (n+1) (m+2) (succ_pos n) (nat.lt_of_sub_eq_succ rfl)

@[simp] lemma one_lt_pow_iff {k n : ℕ} (h : 0 ≠ k) : 1 < n ^ k ↔ 1 < n :=
begin
  cases n,
  { cases k; simp [zero_pow_eq] },
  cases n,
  { rw one_pow },
  refine ⟨λ _, one_lt_succ_succ n, λ _, _⟩,
  induction k with k hk,
  { exact absurd rfl h },
  cases k,
  { simp },
  exact one_lt_mul (one_lt_succ_succ _).le (hk (succ_ne_zero k).symm),
end

lemma one_lt_two_pow (n : ℕ) (h₀ : 0 < n) : 1 < 2^n := one_lt_pow n 2 h₀ dec_trivial
lemma one_lt_two_pow' (n : ℕ) : 1 < 2^(n+1) := one_lt_pow (n+1) 2 (succ_pos n) dec_trivial

lemma pow_right_strict_mono {x : ℕ} (k : 2 ≤ x) : strict_mono (λ (n : ℕ), x^n) :=
λ _ _, pow_lt_pow_of_lt_right k

lemma pow_le_iff_le_right {x m n : ℕ} (k : 2 ≤ x) : x^m ≤ x^n ↔ m ≤ n :=
strict_mono.le_iff_le (pow_right_strict_mono k)

lemma pow_lt_iff_lt_right {x m n : ℕ} (k : 2 ≤ x) : x^m < x^n ↔ m < n :=
strict_mono.lt_iff_lt (pow_right_strict_mono k)

lemma pow_right_injective {x : ℕ} (k : 2 ≤ x) : function.injective (λ (n : ℕ), x^n) :=
strict_mono.injective (pow_right_strict_mono k)

lemma pow_left_strict_mono {m : ℕ} (k : 1 ≤ m) : strict_mono (λ (x : ℕ), x^m) :=
λ _ _ h, pow_lt_pow_of_lt_left h k

lemma mul_lt_mul_pow_succ {n a q : ℕ} (a0 : 0 < a) (q1 : 1 < q) :
  n * q < a * q ^ (n + 1) :=
begin
  rw [pow_succ', ← mul_assoc, mul_lt_mul_right (zero_lt_one.trans q1)],
  exact lt_mul_of_one_le_of_lt (nat.succ_le_iff.mpr a0) (nat.lt_pow_self q1 n),
end

end nat

lemma strict_mono.nat_pow {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℕ} (hf : strict_mono f) :
  strict_mono (λ m, (f m) ^ n) :=
(nat.pow_left_strict_mono hn).comp hf

namespace nat

lemma pow_le_iff_le_left {m x y : ℕ} (k : 1 ≤ m) : x^m ≤ y^m ↔ x ≤ y :=
strict_mono.le_iff_le (pow_left_strict_mono k)

lemma pow_lt_iff_lt_left {m x y : ℕ} (k : 1 ≤ m) : x^m < y^m ↔ x < y :=
strict_mono.lt_iff_lt (pow_left_strict_mono k)

lemma pow_left_injective {m : ℕ} (k : 1 ≤ m) : function.injective (λ (x : ℕ), x^m) :=
strict_mono.injective (pow_left_strict_mono k)

theorem sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by { rw [sq, sq], exact nat.mul_self_sub_mul_self_eq a b }

alias sq_sub_sq ← pow_two_sub_pow_two

/-! ### `pow` and `mod` / `dvd` -/

theorem pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n :=
begin
  induction b with b ih,
  refl, simp [pow_succ, nat.mul_mod, ih],
end

theorem mod_pow_succ {b : ℕ} (w m : ℕ) :
  m % (b^succ w) = b * (m/b % b^w) + m % b :=
begin
  by_cases b_h : b = 0,
  { simp [b_h, pow_succ], },
  have b_pos := nat.pos_of_ne_zero b_h,
  apply nat.strong_induction_on m,
  clear m,
  intros p IH,
  cases lt_or_ge p (b^succ w) with h₁ h₁,
  -- base case: p < b^succ w
  { have h₂ : p / b < b^w,
    { rw [div_lt_iff_lt_mul b_pos],
      simpa [pow_succ'] using h₁ },
    rw [mod_eq_of_lt h₁, mod_eq_of_lt h₂],
    simp [div_add_mod] },
  -- step: p ≥ b^succ w
  { -- Generate condition for induction hypothesis
    have h₂ : p - b^succ w < p,
    { exact tsub_lt_self ((pow_pos b_pos _).trans_le h₁) (pow_pos b_pos _) },
    -- Apply induction
    rw [mod_eq_sub_mod h₁, IH _ h₂],
    -- Normalize goal and h1
    simp only [pow_succ],
    simp only [ge, pow_succ] at h₁,
    -- Pull subtraction outside mod and div
    rw [sub_mul_mod _ _ _ h₁, sub_mul_div _ _ _ h₁],
    -- Cancel subtraction inside mod b^w
    have p_b_ge :  b^w ≤ p / b,
    { rw [le_div_iff_mul_le b_pos, mul_comm],
      exact h₁ },
    rw [eq.symm (mod_eq_sub_mod p_b_ge)] }
end

lemma pow_dvd_pow_iff_pow_le_pow {k l : ℕ} : Π {x : ℕ} (w : 0 < x), x^k ∣ x^l ↔ x^k ≤ x^l
| (x+1) w :=
begin
  split,
  { intro a, exact le_of_dvd (pow_pos (succ_pos x) l) a, },
  { intro a, cases x with x,
    { simp only [one_pow], },
    { have le := (pow_le_iff_le_right (nat.le_add_left _ _)).mp a,
      use (x+2)^(l-k),
      rw [←pow_add, add_comm k, tsub_add_cancel_of_le le], } }
end

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
lemma pow_dvd_pow_iff_le_right {x k l : ℕ} (w : 1 < x) : x^k ∣ x^l ↔ k ≤ l :=
by rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), pow_le_iff_le_right w]

lemma pow_dvd_pow_iff_le_right' {b k l : ℕ} : (b+2)^k ∣ (b+2)^l ↔ k ≤ l :=
pow_dvd_pow_iff_le_right (nat.lt_of_sub_eq_succ rfl)

lemma not_pos_pow_dvd : ∀ {p k : ℕ} (hp : 1 < p) (hk : 1 < k), ¬ p^k ∣ p
| (succ p) (succ k) hp hk h :=
  have succ p * (succ p)^k ∣ succ p * 1, by simpa [pow_succ] using h,
  have (succ p) ^ k ∣ 1, from dvd_of_mul_dvd_mul_left (succ_pos _) this,
  have he : (succ p) ^ k = 1, from eq_one_of_dvd_one this,
  have k < (succ p) ^ k, from lt_pow_self hp k,
  have k < 1, by rwa [he] at this,
  have k = 0, from nat.eq_zero_of_le_zero $ le_of_lt_succ this,
  have 1 < 1, by rwa [this] at hk,
  absurd this dec_trivial

lemma pow_dvd_of_le_of_pow_dvd {p m n k : ℕ} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
(pow_dvd_pow _ hmn).trans hdiv

lemma dvd_of_pow_dvd {p k m : ℕ} (hk : 1 ≤ k) (hpk : p^k ∣ m) : p ∣ m :=
by rw ←pow_one p; exact pow_dvd_of_le_of_pow_dvd hk hpk

lemma pow_div {x m n : ℕ} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) :=
by rw [nat.div_eq_iff_eq_mul_left (pow_pos hx n) (pow_dvd_pow _ h), pow_sub_mul_pow _ h]

lemma lt_of_pow_dvd_right {p i n : ℕ} (hn : n ≠ 0) (hp : 2 ≤ p) (h : p ^ i ∣ n) : i < n :=
begin
  rw ←pow_lt_iff_lt_right hp,
  exact lt_of_le_of_lt (le_of_dvd hn.bot_lt h) (lt_pow_self (succ_le_iff.mp hp) n),
end

end nat
