/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import algebra.group_with_zero.power
import tactic.linarith

/-!
# Integer power operation on fields and division rings

This file collects basic facts about the operation of raising an element of a `division_ring` to an
integer power. More specialised results are provided in the case of a linearly ordered field.
-/

universe u

@[simp] lemma ring_hom.map_fpow {K L : Type*} [division_ring K] [division_ring L] (f : K →+* L) :
  ∀ (a : K) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_monoid_with_zero_hom.map_fpow

@[simp] lemma fpow_bit0_neg {K : Type*} [division_ring K] (x : K) (n : ℤ) :
  (-x) ^ (bit0 n) = x ^ bit0 n :=
by rw [fpow_bit0', fpow_bit0', neg_mul_neg]

lemma fpow_even_neg {K : Type*} [division_ring K] (a : K) {n : ℤ} (h : even n) :
  (-a) ^ n = a ^ n :=
begin
  obtain ⟨k, rfl⟩ := h,
  rw [←bit0_eq_two_mul, fpow_bit0_neg],
end

@[simp] lemma fpow_bit1_neg {K : Type*} [division_ring K] (x : K) (n : ℤ) :
  (-x) ^ (bit1 n) = - x ^ bit1 n :=
by rw [fpow_bit1', fpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

section ordered_field_power
open int

variables {K : Type u} [linear_ordered_field K] {a : K} {n : ℤ}

lemma fpow_eq_zero_iff (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨fpow_eq_zero, _⟩,
  rintros rfl,
  exact zero_fpow _ hn.ne'
end

lemma fpow_nonneg {a : K} (ha : 0 ≤ a) : ∀ (z : ℤ), 0 ≤ a ^ z
| (n : ℕ) := by { rw gpow_coe_nat, exact pow_nonneg ha _ }
| -[1+n]  := by { rw gpow_neg_succ_of_nat, exact inv_nonneg.2 (pow_nonneg ha _) }

lemma fpow_pos_of_pos {a : K} (ha : 0 < a) : ∀ (z : ℤ), 0 < a ^ z
| (n : ℕ) := by { rw gpow_coe_nat, exact pow_pos ha _ }
| -[1+n]  := by { rw gpow_neg_succ_of_nat, exact inv_pos.2 (pow_pos ha _) }

lemma fpow_le_of_le {x : K} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp only [of_nat_eq_coe, gpow_coe_nat],
    apply pow_le_pow hx,
    apply le_of_coe_nat_le_coe_nat h },
  { apply absurd h,
    apply not_le_of_gt,
    exact lt_of_lt_of_le (neg_succ_lt_zero _) (of_nat_nonneg _) },
  { simp only [gpow_neg_succ_of_nat, one_div, of_nat_eq_coe, gpow_coe_nat],
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le hx },
  { simp only [gpow_neg_succ_of_nat],
    apply (inv_le_inv _ _).2,
    { apply pow_le_pow hx,
      have : -(↑(a+1) : ℤ) ≤ -(↑(b+1) : ℤ), from h,
      have h' := le_of_neg_le_neg this,
      apply le_of_coe_nat_le_coe_nat h' },
    repeat { apply pow_pos (lt_of_lt_of_le zero_lt_one hx) } }
end

lemma pow_le_max_of_min_le {x : K} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
      x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
begin
  wlog hle : a ≤ b,
  have hnle : -b ≤ -a, from neg_le_neg hle,
  have hfle : x ^ (-b) ≤ x ^ (-a), from fpow_le_of_le hx hnle,
  have : x ^ (-c) ≤ x ^ (-a),
  { apply fpow_le_of_le hx,
    simpa only [min_eq_left hle, neg_le_neg_iff] using h },
  simpa only [max_eq_left hfle]
end

lemma fpow_le_one_of_nonpos {p : K} (hp : 1 ≤ p) {z : ℤ} (hz : z ≤ 0) : p ^ z ≤ 1 :=
calc p ^ z ≤ p ^ 0 : fpow_le_of_le hp hz
          ... = 1        : by simp

lemma one_le_fpow_of_nonneg {p : K} (hp : 1 ≤ p) {z : ℤ} (hz : 0 ≤ z) : 1 ≤ p ^ z :=
calc p ^ z ≥ p ^ 0 : fpow_le_of_le hp hz
          ... = 1        : by simp

theorem fpow_bit0_nonneg (a : K) (n : ℤ) : 0 ≤ a ^ bit0 n :=
by { rw fpow_bit0, exact mul_self_nonneg _ }

theorem fpow_two_nonneg (a : K) : 0 ≤ a ^ 2 :=
pow_bit0_nonneg a 1

theorem fpow_bit0_pos {a : K} (h : a ≠ 0) (n : ℤ) : 0 < a ^ bit0 n :=
(fpow_bit0_nonneg a n).lt_of_ne (fpow_ne_zero _ h).symm

theorem fpow_two_pos_of_ne_zero (a : K) (h : a ≠ 0) : 0 < a ^ 2 :=
pow_bit0_pos h 1

@[simp] theorem fpow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ fpow_nonneg h' _,
 λ h, by rw [bit1, fpow_add_one h.ne]; exact mul_neg_of_pos_of_neg (fpow_bit0_pos h.ne _) h⟩

@[simp] theorem fpow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 fpow_bit1_neg_iff

@[simp] theorem fpow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
begin
  rw [le_iff_lt_or_eq, fpow_bit1_neg_iff],
  split,
  { rintro (h | h),
    { exact h.le },
    { exact (fpow_eq_zero h).le } },
  { intro h,
    rcases eq_or_lt_of_le h with rfl|h,
    { exact or.inr (zero_fpow _ (bit1_ne_zero n)) },
    { exact or.inl h } }
end

@[simp] theorem fpow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le fpow_bit1_nonpos_iff

lemma fpow_even_nonneg (a : K) {n : ℤ} (hn : even n) :
  0 ≤ a ^ n :=
begin
  cases le_or_lt 0 a with h h,
  { exact fpow_nonneg h _ },
  { rw [←fpow_even_neg _ hn],
    replace h : 0 ≤ -a := neg_nonneg_of_nonpos (le_of_lt h),
    exact fpow_nonneg h _ }
end

theorem fpow_even_pos (ha : a ≠ 0) (hn : even n) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using fpow_bit0_pos ha k

theorem fpow_odd_nonneg (ha : 0 ≤ a) (hn : odd n) : 0 ≤ a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using fpow_bit1_nonneg_iff.mpr ha

theorem fpow_odd_pos (ha : 0 < a) (hn : odd n) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using fpow_bit1_pos_iff.mpr ha

theorem fpow_odd_nonpos (ha : a ≤ 0) (hn : odd n) : a ^ n ≤ 0:=
by cases hn with k hk; simpa only [hk, two_mul] using fpow_bit1_nonpos_iff.mpr ha

theorem fpow_odd_neg (ha : a < 0) (hn : odd n) : a ^ n < 0:=
by cases hn with k hk; simpa only [hk, two_mul] using fpow_bit1_neg_iff.mpr ha

lemma fpow_even_abs (a : K) {p : ℤ} (hp : even p) :
  abs a ^ p = a ^ p :=
begin
  cases abs_choice a with h h;
  simp only [h, fpow_even_neg _ hp],
end

@[simp] lemma fpow_bit0_abs (a : K) (p : ℤ) :
  (abs a) ^ bit0 p = a ^ bit0 p :=
fpow_even_abs _ (even_bit0 _)

lemma abs_fpow_even (a : K) {p : ℤ} (hp : even p) :
  abs (a ^ p) = a ^ p :=
begin
  rw [abs_eq_self],
  exact fpow_even_nonneg _ hp
end

@[simp] lemma abs_fpow_bit0 (a : K) (p : ℤ) :
  abs (a ^ bit0 p) = a ^ bit0 p :=
abs_fpow_even _ (even_bit0 _)

end ordered_field_power

lemma one_lt_pow {K} [linear_ordered_semiring K] {p : K} (hp : 1 < p) : ∀ {n : ℕ}, 1 ≤ n → 1 < p ^ n
| 1 h := by simp; assumption
| (k+2) h :=
  begin
    rw [←one_mul (1 : K), pow_succ],
    apply mul_lt_mul,
    { assumption },
    { apply le_of_lt, simpa using one_lt_pow (nat.le_add_left 1 k)},
    { apply zero_lt_one },
    { apply le_of_lt (lt_trans zero_lt_one hp) }
  end

lemma one_lt_fpow {K}  [linear_ordered_field K] {p : K} (hp : 1 < p) :
  ∀ z : ℤ, 0 < z → 1 < p ^ z
| (n : ℕ) h := by { rw [gpow_coe_nat],
    exact one_lt_pow hp (nat.succ_le_of_lt (int.lt_of_coe_nat_lt_coe_nat h)) }
| -[1+ n] h := ((int.neg_succ_not_pos _).mp h).elim

section ordered
variables  {K : Type*} [linear_ordered_field K]

lemma nat.fpow_pos_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : 0 < (p:K)^n :=
by { apply fpow_pos_of_pos, exact_mod_cast h }

lemma nat.fpow_ne_zero_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : (p:K)^n ≠ 0 :=
ne_of_gt (nat.fpow_pos_of_pos h n)

lemma fpow_strict_mono {x : K} (hx : 1 < x) :
  strict_mono (λ n:ℤ, x ^ n) :=
λ m n h, show x ^ m < x ^ n,
begin
  have xpos : 0 < x := zero_lt_one.trans hx,
  have h₀ : x ≠ 0 := xpos.ne',
  have hxm : 0 < x^m := fpow_pos_of_pos xpos m,
  have h : 1 < x ^ (n - m) := one_lt_fpow hx _ (sub_pos_of_lt h),
  replace h := mul_lt_mul_of_pos_right h hxm,
  rwa [sub_eq_add_neg, fpow_add h₀, mul_assoc, fpow_neg_mul_fpow_self _ h₀, one_mul, mul_one] at h,
end

@[simp] lemma fpow_lt_iff_lt {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m < x ^ n ↔ m < n :=
(fpow_strict_mono hx).lt_iff_lt

@[simp] lemma fpow_le_iff_le {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m ≤ x ^ n ↔ m ≤ n :=
(fpow_strict_mono hx).le_iff_le

@[simp] lemma pos_div_pow_pos {a b : K} (ha : 0 < a) (hb : 0 < b) (k : ℕ) : 0 < a/b^k :=
div_pos ha (pow_pos hb k)

@[simp] lemma div_pow_le {a b : K} (ha : 0 < a) (hb : 1 ≤ b) (k : ℕ) : a/b^k ≤ a :=
(div_le_iff $ pow_pos (lt_of_lt_of_le zero_lt_one hb) k).mpr
(calc a = a * 1 : (mul_one a).symm
   ...  ≤ a*b^k : (mul_le_mul_left ha).mpr $ one_le_pow_of_one_le hb _)

lemma fpow_injective {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) :
  function.injective ((^) x : ℤ → K) :=
begin
  intros m n h,
  rcases h₁.lt_or_lt with H|H,
  { apply (fpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← fpow_neg_one, ← fpow_mul, ← fpow_mul, mul_comm _ m, mul_comm _ n, fpow_mul, fpow_mul,
      h], },
  { exact (fpow_strict_mono H).injective h, },
end

@[simp] lemma fpow_inj {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) {m n : ℤ} :
  x ^ m = x ^ n ↔ m = n :=
(fpow_injective h₀ h₁).eq_iff

end ordered

section
variables {K : Type*} [field K]

@[simp, norm_cast] theorem rat.cast_fpow [char_zero K] (q : ℚ) (n : ℤ) :
  ((q ^ n : ℚ) : K) = q ^ n :=
(rat.cast_hom K).map_fpow q n

end
