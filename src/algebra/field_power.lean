/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Integer power operation on fields.
-/
import algebra.group_with_zero_power
import tactic.linarith

universe u

@[simp] lemma ring_hom.map_fpow {K L : Type*} [division_ring K] [division_ring L] (f : K →+* L) :
  ∀ (a : K) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_monoid_hom.map_fpow f.map_zero

section ordered_field_power
open int

variables {K : Type u} [discrete_linear_ordered_field K]

lemma fpow_nonneg_of_nonneg {a : K} (ha : 0 ≤ a) : ∀ (z : ℤ), 0 ≤ a ^ z
| (of_nat n) := pow_nonneg ha _
| -[1+n]     := inv_nonneg.2 $ pow_nonneg ha _

lemma fpow_pos_of_pos {a : K} (ha : 0 < a) : ∀ (z : ℤ), 0 < a ^ z
| (of_nat n) := pow_pos ha _
| -[1+n]     := inv_pos.2 $ pow_pos ha _

lemma fpow_le_of_le {x : K} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp only [fpow_of_nat, of_nat_eq_coe],
    apply pow_le_pow hx,
    apply le_of_coe_nat_le_coe_nat h },
  { apply absurd h,
    apply not_le_of_gt,
    exact lt_of_lt_of_le (neg_succ_lt_zero _) (of_nat_nonneg _) },
  { simp only [fpow_neg_succ_of_nat, one_div],
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le hx },
  { simp only [fpow_neg_succ_of_nat],
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

end ordered_field_power

lemma one_lt_pow {K} [linear_ordered_semiring K] {p : K} (hp : 1 < p) : ∀ {n : ℕ}, 1 ≤ n → 1 < p ^ n
| 1 h := by simp; assumption
| (k+2) h :=
  begin
    rw ←one_mul (1 : K),
    apply mul_lt_mul,
    { assumption },
    { apply le_of_lt, simpa using one_lt_pow (nat.le_add_left 1 k)},
    { apply zero_lt_one },
    { apply le_of_lt (lt_trans zero_lt_one hp) }
  end

lemma one_lt_fpow {K}  [discrete_linear_ordered_field K] {p : K} (hp : 1 < p) :
  ∀ z : ℤ, 0 < z → 1 < p ^ z
| (int.of_nat n) h := one_lt_pow hp (nat.succ_le_of_lt (int.lt_of_coe_nat_lt_coe_nat h))

section ordered
variables  {K : Type*} [discrete_linear_ordered_field K]

lemma nat.fpow_pos_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : 0 < (p:K)^n :=
by { apply fpow_pos_of_pos, exact_mod_cast h }

lemma nat.fpow_ne_zero_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : (p:K)^n ≠ 0 :=
ne_of_gt (nat.fpow_pos_of_pos h n)

lemma fpow_strict_mono {x : K} (hx : 1 < x) :
  strict_mono (λ n:ℤ, x ^ n) :=
λ m n h, show x ^ m < x ^ n,
begin
  have xpos : 0 < x := by linarith,
  have h₀ : x ≠ 0 := by linarith,
  have hxm : 0 < x^m := fpow_pos_of_pos xpos m,
  have hxm₀ : x^m ≠ 0 := ne_of_gt hxm,
  suffices : 1 < x^(n-m),
  { replace := mul_lt_mul_of_pos_right this hxm,
    simp [sub_eq_add_neg] at this,
    simpa [*, fpow_add, mul_assoc, fpow_neg, inv_mul_cancel], },
  apply one_lt_fpow hx, linarith,
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
  rcases lt_trichotomy x 1 with H|rfl|H,
  { apply (fpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← fpow_neg_one, ← fpow_mul, ← fpow_mul, mul_comm _ m, mul_comm _ n, fpow_mul, fpow_mul,
      h], },
  { contradiction },
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
