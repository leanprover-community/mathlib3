/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Integer power operation on fields.
-/

import algebra.group_power algebra.ordered_field
import tactic.wlog tactic.linarith

universe u

section field_power
open int nat
variables {K : Type u} [division_ring K]

@[simp] lemma zero_gpow : ∀ z : ℕ, z ≠ 0 → (0 : K)^z = 0
| 0 h := absurd rfl h
| (k+1) h := zero_mul _

/-- The integer power of an element of a division ring (e.g., a field). -/
def fpow (a : K) : ℤ → K
| (of_nat n) := a ^ n
| -[1+n] := 1/(a ^ (n+1))

instance : has_pow K ℤ := ⟨fpow⟩

@[simp] lemma fpow_of_nat (a : K) (n : ℕ) : a ^ (n : ℤ) = a ^ n := rfl

lemma fpow_neg_succ_of_nat (a : K) (n : ℕ) : a ^ (-[1+ n]) = 1 / (a ^ (n + 1)) := rfl

lemma unit_pow {a : K} (ha : a ≠ 0) : ∀ n : ℕ, a ^ n = ↑((units.mk0 a ha)^n)
| 0 := units.coe_one.symm
| (k+1) := by simp only [_root_.pow_succ, units.coe_mul, units.mk0_val]; rw unit_pow

lemma fpow_eq_gpow {a : K} (h : a ≠ 0) : ∀ (z : ℤ), a ^ z = ↑(gpow (units.mk0 a h) z)
| (of_nat k) := unit_pow _ _
| -[1+k] := by rw [fpow_neg_succ_of_nat, gpow, one_div_eq_inv, units.inv_eq_inv, unit_pow]

lemma fpow_inv (a : K) : a ^ (-1 : ℤ) = a⁻¹ :=
show 1*(a*1)⁻¹ = a⁻¹, by rw [one_mul, mul_one]

lemma fpow_ne_zero_of_ne_zero {a : K} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (of_nat n) := pow_ne_zero _ ha
| -[1+n] := one_div_ne_zero $ pow_ne_zero _ ha

@[simp] lemma fpow_zero {a : K} : a ^ (0 : ℤ) = 1 :=
pow_zero a

lemma fpow_add {a : K} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 + z2) = a ^ z1 * a ^ z2 :=
begin simp only [fpow_eq_gpow ha], rw ← units.coe_mul, congr, apply gpow_add end

@[simp] lemma one_fpow : ∀(i : ℤ), (1 : K) ^ i = 1
| (int.of_nat n) := _root_.one_pow n
| -[1+n]         := show 1/(1 ^ (n+1) : K) = 1, by simp

@[simp] lemma fpow_one (a : K) : a^(1:ℤ) = a :=
pow_one a

end field_power

@[simp] lemma ring_hom.map_fpow {α β : Type*} [discrete_field α] [discrete_field β] (f : α →+* β)
  (a : α) : ∀ (n : ℤ), f (a ^ n) = f a ^ n
| (n : ℕ) := f.map_pow a n
| -[1+n] := by simp [fpow_neg_succ_of_nat, f.map_pow, f.map_inv]

lemma ring_hom.map_fpow' {K L : Type*} [division_ring K] [division_ring L] (f : K →+* L)
  (a : K) (ha : a ≠ 0) : ∀ (n : ℤ), f (a ^ n) = f a ^ n
| (n : ℕ) := f.map_pow a n
| -[1+ n] :=
begin
  have : a^(n+1) ≠ 0 := mt pow_eq_zero ha,
  simp [fpow_neg_succ_of_nat, f.map_pow, f.map_inv' this],
end

namespace is_ring_hom

lemma map_fpow {α β : Type*} [discrete_field α] [discrete_field β] (f : α → β) [is_ring_hom f]
  (a : α) : ∀ (n : ℤ), f (a ^ n) = f a ^ n :=
(ring_hom.of f).map_fpow a

lemma map_fpow' {K L : Type*} [division_ring K] [division_ring L] (f : K → L) [is_ring_hom f]
  (a : K) (ha : a ≠ 0) : ∀ (n : ℤ), f (a ^ n) = f a ^ n :=
(ring_hom.of f).map_fpow' a ha

end is_ring_hom

section discrete_field_power
open int
variables {K : Type u} [discrete_field K]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → (0 : K) ^ z = 0
| (of_nat n) h := zero_gpow _ $ by rintro rfl; exact h rfl
| -[1+n] h := show 1/(0*0^n)=(0:K), by rw [zero_mul, one_div_zero]

lemma fpow_neg (a : K) : ∀ n : ℤ, a ^ (-n) = 1 / a ^ n
| (0) := by simp
| (of_nat (n+1)) := rfl
| -[1+n] := show fpow a (n+1) = 1 / (1 / fpow a (n+1)), by rw one_div_one_div

lemma fpow_sub {a : K} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg, ←div_eq_mul_one_div]

lemma fpow_mul (a : K) (i j : ℤ) : a ^ (i * j) = (a ^ i) ^ j :=
begin
  by_cases a = 0,
  { subst h,
    have : ¬ i = 0 → ¬ j = 0 → ¬ i * j = 0, begin rw [mul_eq_zero, not_or_distrib], exact and.intro end,
    by_cases hi : i = 0; by_cases hj : j = 0;
      simp [hi, hj, zero_fpow i, zero_fpow j, zero_fpow _ (this _ _), one_fpow] },
  rw [fpow_eq_gpow h, fpow_eq_gpow h, fpow_eq_gpow (units.ne_zero _), units.mk0_coe],
  fapply congr_arg coe _, -- TODO: uh oh
  exact gpow_mul (units.mk0 a h) i j
end

lemma mul_fpow (a b : K) : ∀(i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (int.of_nat n) := _root_.mul_pow a b n
| -[1+n] :=
  by rw [fpow_neg_succ_of_nat, fpow_neg_succ_of_nat, fpow_neg_succ_of_nat,
      mul_pow, div_mul_div, one_mul]

end discrete_field_power

section ordered_field_power
open int

variables {K : Type u} [discrete_linear_ordered_field K]

lemma fpow_nonneg_of_nonneg {a : K} (ha : 0 ≤ a) : ∀ (z : ℤ), 0 ≤ a ^ z
| (of_nat n) := pow_nonneg ha _
| -[1+n] := div_nonneg' zero_le_one $ pow_nonneg ha _

lemma fpow_pos_of_pos {a : K} (ha : 0 < a) : ∀ (z : ℤ), 0 < a ^ z
| (of_nat n) := pow_pos ha _
| -[1+n] := div_pos zero_lt_one $ pow_pos ha _

lemma fpow_le_of_le {x : K} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp only [fpow_of_nat, of_nat_eq_coe],
    apply pow_le_pow hx,
    apply le_of_coe_nat_le_coe_nat h },
  { apply absurd h,
    apply not_le_of_gt,
    exact lt_of_lt_of_le (neg_succ_lt_zero _) (of_nat_nonneg _) },
  { simp only [fpow_neg_succ_of_nat, one_div_eq_inv],
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le hx },
  { simp only [fpow_neg_succ_of_nat],
    apply (one_div_le_one_div _ _).2,
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
    simpa [*, fpow_add, mul_assoc, fpow_neg, inv_mul_cancel], },
  apply one_lt_fpow hx, linarith,
end

@[simp] lemma fpow_lt_iff_lt {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m < x ^ n ↔ m < n :=
(fpow_strict_mono hx).lt_iff_lt

@[simp] lemma fpow_le_iff_le {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m ≤ x ^ n ↔ m ≤ n :=
(fpow_strict_mono hx).le_iff_le

lemma injective_fpow {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) :
  function.injective ((^) x : ℤ → K) :=
begin
  intros m n h,
  rcases lt_trichotomy x 1 with H|rfl|H,
  { apply (fpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← fpow_inv, ← fpow_mul, ← fpow_mul, mul_comm _ m, mul_comm _ n, fpow_mul, fpow_mul, h], },
  { contradiction },
  { exact (fpow_strict_mono H).injective h, },
end

@[simp] lemma fpow_inj {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) {m n : ℤ} :
  x ^ m = x ^ n ↔ m = n :=
⟨λ h, injective_fpow h₀ h₁ h, congr_arg _⟩

end ordered

section
variables {K : Type*} [discrete_field K]

@[simp] theorem fpow_neg_mul_fpow_self (n : ℕ) {x : K} (h : x ≠ 0) :
  x^-(n:ℤ) * x^n = 1 :=
begin
  convert inv_mul_cancel (pow_ne_zero n h),
  rw [fpow_neg, one_div_eq_inv, fpow_of_nat]
end

@[simp, move_cast] theorem cast_fpow [char_zero K] (q : ℚ) (n : ℤ) :
  ((q ^ n : ℚ) : K) = q ^ n :=
(ring_hom.of rat.cast).map_fpow q n

lemma fpow_eq_zero {x : K} {n : ℤ} (h : x^n = 0) : x = 0 :=
classical.by_contradiction $ λ hx, fpow_ne_zero_of_ne_zero hx n h

end
