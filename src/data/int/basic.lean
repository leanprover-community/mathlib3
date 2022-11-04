/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.nat.pow
import data.nat.cast
import data.int.defs.order
import algebra.ring.regular

/-!
# Basic operations on the integers

This file contains lemmas about integers, which required further imports than
`data/int/defs/basic.lean` or `data/int/defs/order.lean`.

## Recursors
* `int.bit_cases_on`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.

-/

open nat

namespace int

@[simp] theorem coe_nat_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n := nat.cast_pos

lemma le_coe_nat_sub (m n : ℕ) :
  (m - n : ℤ) ≤ ↑(m - n : ℕ) :=
begin
  by_cases h: m ≥ n,
  { exact le_of_eq (int.coe_nat_sub h).symm },
  { simp [le_of_not_ge h, coe_nat_le] }
end

lemma coe_nat_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) := int.coe_nat_pos.2 (succ_pos n)

/-! ### succ and pred -/

@[simp] lemma succ_coe_nat_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
lt_add_one_iff.mpr (by simp)

/-! ### nat abs -/

variables {a b : ℤ} {n : ℕ}

lemma nat_abs_eq_iff_sq_eq {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a ^ 2 = b ^ 2 :=
by { rw [sq, sq], exact nat_abs_eq_iff_mul_self_eq }

lemma nat_abs_lt_iff_sq_lt {a b : ℤ} : a.nat_abs < b.nat_abs ↔ a ^ 2 < b ^ 2 :=
by { rw [sq, sq], exact nat_abs_lt_iff_mul_self_lt }

lemma nat_abs_le_iff_sq_le {a b : ℤ} : a.nat_abs ≤ b.nat_abs ↔ a ^ 2 ≤ b ^ 2 :=
by { rw [sq, sq], exact nat_abs_le_iff_mul_self_le }

lemma nat_abs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  nat_abs a = nat_abs b ↔ a = b :=
by rw [←sq_eq_sq ha hb, ←nat_abs_eq_iff_sq_eq]

lemma nat_abs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
  nat_abs a = nat_abs b ↔ a = b :=
by simpa only [int.nat_abs_neg, neg_inj]
 using nat_abs_inj_of_nonneg_of_nonneg
  (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

lemma nat_abs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
  nat_abs a = nat_abs b ↔ a = -b :=
by simpa only [int.nat_abs_neg]
  using nat_abs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

lemma nat_abs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
  nat_abs a = nat_abs b ↔ -a = b :=
by simpa only [int.nat_abs_neg]
  using nat_abs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

section intervals
open set

lemma strict_mono_on_nat_abs : strict_mono_on nat_abs (Ici 0) :=
λ a ha b hb hab, nat_abs_lt_nat_abs_of_nonneg_of_lt ha hab

lemma strict_anti_on_nat_abs : strict_anti_on nat_abs (Iic 0) :=
λ a ha b hb hab, by simpa [int.nat_abs_neg]
  using nat_abs_lt_nat_abs_of_nonneg_of_lt (right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

lemma inj_on_nat_abs_Ici : inj_on nat_abs (Ici 0) := strict_mono_on_nat_abs.inj_on

lemma inj_on_nat_abs_Iic : inj_on nat_abs (Iic 0) := strict_anti_on_nat_abs.inj_on

end intervals

/-! ### dvd -/

@[norm_cast] theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
⟨λ ⟨a, ae⟩, m.eq_zero_or_pos.elim
  (λm0, by simp [m0] at ae; simp [ae, m0])
  (λm0l, by
  { cases eq_coe_of_zero_le (@nonneg_of_mul_nonneg_right ℤ _ m a
      (by simp [ae.symm]) (by simpa using m0l)) with k e,
    subst a, exact ⟨k, int.coe_nat_inj ae⟩ }),
 λ ⟨k, e⟩, dvd.intro k $ by rw [e, int.coe_nat_mul]⟩

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.nat_abs :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [coe_nat_dvd]

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.nat_abs ∣ n :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [coe_nat_dvd]

@[simp]
theorem sign_pow_bit1 (k : ℕ) : ∀ n : ℤ, n.sign ^ (bit1 k) = n.sign
| (n+1:ℕ) := one_pow (bit1 k)
| 0       := zero_pow (nat.zero_lt_bit1 k)
| -[1+ n] := (neg_pow_bit1 1 k).trans (congr_arg (λ x, -x) (one_pow (bit1 k)))

theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
match a, b, eq_succ_of_zero_lt bpos, H with
| (m : ℕ), ._, ⟨n, rfl⟩, H := coe_nat_le_coe_nat_of_le $
  nat.le_of_dvd n.succ_pos $ coe_nat_dvd.1 H
| -[1+ m], ._, ⟨n, rfl⟩, _ :=
  le_trans (le_of_lt $ neg_succ_lt_zero _) (coe_zero_le _)
end

theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
match a, eq_coe_of_zero_le H, H' with
| ._, ⟨n, rfl⟩, H' := congr_arg coe $
  nat.eq_one_of_dvd_one $ coe_nat_dvd.1 H'
end

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])

lemma of_nat_dvd_of_dvd_nat_abs {a : ℕ} : ∀ {z : ℤ} (haz : a ∣ z.nat_abs), ↑a ∣ z
| (int.of_nat _) haz := int.coe_nat_dvd.2 haz
| -[1+k] haz :=
  begin
    change ↑a ∣ -(k+1 : ℤ),
    apply dvd_neg_of_dvd,
    apply int.coe_nat_dvd.2,
    exact haz
  end

lemma dvd_nat_abs_of_of_nat_dvd {a : ℕ} : ∀ {z : ℤ} (haz : ↑a ∣ z), a ∣ z.nat_abs
| (int.of_nat _) haz := int.coe_nat_dvd.1 (int.dvd_nat_abs.2 haz)
| -[1+k] haz :=
  have haz' : (↑a:ℤ) ∣ (↑(k+1):ℤ), from dvd_of_dvd_neg haz,
  int.coe_nat_dvd.1 haz'

lemma pow_dvd_of_le_of_pow_dvd {p m n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) :
  ↑(p ^ m) ∣ k :=
begin
  induction k,
  { apply int.coe_nat_dvd.2,
    apply pow_dvd_of_le_of_pow_dvd hmn,
    apply int.coe_nat_dvd.1 hdiv },
  change -[1+k] with -(↑(k+1) : ℤ),
  apply dvd_neg_of_dvd,
  apply int.coe_nat_dvd.2,
  apply pow_dvd_of_le_of_pow_dvd hmn,
  apply int.coe_nat_dvd.1,
  apply dvd_of_dvd_neg,
  exact hdiv,
end

lemma dvd_of_pow_dvd {p k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p^k) ∣ m) : ↑p ∣ m :=
by rw ←pow_one p; exact pow_dvd_of_le_of_pow_dvd hk hpk

theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=
begin
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs],
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj'],
  apply nat.dvd_antisymm
end

/-! ### `/` and ordering -/

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c)
    (h : b * a = c * d) :
  a = c / b * d :=
begin
  cases hbc with k hk,
  subst hk,
  rw [int.mul_div_cancel_left _ hb],
  rw mul_assoc at h,
  apply mul_left_cancel₀ hb h
end

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
lemma eq_zero_of_dvd_of_nat_abs_lt_nat_abs {a b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a) :
  b = 0 :=
begin
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at w,
  rw ←nat_abs_eq_zero,
  exact eq_zero_of_dvd_of_lt w h
end

lemma eq_zero_of_dvd_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
eq_zero_of_dvd_of_nat_abs_lt_nat_abs h (nat_abs_lt_nat_abs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
lemma eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs {a b c : ℤ} (h1 : a % b = c)
    (h2 : nat_abs (a - c) < nat_abs b) :
  a = c :=
eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_lt_nat_abs (dvd_sub_of_mod_eq h1) h2)

theorem of_nat_add_neg_succ_of_nat_of_ge {m n : ℕ}
  (h : n.succ ≤ m) : of_nat m + -[1+n] = of_nat (m - n.succ) :=
begin
  change sub_nat_nat _ _ = _,
  have h' : n.succ - m = 0,
  apply tsub_eq_zero_iff_le.mpr h,
  simp [*, sub_nat_nat]
end

lemma nat_abs_le_of_dvd_ne_zero {s t : ℤ} (hst : s ∣ t) (ht : t ≠ 0) : nat_abs s ≤ nat_abs t :=
not_lt.mp (mt (eq_zero_of_dvd_of_nat_abs_lt_nat_abs hst) ht)

/-! ### to_nat -/

lemma to_nat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.to_nat = 0
| 0           _ := rfl
| (n + 1 : ℕ) h := (h.not_lt (by simp)).elim
| -[1+ n]     _ := rfl

/-! ### units -/

lemma is_unit_sq {a : ℤ} (ha : is_unit a) : a ^ 2 = 1 :=
by rw [sq, is_unit_mul_self ha]

@[simp] lemma units_sq (u : ℤˣ) : u ^ 2 = 1 :=
by rw [units.ext_iff, units.coe_pow, units.coe_one, is_unit_sq u.is_unit]

@[simp] lemma units_mul_self (u : ℤˣ) : u * u = 1 :=
by rw [←sq, units_sq]

@[simp] lemma units_inv_eq_self (u : ℤˣ) : u⁻¹ = u :=
by rw [inv_eq_iff_mul_eq_one, units_mul_self]

-- `units.coe_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further
@[simp] lemma units_coe_mul_self (u : ℤˣ) : (u * u : ℤ) = 1 :=
by rw [←units.coe_mul, units_mul_self, units.coe_one]

@[simp] lemma neg_one_pow_ne_zero {n : ℕ} : (-1 : ℤ)^n ≠ 0 :=
pow_ne_zero _ (abs_pos.mp (by simp))

/-! ### bitwise ops -/

local attribute [simp] int.zero_div

@[simp] lemma div2_bit (b n) : div2 (bit b n) = n :=
begin
  rw [bit_val, div2_val, add_comm, int.add_mul_div_left, (_ : (_/2:ℤ) = 0), zero_add],
  cases b,
  { simp },
  { show of_nat _ = _, rw nat.div_eq_zero; simp },
  { cc }
end

lemma shiftl_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftl m (n + k) = shiftl (shiftl m n) k
| (m : ℕ) n (k:ℕ) := congr_arg of_nat (nat.shiftl_add _ _ _)
| -[1+ m] n (k:ℕ) := congr_arg neg_succ_of_nat (nat.shiftl'_add _ _ _ _)
| (m : ℕ) n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl ↑m i = nat.shiftr (nat.shiftl m n) k)
    (λ i n, congr_arg coe $
      by rw [← nat.shiftl_sub, add_tsub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg coe $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl_sub, tsub_self]; refl)
| -[1+ m] n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl -[1+ m] i = -[1+ nat.shiftr (nat.shiftl' tt m n) k])
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [← nat.shiftl'_sub, add_tsub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl'_sub, tsub_self]; refl)

lemma shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (n - k) = shiftr (shiftl m n) k :=
shiftl_add _ _ _

lemma shiftl_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftl m n = m * ↑(2 ^ n)
| (m : ℕ) n := congr_arg coe (nat.shiftl_eq_mul_pow _ _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λi, -i) (nat.shiftl'_tt_eq_mul_pow _ _)

lemma shiftr_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftr m n = m / ↑(2 ^ n)
| (m : ℕ) n := by rw shiftr_coe_nat; exact congr_arg coe (nat.shiftr_eq_div_pow _ _)
| -[1+ m] n := begin
  rw [shiftr_neg_succ, neg_succ_of_nat_div, nat.shiftr_eq_div_pow], refl,
  exact coe_nat_lt_coe_nat_of_lt (pow_pos dec_trivial _)
end

lemma one_shiftl (n : ℕ) : shiftl 1 n = (2 ^ n : ℕ) :=
congr_arg coe (nat.one_shiftl _)

@[simp] lemma zero_shiftl : ∀ n : ℤ, shiftl 0 n = 0
| (n : ℕ) := congr_arg coe (nat.zero_shiftl _)
| -[1+ n] := congr_arg coe (nat.zero_shiftr _)

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 := zero_shiftl _

lemma sq_eq_one_of_sq_lt_four {x : ℤ} (h1 : x ^ 2 < 4) (h2 : x ≠ 0) : x ^ 2 = 1 :=
sq_eq_one_iff.mpr ((abs_eq (zero_le_one' ℤ)).mp (le_antisymm (lt_add_one_iff.mp
  (abs_lt_of_sq_lt_sq h1 zero_le_two)) (sub_one_lt_iff.mp (abs_pos.mpr h2))))

lemma sq_eq_one_of_sq_le_three {x : ℤ} (h1 : x ^ 2 ≤ 3) (h2 : x ≠ 0) : x ^ 2 = 1 :=
sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one 3)) h2

end int
