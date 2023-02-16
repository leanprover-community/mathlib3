/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.set.function
import data.int.order.lemmas
import data.int.bitwise
import data.nat.cast.basic
import data.nat.order.lemmas

/-!
# Miscellaneous lemmas about the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about integers, which require further imports than
`data.int.basic` or `data.int.order`.

-/

open nat

namespace int

lemma le_coe_nat_sub (m n : ℕ) :
  (m - n : ℤ) ≤ ↑(m - n : ℕ) :=
begin
  by_cases h: m ≥ n,
  { exact le_of_eq (int.coe_nat_sub h).symm },
  { simp [le_of_not_ge h, coe_nat_le] }
end

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

/-! ### to_nat -/

lemma to_nat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.to_nat = 0
| 0           _ := rfl
| (n + 1 : ℕ) h := (h.not_lt (by simp)).elim
| -[1+ n]     _ := rfl


/-! ### bitwise ops

This lemma is orphaned from `data.int.bitwise` as it also requires material from `data.int.order`.
-/

local attribute [simp] int.zero_div

@[simp] lemma div2_bit (b n) : div2 (bit b n) = n :=
begin
  rw [bit_val, div2_val, add_comm, int.add_mul_div_left, (_ : (_/2:ℤ) = 0), zero_add],
  cases b,
  { simp },
  { show of_nat _ = _, rw nat.div_eq_zero; simp },
  { cc }
end

end int
