/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
import algebra.order.field.basic
import algebra.order.ring.char_zero
import data.nat.cast.basic

/-!
# Cast of naturals into fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

 * `nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
 * `nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/

namespace nat

variables {α : Type*}

@[simp] theorem cast_div [field α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
  ((m / n : ℕ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, {rintro rfl, simpa using n_nonzero},
  rw [nat.mul_div_cancel_left _ this.bot_lt, cast_mul, mul_div_cancel_left _ n_nonzero],
end

lemma cast_div_div_div_cancel_right [field α] [char_zero α] {m n d : ℕ} (hn : d ∣ n) (hm : d ∣ m) :
  (↑(m / d) : α) / (↑(n / d) : α) = (m : α) / n :=
begin
  rcases eq_or_ne d 0 with rfl | hd, { simp [zero_dvd_iff.mp hm], },
  replace hd : (d : α) ≠ 0, { norm_cast, assumption, },
  simp [hd, hm, hn, div_div_div_cancel_right _ hd],
end

section linear_ordered_semifield
variables [linear_ordered_semifield α]

/-- Natural division is always less than division in the field. -/
lemma cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n :=
begin
  cases n,
  { rw [cast_zero, div_zero, nat.div_zero, cast_zero] },
  rwa [le_div_iff, ←nat.cast_mul],
  exact nat.cast_le.2 (nat.div_mul_le_self m n.succ),
  { exact nat.cast_pos.2 n.succ_pos }
end

lemma inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
inv_pos.2 $ add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

lemma one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) :=
by { rw one_div, exact inv_pos_of_nat }

lemma one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) :=
by { refine one_div_le_one_div_of_le _ _, exact nat.cast_add_one_pos _, simpa }

lemma one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) :=
by { refine one_div_lt_one_div_of_lt _ _, exact nat.cast_add_one_pos _, simpa }

end linear_ordered_semifield
end nat
