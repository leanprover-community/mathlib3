/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime data.padics.padic_norm

open rat real

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem irr_sqrt_of_padic_val_odd (m : ℤ) (Hnpl : m > 0)
  (Hpn : ∃ (p : ℕ) [nat.prime p], (padic_val p m) % 2 = 1) :
  irrational (sqrt m)
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  rcases Hpn with ⟨p, Hp, Hpv⟩, resetI,
  simp [num_denom', mk_eq_div] at e,
  have Hnpl' : 0 < (m : ℝ) := int.cast_pos.2 Hnpl,
  have Hd0 : (0:ℝ) < d := nat.cast_pos.2 h,
  have := mul_self_sqrt (le_of_lt Hnpl'),
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt (mul_pos Hd0 Hd0))] at this,
  have : m * (d * d) = n * n := (@int.cast_inj ℝ _ _ _ _ _).1 (by simpa),
  have d0' : (d:ℤ) ≠ 0, rw int.coe_nat_ne_zero, apply ne_of_gt h,
  have n0 : n ≠ 0, intro y0, rw [y0, int.cast_zero, zero_div, sqrt_eq_zero'] at e, revert e, apply not_le_of_gt Hnpl',
  have HPV : padic_val p (m * (d * d)) = padic_val p (n * n), rw this,
  rw [←padic_val.mul p (ne_of_gt Hnpl) (mul_ne_zero d0' d0'), ←padic_val.mul p d0' d0',
      ←padic_val.mul p n0 n0, ←mul_two, ←mul_two] at HPV,
  have HPV' : (padic_val p m + padic_val p d * 2) % 2 = (padic_val p n * 2) % 2, rw HPV,
  rw [nat.mul_mod_left, nat.add_mul_mod_self_right, Hpv] at HPV',
  cases HPV'
end

theorem irr_sqrt_two : irrational (sqrt 2) :=
irr_sqrt_of_padic_val_odd 2 dec_trivial ⟨2, dec_trivial, rfl⟩

variables {q : ℚ} {x : ℝ}

theorem irr_rat_add_of_irr : irrational x → irrational (q + x) :=
mt $ λ ⟨a, h⟩, ⟨-q + a, by rw [rat.cast_add, ← h, rat.cast_neg, neg_add_cancel_left]⟩

@[simp] theorem irr_rat_add_iff_irr : irrational (q + x) ↔ irrational x :=
⟨by simpa only [cast_neg, neg_add_cancel_left] using @irr_rat_add_of_irr (-q) (q+x),
irr_rat_add_of_irr⟩

@[simp] theorem irr_add_rat_iff_irr : irrational (x + q) ↔ irrational x :=
by rw [add_comm, irr_rat_add_iff_irr]

theorem irr_mul_rat_iff_irr (Hqn0 : q ≠ 0) : irrational (x * ↑q) ↔ irrational x :=
⟨mt $ λ ⟨r, hr⟩, ⟨r * q, hr.symm ▸ (rat.cast_mul _ _).symm⟩,
mt $ λ ⟨r, hr⟩, ⟨r / q, by rw [cast_div, ← hr, mul_div_cancel]; rwa cast_ne_zero⟩⟩

theorem irr_of_irr_mul_self : irrational (x * x) → irrational x :=
mt $ λ ⟨p, e⟩, ⟨p * p, by rw [e, cast_mul]⟩