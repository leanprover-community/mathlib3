/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime data.padics.padic_norm tactic.linarith

open rat real

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem irr_nrt_of_n_not_dvd_padic_val {x : ℝ} (n : ℕ) (m : ℤ) (p : ℕ)
        [hp : nat.prime p] (hxr : x ^ n = m) (hv : padic_val p m % n ≠ 0) :
        irrational x
| ⟨q, e⟩ := begin
  rcases nat.eq_zero_or_pos n with rfl | hnpos,
  { rw [eq_comm, pow_zero, ← int.cast_one, int.cast_inj] at hxr,
    rw [hxr, padic_val.one hp.gt_one, nat.zero_mod] at hv,
    exact hv rfl },
  rcases decidable.em (m = 0) with rfl | hm,
  { rw [padic_val.zero, nat.zero_mod] at hv,
    exact hv rfl },
  rw [e, ←cast_coe_int, ←cast_pow, cast_inj] at hxr,
  have : padic_val_rat p (q ^ n) % n = padic_val_rat p m % n, { rw hxr },
  have hqnz : q ≠ 0,
  { rintro rfl, apply hm,
    rwa [zero_pow (hnpos), eq_comm, int.cast_eq_zero] at hxr },
  rw [padic_val_rat.padic_val_rat_of_int hp.gt_one, ← int.coe_nat_mod, padic_val_rat.pow p hqnz,
      int.mul_mod_right, eq_comm, int.coe_nat_eq_zero] at this,
  exact hv this,
end

theorem irr_sqrt_of_padic_val_odd (m : ℤ) (hm : m ≥ 0)
  (p : ℕ) [hp : nat.prime p] (Hpv : padic_val p m % 2 = 1) :
  irrational (sqrt m) :=
irr_nrt_of_n_not_dvd_padic_val 2 m p
  (sqr_sqrt (int.cast_nonneg.2 hm))
  (by rw Hpv; exact one_ne_zero)

theorem irr_sqrt_of_prime (p : ℕ) (hp : nat.prime p) : irrational (sqrt p) :=
irr_sqrt_of_padic_val_odd p (int.coe_nat_nonneg p) p $
by rw padic_val.padic_val_self hp.gt_one; refl

theorem irr_sqrt_two : irrational (sqrt 2) := irr_sqrt_of_prime 2 nat.prime_two

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