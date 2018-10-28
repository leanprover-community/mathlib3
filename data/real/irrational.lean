/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime data.padics.padic_norm tactic.linarith

open rat real

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem irr_nrt_of_notint_nrt (x : ℝ) (n : ℕ) (m : ℤ)
        (hxr : x ^ n = m) (hv : ¬ (∃ y : ℤ, x = ↑y)) (hnpos : n > 0) (hmpos : m > 0) :
        irrational x
| ⟨q, e⟩ := begin
  rw [e, ←cast_pow] at hxr, cases q,
  have c1 : ((q_denom : ℤ) : ℝ) ≠ 0, rw [int.cast_ne_zero, int.coe_nat_ne_zero], apply ne_of_gt(q_pos),
  have c2 : (((q_denom ^ n) : ℤ) : ℝ) ≠ 0, rw int.cast_ne_zero, apply pow_ne_zero, rw int.coe_nat_ne_zero, apply ne_of_gt(q_pos),
  have c3 : q_denom ≠ 1, intro, rw [rat.num_denom', a, mk_eq_div, int.coe_nat_one, int.cast_one, div_one, cast_coe_int] at e, apply hv, existsi q_num, exact e,
  rw [num_denom', cast_pow, cast_mk, div_pow, ←int.cast_pow, ←int.cast_pow, div_eq_iff_mul_eq, ←int.cast_mul, int.cast_inj] at hxr, swap, exact c2, swap, exact c1,
  have hdivn : (↑q_denom ^ n) ∣ (q_num)^n, apply dvd.intro_left m hxr,
  rw [←int.dvd_nat_abs, ←int.coe_nat_pow, int.coe_nat_dvd, int.nat_abs_pow, nat.pow_dvd_pow_iff hnpos] at hdivn,
  have hdivn' : nat.gcd (int.nat_abs q_num) (q_denom) = q_denom, apply nat.gcd_eq_right hdivn,
  have hint : q_denom = 1, rw ←hdivn', apply nat.coprime.gcd_eq_one q_cop,
  apply c3, exact hint,
end

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
