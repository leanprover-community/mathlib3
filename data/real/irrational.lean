/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime

open rat real

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem irr_sqrt_two : irrational (sqrt 2)
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  simp [num_denom', mk_eq_div] at e,
  have := mul_self_sqrt (le_of_lt two_pos),
  have d0 : (0:ℝ) < d := nat.cast_pos.2 h,
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt $ mul_pos d0 d0),
    ← int.cast_mul, ← int.nat_abs_mul_self] at this,
  generalize_hyp : n.nat_abs = k at c this,
  have E : 2 * (d * d) = k * k := (@nat.cast_inj ℝ _ _ _ _ _).1 (by simpa),
  have ke : 2 ∣ k,
  { refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rw ← E, apply dvd_mul_right },
  have de : 2 ∣ d,
  { have := mul_dvd_mul ke ke,
    refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rwa [← E, nat.mul_dvd_mul_iff_left (nat.succ_pos 1)] at this },
  exact nat.not_coprime_of_dvd_of_dvd (nat.lt_succ_self _) ke de c
end

variables {q : ℚ} {x : ℝ}

theorem irr_rat_add_of_irr (hx_irr : irrational x) : irrational (q + x) :=
λ ⟨a, h⟩, hx_irr ⟨-q + a, by rw [cast_add, ← h, cast_neg, neg_add_cancel_left]⟩

theorem irr_iff_irr_add_rat : irrational x ↔ irrational (x + q) :=
⟨by rw add_comm; exact irr_rat_add_of_irr,
by simpa only [cast_neg, add_comm, add_neg_cancel_right] using @irr_rat_add_of_irr (-q) (x+q)⟩

theorem irr_mul_rat_of_irr (Hqn0 : q ≠ 0) (Hix : irrational x) : irrational (x * ↑q) :=
λ ⟨r, Hr⟩, Hix ⟨r / q, by rw [cast_div, ← Hr, mul_div_cancel]; rwa cast_ne_zero⟩

theorem irr_of_irr_mul_self (k : ℝ) (Hix : irrational (k*k)) : irrational k :=
λ ⟨p, e⟩, Hix ⟨p * p, by rw [e, cast_mul]⟩