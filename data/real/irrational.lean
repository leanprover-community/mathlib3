/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime

open real rat

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem sqrt_two_irrational : irrational (sqrt 2)
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  simp [num_denom', mk_eq_div] at e,
  have := mul_self_sqrt (le_of_lt two_pos),
  have d0 : (0:ℝ) < d := nat.cast_pos.2 h,
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt $ mul_pos d0 d0),
      ← int.cast_mul, ← int.nat_abs_mul_self] at this,
  revert c this, generalize : n.nat_abs = a, intros,
  have E : 2 * (d * d) = a * a := (@nat.cast_inj ℝ _ _ _ _ _).1 (by simpa),
  have ae : 2 ∣ a,
  { refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rw ← E, apply dvd_mul_right },
  have de : 2 ∣ d,
  { have := mul_dvd_mul ae ae,
    refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rwa [← E, nat.mul_dvd_mul_iff_left (nat.succ_pos 1)] at this },
  exact nat.not_coprime_of_dvd_of_dvd (nat.lt_succ_self _) ae de c
end
