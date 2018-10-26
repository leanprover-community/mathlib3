/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime

open rat real

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

theorem irr_of_rat_add_irr (q : ℚ) (x : ℝ) :
  irrational x → irrational (q + x) :=
λ hx_irr hq_rat, hx_irr (exists.elim hq_rat (λ a h, exists.intro (-q + a)
begin by
  rw [← zero_add x, ← neg_add_self ↑q, add_assoc, h, cast_add, cast_neg],
end
))

theorem irr_of_add_irr_iff (q : ℚ) (x : ℝ) : irrational x ↔ irrational(x+↑q) := begin
split, 
    intro Hix, rintro ⟨p, e⟩,
    rw [←add_comm, eq_comm, ←neg_add_eq_iff_eq_add, ←cast_neg, ←cast_add] at e,
    unfold irrational at Hix, apply Hix, existsi (-q+p), exact e.symm,
intro Hix, unfold irrational at Hix, rintro ⟨p, e⟩, apply Hix,
rw [←add_right_inj ↑q, ←cast_add] at e, existsi (p+q), assumption,
end

theorem irr_of_irr_mul_rat (q : ℚ) (x : ℝ) : q ≠ 0 → irrational x → irrational (x * ↑q) :=
begin
    intro Hqn0, intro Hix, intro Hqxrat, cases Hqxrat with r Hr,
    rw [←div_eq_iff_mul_eq, rat.num_denom r, rat.num_denom q, rat.cast_mk, rat.cast_mk, div_div_div_div_eq] at Hr,
    rw [←int.cast_mul, ←int.cast_mul, ←rat.cast_mk_of_ne_zero] at Hr,
    unfold irrational at Hix, apply Hix, existsi (rat.mk (r.num * ↑(q.denom)) (↑(r.denom) * q.num)),
    exact Hr.symm,
    intro Hxd0, rw [int.cast_eq_zero, mul_eq_zero] at Hxd0, cases Hxd0,
    rw int.coe_nat_eq_zero at Hxd0,
    revert Hxd0,
    apply rat.denom_ne_zero,
    revert Hxd0, apply rat.num_ne_zero_of_ne_zero, exact Hqn0,
    rw rat.cast_ne_zero, exact Hqn0,
end

theorem irr_of_irr_mul_rat_alt (q : ℚ) (x : ℝ) : q ≠ 0 → irrational x → irrational(x*↑q) := begin
intros Hn0 Hix, rintro ⟨p, e⟩, unfold irrational at Hix,
rw [←div_eq_iff_mul_eq, ←cast_div] at e,
apply Hix, existsi (p / q), exact e.symm,
intro Hq, apply Hn0, rwa cast_eq_zero at Hq,
end

theorem sqrt_irr_is_irr (k : ℝ) : k ≠ 0 → irrational (k*k) → irrational k := begin
intros Hn0 Hix, rintro ⟨p, e⟩, unfold irrational at Hix, apply Hix,
have e_help := mul_self_eq_mul_self_iff k ↑p,
have e_sqr : k * k = ↑p * ↑p,
    rw e_help, left, assumption,
rw ←cast_mul at e_sqr, existsi p*p, assumption,
end