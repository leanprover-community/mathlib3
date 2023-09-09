/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.basic
import ring_theory.ideal.local_ring
import algebra.is_prime_pow
import data.nat.factorization.basic

/-!
# Characteristics of local rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main result

- `char_p_zero_or_prime_power`: In a commutative local ring the characteristics is either
  zero or a prime power.

-/

/-- In a local ring the characteristics is either zero or a prime power. -/
theorem char_p_zero_or_prime_power (R : Type*) [comm_ring R] [local_ring R] (q : ℕ)
  [char_R_q : char_p R q] : q = 0 ∨ is_prime_pow q :=
begin
  /- Assume `q := char(R)` is not zero. -/
  apply or_iff_not_imp_left.2,
  intro q_pos,
  let K := local_ring.residue_field R,
  haveI RM_char := ring_char.char_p K,

  let r := ring_char K,
  let n := (q.factorization) r,
  /- `r := char(R/m)` is either prime or zero: -/
  cases char_p.char_is_prime_or_zero K r with r_prime r_zero,
  { let a := q / (r ^ n),
    /- If `r` is prime, we can write it as `r = a * q^n` ... -/
    have q_eq_a_mul_rn : q = r ^ n * a := by rw nat.mul_div_cancel' (nat.ord_proj_dvd q r),
    have r_ne_dvd_a := nat.not_dvd_ord_compl r_prime q_pos,

    have rn_dvd_q: r ^ n ∣ q := ⟨a, q_eq_a_mul_rn⟩,
    rw mul_comm at q_eq_a_mul_rn,
    have a_dvd_q : a ∣ q := ⟨r ^ n, q_eq_a_mul_rn⟩,
    /- ... where `a` is a unit. -/
    have a_unit : is_unit (a : R) :=
    begin
      by_contradiction g,
      rw ←mem_nonunits_iff at g,
      rw ←local_ring.mem_maximal_ideal at g,
      have a_cast_zero := (ideal.quotient.eq_zero_iff_mem).2 g,
      rw map_nat_cast at a_cast_zero,
      have r_dvd_a := (ring_char.spec K a).1 a_cast_zero,
      exact absurd r_dvd_a r_ne_dvd_a,
    end,
    /- Let `b` be the inverse of `a`. -/
    cases a_unit.exists_left_inv with a_inv h_inv_mul_a,
    have rn_cast_zero : ↑(r ^ n) = (0 : R) :=
    begin
      rw [nat.cast_pow, ←@mul_one R _ (r ^ n), mul_comm,
        ←(classical.some_spec a_unit.exists_left_inv), mul_assoc, ←nat.cast_pow, ←nat.cast_mul,
        ←q_eq_a_mul_rn, char_p.cast_eq_zero R q],
      simp,
    end,
    have q_eq_rn := nat.dvd_antisymm ((char_p.cast_eq_zero_iff R q (r ^ n)).mp rn_cast_zero)
      rn_dvd_q,
    have n_pos : n ≠ 0,
      from λ n_zero, absurd (by simpa [n_zero] using q_eq_rn) (char_p.char_ne_one R q),

    /- Definition of prime power: `∃ r n, prime r ∧ 0 < n ∧ r ^ n = q`. -/
    exact ⟨r, ⟨n, ⟨r_prime.prime, ⟨pos_iff_ne_zero.mpr n_pos, q_eq_rn.symm⟩⟩⟩⟩},
  { haveI K_char_p_0 := ring_char.of_eq r_zero,
    haveI K_char_zero: char_zero K := char_p.char_p_to_char_zero K,
    haveI R_char_zero := ring_hom.char_zero (local_ring.residue R),
    /- Finally, `r = 0` would lead to a contradiction: -/
    have q_zero := char_p.eq R char_R_q (char_p.of_char_zero R),
    exact absurd q_zero q_pos}
end
