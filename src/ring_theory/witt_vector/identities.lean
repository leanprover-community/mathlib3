/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.frobenius
import ring_theory.witt_vector.verschiebung
import ring_theory.witt_vector.mul_p

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace witt_vector

variables {p : ℕ} {R : Type*} [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`
include hp
noncomputable theory

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
lemma frobenius_verschiebung (x : 𝕎 R) :
  frobenius (verschiebung x) = x * p :=
by { ghost_calc x, ghost_simp [mul_comm] }

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `zmod p`. -/
lemma verschiebung_zmod (x : 𝕎 (zmod p)) :
  verschiebung x = x * p :=
by rw [← frobenius_verschiebung, frobenius_zmodp]

lemma coeff_p_pow [char_p R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 :=
begin
  induction i with i h,
  { simp only [one_coeff_zero, ne.def, pow_zero] },
  { rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p,
        verschiebung_coeff_succ, h, one_pow], }
end

lemma coeff_p_pow_eq_zero [char_p R p] {i j : ℕ} (hj : j ≠ i) : (p ^ i : 𝕎 R).coeff j = 0 :=
begin
  induction i with i hi generalizing j,
  { rw [pow_zero, one_coeff_eq_of_pos],
    exact nat.pos_of_ne_zero hj },
  { rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p],
    cases j,
    { rw [verschiebung_coeff_zero, zero_pow],
      exact nat.prime.pos hp.out },
    { rw [verschiebung_coeff_succ, hi, zero_pow],
      { exact nat.prime.pos hp.out },
      { exact ne_of_apply_ne (λ (j : ℕ), j.succ) hj } } }
end

/-- The “projection formula” for Frobenius and Verschiebung. -/
lemma verschiebung_mul_frobenius (x y : 𝕎 R) :
  verschiebung (x * frobenius y) = verschiebung x * y :=
by { ghost_calc x y, rintro ⟨⟩; ghost_simp [mul_assoc] }

lemma mul_char_p_coeff_zero [char_p R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 :=
begin
  rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_zero, zero_pow],
  exact nat.prime.pos hp.out
end

lemma mul_char_p_coeff_succ [char_p R p] (x : 𝕎 R) (i : ℕ) :
  (x * p).coeff (i + 1) = (x.coeff i)^p :=
by rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_succ]


end witt_vector
