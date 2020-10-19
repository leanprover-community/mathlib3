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

In this file we show deduce common identities between the Frobenius and Verschiebung operators.

### Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “product formula”: `V(x * F y) = V x * y`
-/

namespace witt_vector

variables {p : ℕ} {R : Type*} [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector

open mv_polynomial
noncomputable theory

include hp

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
lemma frobenius_verschiebung (x : 𝕎 R) :
  frobenius (verschiebung x) = x * p :=
by { ghost_calc x, ghost_simp [mul_comm] }

lemma verschiebung_zmod (x : 𝕎 (zmod p)) :
  verschiebung x = x * p :=
begin
  rw [← frobenius_verschiebung, frobenius_zmodp],
end

lemma coeff_p_pow [char_p R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 :=
begin
  induction i with i h,
  { simp only [one_coeff_zero, ne.def, pow_zero] },
  { rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p,
        verschiebung_coeff_succ, h, one_pow], }
end

/-- The “product formula” for Frobenius and Verschiebung. -/
lemma verschiebung_mul_frobenius (x y : 𝕎 R) :
  verschiebung (x * frobenius y) = verschiebung x * y :=
begin
  ghost_calc x y,
  rintro ⟨⟩; ghost_simp [mul_assoc]
end

end witt_vector
