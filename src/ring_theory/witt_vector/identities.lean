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
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
noncomputable theory

include hp

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
lemma frobenius_verschiebung (x : 𝕎 R) :
  frobenius (verschiebung x) = x * p :=
begin
  polify x,
  introsI,
  simp only [ghost_component_verschiebung, ghost_component_frobenius,
    ring_hom.map_mul, ring_hom.map_nat_cast, mul_comm],
end

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
  polify x y,
  rintro S _Scr x y ⟨⟩; resetI;
  simp [ghost_component_zero_verschiebung, zero_mul, ring_hom.map_mul,
    ghost_component_verschiebung, ghost_component_frobenius, nat.succ_eq_add_one, mul_assoc],
end

end witt_vector
