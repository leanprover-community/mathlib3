/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial.basic
import data.zmod.basic

/-!
## Facts concerning polynomials over `zmod n`
-/

namespace mv_polynomial

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `zmod n`. -/
lemma C_dvd_iff_zmod {σ : Type*} (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
C_dvd_iff_map_hom_eq_zero _ _ (char_p.int_cast_eq_zero_iff (zmod n) n) _

end mv_polynomial
