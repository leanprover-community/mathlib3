/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.mv_polynomial.cardinal
import data.mv_polynomial.equiv
/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ℵ₀`.
-/
universe u

open_locale cardinal polynomial
open cardinal

namespace polynomial

lemma cardinal_mk_le_max {R : Type u} [comm_semiring R] : #R[X] ≤ max (#R) ℵ₀ :=
calc #R[X] = #(mv_polynomial punit.{u + 1} R) :
  cardinal.eq.2 ⟨(mv_polynomial.punit_alg_equiv.{u u} R).to_equiv.symm⟩
... ≤ _ : mv_polynomial.cardinal_mk_le_max
... ≤ _ : by rw [max_assoc, max_eq_right (lt_aleph_0_of_finite punit).le]

end polynomial
