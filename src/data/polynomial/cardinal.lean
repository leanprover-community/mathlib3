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
of `#R` and `ω`.
-/
universe u

open_locale cardinal
open cardinal

namespace polynomial

lemma cardinal_mk_le_max {R : Type u} [comm_semiring R] : #(polynomial R) ≤ max (#R) ω :=
calc #(polynomial R) = #(mv_polynomial punit.{u + 1} R) :
  cardinal.eq.2 ⟨(mv_polynomial.punit_alg_equiv.{u u} R).to_equiv.symm⟩
... ≤ _ : mv_polynomial.cardinal_mk_le_max
... ≤ _ : begin
  have : #(punit.{u + 1}) ≤ ω, from le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩),
  rw [max_assoc, max_eq_right this]
end

end polynomial
