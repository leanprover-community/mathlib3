/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Eric Wieser
-/
import algebra.ring.equiv
import data.real.basic

/-! # Tautological equivalence of `ℝ` with Cauchy sequences

Separated from `data.real.basic` to avoid the `algebra.ring.equiv` import.
-/

namespace real

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equiv_Cauchy : ℝ ≃ cau_seq.completion.Cauchy :=
⟨real.cauchy, real.of_cauchy, λ ⟨_⟩, rfl, λ _, rfl⟩

/-- `real.equiv_Cauchy` as a ring equivalence. -/
@[simps]
def ring_equiv_Cauchy : ℝ ≃+* cau_seq.completion.Cauchy :=
{ to_fun := cauchy,
  inv_fun := of_cauchy,
  map_add' := cauchy_add,
  map_mul' := cauchy_mul,
  ..equiv_Cauchy }

end real
