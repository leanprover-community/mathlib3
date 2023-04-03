/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import data.polynomial.basic
import set_theory.cardinal.ordinal
/-!
# Cardinality of Polynomial Ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The reuslt in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/
universe u

open_locale cardinal polynomial
open cardinal

namespace polynomial

@[simp] lemma cardinal_mk_eq_max {R : Type u} [semiring R] [nontrivial R] : #R[X] = max (#R) ℵ₀ :=
(to_finsupp_iso R).to_equiv.cardinal_eq.trans $
  by { rw [add_monoid_algebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm], refl }

lemma cardinal_mk_le_max {R : Type u} [semiring R] : #R[X] ≤ max (#R) ℵ₀ :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0) },
  { exact cardinal_mk_eq_max.le },
end

end polynomial
