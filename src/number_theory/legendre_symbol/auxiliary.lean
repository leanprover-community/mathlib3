/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import algebra.group_power.basic
import algebra.group_with_zero.basic

/-!
# Some auxiliary results

We collect some results here that are not specific to quadratic characters
or Legendre symbols, but are needed in some places there.
They will be moved to appropriate places eventually.
-/

section monoid
-- Auxiliary stuff for monoids

-- This would fit in `algebra.group_power.basic`, where `pow_monoid_hom` is defined,
-- but there, `zero_pow` is unknown,
-- or in `algebra.group_with_zero.basic`, but there, `pow_monoid_hom` is unknown.
/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `monoid_with_zero_hom` -/
def pow_monoid_with_zero_hom {M : Type*} [comm_monoid_with_zero M] {n : ℕ} (hn : 0 < n) :
  M →*₀ M :=
{ map_zero' := zero_pow hn,
  ..pow_monoid_hom n }

end monoid
