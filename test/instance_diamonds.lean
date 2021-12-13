/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.module.pi
import data.polynomial.basic
import group_theory.group_action.prod
import group_theory.group_action.units
import data.complex.module

/-! # Tests that instances do not form diamonds -/

/-! ## Scalar action instances -/
section has_scalar

example :
  (sub_neg_monoid.has_scalar_int : has_scalar ℤ ℂ) = (complex.has_scalar : has_scalar ℤ ℂ) :=
rfl

section units

example (α : Type*) [monoid α] :
  (units.mul_action : mul_action (units α) (α × α)) = prod.mul_action := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [Π i, mul_action R (β i)] :
  (units.mul_action : mul_action (units R) (Π i, β i)) = pi.mul_action _ := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [semiring α] [distrib_mul_action R α] :
  (units.distrib_mul_action : distrib_mul_action (units R) (polynomial α)) =
    polynomial.distrib_mul_action :=
rfl

/-!
TODO: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Emul_action'.20diamond/near/246402813
```lean
example {α : Type*} [comm_monoid α] :
  (units.mul_action' : mul_action (units α) (units α)) = monoid.to_mul_action _ :=
rfl -- fails
```
-/

end units

end has_scalar
