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
open_locale polynomial

example :
  (sub_neg_monoid.has_scalar_int : has_scalar ℤ ℂ) = (complex.has_scalar : has_scalar ℤ ℂ) :=
rfl

example (α β : Type*) [add_monoid α] [add_monoid β] :
  (prod.has_scalar : has_scalar ℕ (α × β)) = add_monoid.has_scalar_nat := rfl

example (α β : Type*) [sub_neg_monoid α] [sub_neg_monoid β] :
  (prod.has_scalar : has_scalar ℤ (α × β)) = sub_neg_monoid.has_scalar_int := rfl

example (α : Type*) (β : α → Type*) [Π a, add_monoid (β a)] :
  (pi.has_scalar : has_scalar ℕ (Π a, β a)) = add_monoid.has_scalar_nat := rfl

example (α : Type*) (β : α → Type*) [Π a, sub_neg_monoid (β a)] :
  (pi.has_scalar : has_scalar ℤ (Π a, β a)) = sub_neg_monoid.has_scalar_int := rfl

section units

example (α : Type*) [monoid α] :
  (units.mul_action : mul_action αˣ (α × α)) = prod.mul_action := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [Π i, mul_action R (β i)] :
  (units.mul_action : mul_action Rˣ (Π i, β i)) = pi.mul_action _ := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [semiring α] [distrib_mul_action R α] :
  (units.distrib_mul_action : distrib_mul_action Rˣ α[X]) =
    polynomial.distrib_mul_action :=
rfl

/-!
TODO: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Emul_action'.20diamond/near/246402813
```lean
example {α : Type*} [comm_monoid α] :
  (units.mul_action' : mul_action αˣ αˣ) = monoid.to_mul_action _ :=
rfl -- fails
```
-/

end units

end has_scalar

/-! ## `with_top` (Type with point at infinity) instances -/
section with_top

example (R : Type*) [h : ordered_semiring R] :
  (@with_top.add_comm_monoid R
    (@non_unital_non_assoc_semiring.to_add_comm_monoid R
      (@non_assoc_semiring.to_non_unital_non_assoc_semiring R
        (@semiring.to_non_assoc_semiring R
          (@ordered_semiring.to_semiring R h)))))
        =
  (@ordered_add_comm_monoid.to_add_comm_monoid (with_top R)
    (@with_top.ordered_add_comm_monoid R
      (@ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid R
        (@ordered_semiring.to_ordered_cancel_add_comm_monoid R h)))) :=
rfl

end with_top

/-! ## `multiplicative` instances -/
section multiplicative

example :
  @monoid.to_mul_one_class (multiplicative ℕ) (comm_monoid.to_monoid _) =
    multiplicative.mul_one_class :=
rfl

-- `dunfold` can still break unification, but it's better to have `dunfold` break it than have the
-- above example fail.
example :
  @monoid.to_mul_one_class (multiplicative ℕ) (comm_monoid.to_monoid _) =
    multiplicative.mul_one_class :=
begin
  dunfold has_one.one multiplicative.mul_one_class,
  success_if_fail { refl, },
  ext,
  refl
end

end multiplicative
