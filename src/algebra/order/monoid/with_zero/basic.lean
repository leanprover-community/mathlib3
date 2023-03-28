/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.with_zero.defs
import algebra.group_with_zero.basic

/-!
# An instance orphaned from `algebra.order.monoid.with_zero.defs`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We put this here to minimise imports: if you can move it back into
`algebra.order.monoid.with_zero.defs` without increasing imports, please do.
-/

open function

universe u
variables {α : Type u}

namespace with_zero

instance contravariant_class_mul_lt {α : Type u} [has_mul α] [partial_order α]
  [contravariant_class α α (*) (<)] :
  contravariant_class (with_zero α) (with_zero α) (*) (<) :=
begin
  refine ⟨λ a b c h, _⟩,
  have := ((zero_le _).trans_lt h).ne',
  lift a to α using left_ne_zero_of_mul this,
  lift c to α using right_ne_zero_of_mul this,
  induction b using with_zero.rec_zero_coe,
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' $ coe_lt_coe.mp h)]
end

end with_zero
