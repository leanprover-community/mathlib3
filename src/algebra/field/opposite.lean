/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.field.defs
import algebra.ring.opposite

/-!
# Field structure on the multiplicative/additive opposite

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables (α : Type*)

instance [division_semiring α] : division_semiring αᵐᵒᵖ :=
{ .. mul_opposite.group_with_zero α, .. mul_opposite.semiring α }

instance [division_ring α] : division_ring αᵐᵒᵖ :=
{ .. mul_opposite.group_with_zero α, .. mul_opposite.ring α }

instance [semifield α] : semifield αᵐᵒᵖ :=
{ .. mul_opposite.division_semiring α, .. mul_opposite.comm_semiring α }

instance [field α] : field αᵐᵒᵖ :=
{ .. mul_opposite.division_ring α, .. mul_opposite.comm_ring α }

instance [division_semiring α] : division_semiring αᵃᵒᵖ :=
{ ..add_opposite.group_with_zero α, ..add_opposite.semiring α }

instance [division_ring α] : division_ring αᵃᵒᵖ :=
{ ..add_opposite.group_with_zero α, ..add_opposite.ring α }

instance [semifield α] : semifield αᵃᵒᵖ :=
{ ..add_opposite.division_semiring α, ..add_opposite.comm_semiring α }

instance [field α] : field αᵃᵒᵖ :=
{ ..add_opposite.division_ring α, ..add_opposite.comm_ring α }
