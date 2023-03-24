/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.field.defs
import algebra.ring.opposite
import data.int.cast.lemmas

/-!
# Field structure on the multiplicative/additive opposite

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables (α : Type*)

namespace mul_opposite

@[to_additive] instance [has_rat_cast α] : has_rat_cast αᵐᵒᵖ := ⟨λ n, op n⟩

variables {α}

@[simp, norm_cast, to_additive]
lemma op_rat_cast [has_rat_cast α] (q : ℚ) : op (q : α) = q := rfl

@[simp, norm_cast, to_additive]
lemma unop_rat_cast [has_rat_cast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl

variables (α)

instance [division_semiring α] : division_semiring αᵐᵒᵖ :=
{ .. mul_opposite.group_with_zero α, .. mul_opposite.semiring α }

instance [division_ring α] : division_ring αᵐᵒᵖ :=
{ rat_cast := λ q, op q,
  rat_cast_mk := λ a b hb h, by { rw [rat.cast_def, op_div, op_nat_cast, op_int_cast],
    exact int.commute_cast _ _ },
  ..mul_opposite.division_semiring α, ..mul_opposite.ring α }

instance [semifield α] : semifield αᵐᵒᵖ :=
{ .. mul_opposite.division_semiring α, .. mul_opposite.comm_semiring α }

instance [field α] : field αᵐᵒᵖ :=
{ .. mul_opposite.division_ring α, .. mul_opposite.comm_ring α }

end mul_opposite

namespace add_opposite

instance [division_semiring α] : division_semiring αᵃᵒᵖ :=
{ ..add_opposite.group_with_zero α, ..add_opposite.semiring α }

instance [division_ring α] : division_ring αᵃᵒᵖ :=
{ ..add_opposite.group_with_zero α, ..add_opposite.ring α }

instance [semifield α] : semifield αᵃᵒᵖ :=
{ ..add_opposite.division_semiring α, ..add_opposite.comm_semiring α }

instance [field α] : field αᵃᵒᵖ :=
{ ..add_opposite.division_ring α, ..add_opposite.comm_ring α }

end add_opposite
