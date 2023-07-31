/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.order.field.basic
import algebra.order.positive.ring

/-!
# Algebraic structures on the set of positive numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the set of positive elements of a linear ordered field is a linear
ordered commutative group.
-/

variables {K : Type*} [linear_ordered_field K]

namespace positive

instance : has_inv {x : K // 0 < x} := ⟨λ x, ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp] lemma coe_inv (x : {x : K // 0 < x}) : ↑x⁻¹ = (x⁻¹ : K) := rfl

instance : has_pow {x : K // 0 < x} ℤ :=
⟨λ x n, ⟨x ^ n, zpow_pos_of_pos x.2 _⟩⟩

@[simp] lemma coe_zpow (x : {x : K // 0 < x}) (n : ℤ) : ↑(x ^ n) = (x ^ n : K) := rfl

instance : linear_ordered_comm_group {x : K // 0 < x} :=
{ mul_left_inv := λ a, subtype.ext $ inv_mul_cancel a.2.ne',
  .. positive.subtype.has_inv, .. positive.subtype.linear_ordered_cancel_comm_monoid }

end positive
