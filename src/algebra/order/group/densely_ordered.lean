/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.canonical.defs
import algebra.order.group.defs
import algebra.order.monoid.order_dual

/-!
# Lemmas about densely linearly ordered groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

section densely_ordered
variables [group α] [linear_order α]
variables [covariant_class α α (*) (≤)]
variables [densely_ordered α] {a b c : α}

@[to_additive]
lemma le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b :=
@le_of_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _ _ _ h

@[to_additive]
lemma le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
le_of_forall_lt_one_mul_le $ λ ε ε1,
  by simpa only [div_eq_mul_inv, inv_inv]  using h ε⁻¹ (left.one_lt_inv_iff.2 ε1)

@[to_additive]
lemma le_iff_forall_one_lt_le_mul : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
⟨λ h ε ε_pos, le_mul_of_le_of_one_le h ε_pos.le, le_of_forall_one_lt_le_mul⟩

@[to_additive]
lemma le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b :=
@le_iff_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _

end densely_ordered
