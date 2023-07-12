/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.order.ring.defs
import algebra.order.sub.canonical
import group_theory.group_action.defs

/-!
# Canoncially ordered rings and semirings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `canonically_ordered_comm_semiring`
  - `canonically_ordered_add_monoid` & multiplication & `*` respects `≤` & no zero divisors
  - `comm_semiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `canonically_ordered_semiring`
They have yet to come up in practice.
-/

open function

set_option old_structure_cmd true

universe u
variables {α : Type u} {β : Type*}


/-- A canonically ordered commutative semiring is an ordered, commutative semiring in which `a ≤ b`
iff there exists `c` with `b = a + c`. This is satisfied by the natural numbers, for example, but
not the integers or other ordered groups. -/
@[protect_proj, ancestor canonically_ordered_add_monoid comm_semiring]
class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_add_monoid α, comm_semiring α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : α}, a * b = 0 → a = 0 ∨ b = 0)

section strict_ordered_semiring
variables [strict_ordered_semiring α] {a b c d : α}

section has_exists_add_of_le
variables [has_exists_add_of_le α]

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d :=
begin
  obtain ⟨b, rfl⟩ := exists_add_of_le hab,
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd,
  rw [mul_add, add_right_comm, mul_add, ←add_assoc],
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab $ (le_add_iff_nonneg_right _).1 hcd) _,
end

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul' (hba : b ≤ a) (hdc : d ≤ c) : a • d + b • c ≤ a • c + b • d :=
by { rw [add_comm (a • d), add_comm (a • c)], exact mul_add_mul_le_mul_add_mul hba hdc }

/-- Binary strict **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d :=
begin
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le,
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le,
  rw [mul_add, add_right_comm, mul_add, ←add_assoc],
  exact add_lt_add_left (mul_lt_mul_of_pos_right hab $ (lt_add_iff_pos_right _).1 hcd) _,
end

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul' (hba : b < a) (hdc : d < c) : a • d + b • c < a • c + b • d :=
by { rw [add_comm (a • d), add_comm (a • c)], exact mul_add_mul_lt_mul_add_mul hba hdc }

end has_exists_add_of_le

end strict_ordered_semiring

namespace canonically_ordered_comm_semiring
variables [canonically_ordered_comm_semiring α] {a b : α}

@[priority 100] -- see Note [lower instance priority]
instance to_no_zero_divisors : no_zero_divisors α :=
⟨λ a b h, canonically_ordered_comm_semiring.eq_zero_or_eq_zero_of_mul_eq_zero h⟩

@[priority 100] -- see Note [lower instance priority]
instance to_covariant_mul_le : covariant_class α α (*) (≤) :=
begin
  refine ⟨λ a b c h, _⟩,
  rcases exists_add_of_le h with ⟨c, rfl⟩,
  rw mul_add,
  apply self_le_add_right
end

@[priority 100] -- see Note [lower instance priority]
instance to_ordered_comm_monoid : ordered_comm_monoid α :=
{ mul_le_mul_left := λ _ _, mul_le_mul_left',
  .. ‹canonically_ordered_comm_semiring α› }

@[priority 100] -- see Note [lower instance priority]
instance to_ordered_comm_semiring : ordered_comm_semiring α :=
{ zero_le_one := zero_le _,
  mul_le_mul_of_nonneg_left := λ a b c h _, mul_le_mul_left' h _,
  mul_le_mul_of_nonneg_right := λ a b c h _, mul_le_mul_right' h _,
  ..‹canonically_ordered_comm_semiring α› }

@[simp] lemma mul_pos : 0 < a * b ↔ (0 < a) ∧ (0 < b) :=
by simp only [pos_iff_ne_zero, ne.def, mul_eq_zero, not_or_distrib]


end canonically_ordered_comm_semiring

section sub

variables [canonically_ordered_comm_semiring α] {a b c : α}
variables [has_sub α] [has_ordered_sub α]

variables [is_total α (≤)]

namespace add_le_cancellable
protected lemma mul_tsub (h : add_le_cancellable (a * c)) :
  a * (b - c) = a * b - a * c :=
begin
  cases total_of (≤) b c with hbc hcb,
  { rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)] },
  { apply h.eq_tsub_of_add_eq, rw [← mul_add, tsub_add_cancel_of_le hcb] }
end

protected lemma tsub_mul (h : add_le_cancellable (b * c)) : (a - b) * c = a * c - b * c :=
by { simp only [mul_comm _ c] at *, exact h.mul_tsub }

end add_le_cancellable

variables [contravariant_class α α (+) (≤)]

lemma mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
contravariant.add_le_cancellable.mul_tsub

lemma tsub_mul (a b c : α) : (a - b) * c = a * c - b * c :=
contravariant.add_le_cancellable.tsub_mul

end sub
