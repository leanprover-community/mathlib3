/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.order.ring.basic
import algebra.order.sub.canonically_ordered

/-! # Canonically ordered commutative semirings. -/

variables {α : Type*}

set_option old_structure_cmd true

/-- A canonically ordered commutative semiring is an ordered, commutative semiring
in which `a ≤ b` iff there exists `c` with `b = a + c`. This is satisfied by the
natural numbers, for example, but not the integers or other ordered groups. -/
@[protect_proj]
class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_add_monoid α, comm_semiring α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

namespace canonically_ordered_comm_semiring
variables [canonically_ordered_comm_semiring α] {a b : α}

@[priority 100] -- see Note [lower instance priority]
instance to_no_zero_divisors : no_zero_divisors α :=
⟨canonically_ordered_comm_semiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩

@[priority 100] -- see Note [lower instance priority]
instance to_covariant_mul_le : covariant_class α α (*) (≤) :=
begin
  refine ⟨λ a b c h, _⟩,
  rcases exists_add_of_le h with ⟨c, rfl⟩,
  rw mul_add,
  apply self_le_add_right
end

@[priority 200] -- see Note [lower instance priority]
instance canonically_ordered_comm_semiring.to_pos_mul_mono : pos_mul_mono α :=
⟨λ x a b h, by { obtain ⟨d, rfl⟩ := exists_add_of_le h, simp_rw [left_distrib, le_self_add], }⟩

@[priority 200] -- see Note [lower instance priority]
instance canonically_ordered_comm_semiring.to_mul_pos_mono : mul_pos_mono α :=
⟨λ x a b h, by { obtain ⟨d, rfl⟩ := exists_add_of_le h, simp_rw [right_distrib, le_self_add], }⟩

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
lemma zero_lt_one [nontrivial α] : (0:α) < 1 := (zero_le 1).lt_of_ne zero_ne_one

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
