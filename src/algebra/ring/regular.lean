/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.regular.basic
import algebra.ring.defs

/-!
# Lemmas about regular elements in rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_left_regular_of_non_zero_divisor [non_unital_non_assoc_ring α] (k : α)
  (h : ∀ (x : α), k * x = 0 → x = 0) : is_left_regular k :=
begin
  refine λ x y (h' : k * x = k * y), sub_eq_zero.mp (h _ _),
  rw [mul_sub, sub_eq_zero, h']
end

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_right_regular_of_non_zero_divisor [non_unital_non_assoc_ring α] (k : α)
  (h : ∀ (x : α), x * k = 0 → x = 0) : is_right_regular k :=
begin
  refine λ x y (h' : x * k = y * k), sub_eq_zero.mp (h _ _),
  rw [sub_mul, sub_eq_zero, h']
end

lemma is_regular_of_ne_zero' [non_unital_non_assoc_ring α] [no_zero_divisors α] {k : α}
  (hk : k ≠ 0) : is_regular k :=
⟨is_left_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk),
 is_right_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk)⟩

lemma is_regular_iff_ne_zero' [nontrivial α] [non_unital_non_assoc_ring α] [no_zero_divisors α]
  {k : α} : is_regular k ↔ k ≠ 0 :=
⟨λ h, by { rintro rfl, exact not_not.mpr h.left not_is_left_regular_zero }, is_regular_of_ne_zero'⟩

/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def no_zero_divisors.to_cancel_monoid_with_zero [ring α] [no_zero_divisors α] :
  cancel_monoid_with_zero α :=
{ mul_left_cancel_of_ne_zero := λ a b c ha,
    @is_regular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
  mul_right_cancel_of_ne_zero := λ a b c hb,
    @is_regular.right _ _ _ (is_regular_of_ne_zero' hb) _ _,
  .. (by apply_instance : monoid_with_zero α) }

/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def no_zero_divisors.to_cancel_comm_monoid_with_zero [comm_ring α] [no_zero_divisors α] :
  cancel_comm_monoid_with_zero α :=
{ .. no_zero_divisors.to_cancel_monoid_with_zero,
  .. (by apply_instance : comm_monoid_with_zero α) }

section is_domain

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_cancel_monoid_with_zero [semiring α] [is_domain α] :
  cancel_monoid_with_zero α :=
{ .. semiring.to_monoid_with_zero α, .. ‹is_domain α› }

variables [comm_semiring α] [is_domain α]

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_cancel_comm_monoid_with_zero : cancel_comm_monoid_with_zero α :=
{ .. ‹comm_semiring α›, .. ‹is_domain α› }

end is_domain
