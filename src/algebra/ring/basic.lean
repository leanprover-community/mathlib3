/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.ring.defs
import algebra.hom.group
import algebra.opposites

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.defs`.

-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open function

namespace add_hom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_left {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨(*) r, mul_add r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_right {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨λ a, a * r, λ _ _, add_mul _ _ r⟩

end add_hom

section add_hom_class

variables {F : Type*} [non_assoc_semiring α] [non_assoc_semiring β] [add_hom_class F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp] lemma map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
map_add _ _ _

end add_hom_class

namespace add_monoid_hom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := (*) r,
  map_zero' := mul_zero r,
  map_add' := mul_add r }

@[simp] lemma coe_mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_left r) = (*) r := rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := λ a, a * r,
  map_zero' := zero_mul r,
  map_add' := λ _ _, add_mul _ _ r }

@[simp] lemma coe_mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_right r) = (* r) := rfl

lemma mul_right_apply {R : Type*} [non_unital_non_assoc_semiring R] (a r : R) :
  mul_right r a = a * r := rfl

end add_monoid_hom

section has_distrib_neg

section has_mul
variables [has_mul α] [has_distrib_neg α]

open mul_opposite

instance : has_distrib_neg αᵐᵒᵖ :=
{ neg_mul := λ _ _, unop_injective $ mul_neg _ _,
  mul_neg := λ _ _, unop_injective $ neg_mul _ _,
  ..mul_opposite.has_involutive_neg _ }

end has_mul

section group
variables [group α] [has_distrib_neg α]

@[simp] lemma inv_neg' (a : α) : (- a)⁻¹ = - a⁻¹ :=
by rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg,neg_neg, mul_left_inv]

end group

end has_distrib_neg

section non_unital_comm_ring
variables [non_unital_comm_ring α] {a b c : α}

local attribute [simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm]),
  refine ⟨b - x, _, by simp, by rw this⟩,
  rw [this, sub_add, ← sub_mul, sub_self]
end

end non_unital_comm_ring

lemma succ_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a + 1 ≠ a :=
λ h, one_ne_zero ((add_right_inj a).mp (by simp [h]))

lemma pred_ne_self [non_assoc_ring α] [nontrivial α] (a : α) : a - 1 ≠ a :=
λ h, one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))

section no_zero_divisors

variable (α)

lemma is_left_cancel_mul_zero.to_no_zero_divisors [ring α] [is_left_cancel_mul_zero α] :
  no_zero_divisors α :=
begin
  refine ⟨λ x y h, _⟩,
  by_cases hx : x = 0,
  { left, exact hx },
  { right,
    rw [← sub_zero (x * y), ← mul_zero x, ← mul_sub] at h,
    convert (is_left_cancel_mul_zero.mul_left_cancel_of_ne_zero) hx h,
    rw [sub_zero] }
end

lemma is_right_cancel_mul_zero.to_no_zero_divisors [ring α] [is_right_cancel_mul_zero α] :
  no_zero_divisors α :=
begin
  refine ⟨λ x y h, _⟩,
  by_cases hy : y = 0,
  { right, exact hy },
  { left,
    rw [← sub_zero (x * y), ← zero_mul y, ← sub_mul] at h,
    convert (is_right_cancel_mul_zero.mul_right_cancel_of_ne_zero) hy h,
    rw [sub_zero] }
end

@[priority 100]
instance no_zero_divisors.to_is_cancel_mul_zero [ring α] [no_zero_divisors α] :
  is_cancel_mul_zero α :=
{ mul_left_cancel_of_ne_zero := λ a b c ha h,
  begin
    rw [← sub_eq_zero, ← mul_sub] at h,
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  end,
  mul_right_cancel_of_ne_zero := λ a b c hb h,
  begin
    rw [← sub_eq_zero, ← sub_mul] at h,
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)
  end }

lemma no_zero_divisors.to_is_domain [ring α] [h : nontrivial α] [no_zero_divisors α] :
  is_domain α :=
{ .. no_zero_divisors.to_is_cancel_mul_zero α, .. h }

@[priority 100]
instance is_domain.to_no_zero_divisors [ring α] [is_domain α] : no_zero_divisors α :=
is_right_cancel_mul_zero.to_no_zero_divisors α

end no_zero_divisors
