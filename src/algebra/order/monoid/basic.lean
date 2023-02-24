/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.defs
import algebra.group.inj_surj
import order.hom.basic

/-!
# Ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops some additional material on ordered monoids.
-/

set_option old_structure_cmd true
open function

universe u
variables {α : Type u} {β : Type*}

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid [ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c, show f (c * a) ≤ f (c * b), by
  { rw [mul, mul], apply mul_le_mul_left', exact ab },
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul npow }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_comm_monoid [linear_ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β] [has_pow β ℕ] [has_sup β] [has_inf β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_monoid β :=
{ .. hf.ordered_comm_monoid f one mul npow,
  .. linear_order.lift f hf hsup hinf }

-- TODO find a better home for the next two constructions.

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `a + b`, for some fixed `a`.
  See also `order_iso.add_left` when working in an additive ordered group.", simps]
def order_embedding.mul_left
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (*) (<)] (m : α) : α ↪o α :=
order_embedding.of_strict_mono (λ n, m * n) (λ a b w, mul_lt_mul_left' w m)

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `b + a`, for some fixed `a`.
  See also `order_iso.add_right` when working in an additive ordered group.", simps]
def order_embedding.mul_right
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (swap (*)) (<)] (m : α) :
  α ↪o α :=
order_embedding.of_strict_mono (λ n, n * m) (λ a b w, mul_lt_mul_right' w m)
