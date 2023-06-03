/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import order.hom.basic
import order.min_max
import algebra.group.units

/-!
# Units in ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

namespace units

@[to_additive]
instance [monoid α] [preorder α] : preorder αˣ :=
preorder.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) < b ↔ a < b := iff.rfl

@[to_additive]
instance [monoid α] [partial_order α] : partial_order αˣ :=
partial_order.lift coe units.ext

@[to_additive]
instance [monoid α] [linear_order α] : linear_order αˣ :=
linear_order.lift' coe units.ext

/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.", simps { fully_applied := ff }]
def order_embedding_coe [monoid α] [linear_order α] : αˣ ↪o α := ⟨⟨coe, ext⟩, λ _ _, iff.rfl⟩

@[simp, norm_cast, to_additive]
theorem max_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(max a b) : α) = max a b :=
monotone.map_max order_embedding_coe.monotone

@[simp, norm_cast, to_additive]
theorem min_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(min a b) : α) = min a b :=
monotone.map_min order_embedding_coe.monotone

end units
