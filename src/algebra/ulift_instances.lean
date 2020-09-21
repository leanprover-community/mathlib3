/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.ring

/-
## Algebraic instances for ulift

In this file we lift algebraic instances on a type `α : Type u` to `ulift.{v} α`.
-/

universe variables v u

namespace ulift
variables (α : Type u)

@[to_additive]
instance [has_one α] : has_one (ulift.{v} α) :=
⟨⟨1⟩⟩

@[to_additive]
instance [has_mul α] : has_mul (ulift.{v} α) :=
⟨λ x y, ⟨x.down * y.down⟩⟩

@[to_additive]
instance [has_inv α] : has_inv (ulift.{v} α) :=
⟨λ x, ⟨x.down⁻¹⟩⟩

@[to_additive]
instance [semigroup α] : semigroup (ulift.{v} α) :=
{ mul_assoc := λ ⟨x⟩ ⟨y⟩ ⟨z⟩, show up (x * y * z) = up (x * (y * z)), by rw mul_assoc,
  .. ulift.has_mul α }

@[to_additive]
instance [comm_semigroup α] : comm_semigroup (ulift.{v} α) :=
{ mul_comm := λ ⟨x⟩ ⟨y⟩, show up (x * y) = up (y * x), by rw mul_comm,
  .. ulift.semigroup α }

@[to_additive]
instance [monoid α] : monoid (ulift.{v} α) :=
{ one_mul := λ ⟨x⟩, show up (1 * x) = up x, by rw one_mul,
  mul_one := λ ⟨x⟩, show up (x * 1) = up x, by rw mul_one,
  .. ulift.semigroup α, .. ulift.has_one α }

@[to_additive]
instance [comm_monoid α] : comm_monoid (ulift.{v} α) :=
{ .. ulift.monoid α, .. ulift.comm_semigroup α }

@[to_additive]
instance [group α] : group (ulift.{v} α) :=
{ mul_left_inv := λ ⟨x⟩, show up (x⁻¹ * x) = up 1, by rw mul_left_inv,
  .. ulift.monoid α, .. ulift.has_inv α }

@[to_additive]
instance [comm_group α] : comm_group (ulift.{v} α) :=
{ .. ulift.group α, .. ulift.comm_semigroup α }

instance [mul_zero_class α] : mul_zero_class (ulift.{v} α) :=
{ mul_zero := λ ⟨x⟩, show up (x * 0) = up 0, by rw mul_zero,
  zero_mul := λ ⟨x⟩, show up (0 * x) = up 0, by rw zero_mul,
  .. ulift.has_mul α, .. ulift.has_zero α }

instance [distrib α] : distrib (ulift.{v} α) :=
{ left_distrib  := λ ⟨x⟩ ⟨y⟩ ⟨z⟩, show up (x * (y + z)) = up (x * y + x * z), by rw mul_add,
  right_distrib := λ ⟨x⟩ ⟨y⟩ ⟨z⟩, show up ((x + y) * z) = up (x * z + y * z), by rw add_mul,
  .. ulift.has_add α, .. ulift.has_mul α }

instance [semiring α] : semiring (ulift.{v} α) :=
{ .. ulift.add_comm_monoid α, .. ulift.monoid α, .. ulift.mul_zero_class α, .. ulift.distrib α }

instance [comm_semiring α] : comm_semiring (ulift.{v} α) :=
{ .. ulift.semiring α, .. ulift.comm_monoid α }

instance [ring α] : ring (ulift.{v} α) :=
{ .. ulift.semiring α, .. ulift.add_group α }

instance [comm_ring α] : comm_ring (ulift.{v} α) :=
{ .. ulift.ring α, .. ulift.comm_semiring α }

/-
TODO:

monoid_with_zero, group_with_zero, cancel_*,
division_ring, field

-/

@[to_additive]
def up_mul_hom [monoid α] : α →* ulift.{v} α :=
{ to_fun := up,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

def up_ring_hom [semiring α] : α →+* ulift.{v} α :=
{ .. up_add_hom α, .. up_mul_hom α }

lemma up_injective : function.injective (up : α → ulift.{v} α) :=
λ x y h, congr_arg ulift.down h

lemma up_surjective : function.surjective (up : α → ulift.{v} α) :=
λ ⟨x⟩, ⟨x, rfl⟩

lemma up_bijective : function.bijective (up : α → ulift.{v} α) :=
⟨up_injective α, up_surjective α⟩

end ulift
