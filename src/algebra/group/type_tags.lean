/--
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Type tags `multiplicative` and `additive` that turn additive structures into multiplicative, and vice versa
-/

import algebra.group.hom

universes u v
variables {α : Type u} {β : Type v}

def additive (α : Type*) := α
def multiplicative (α : Type*) := α

instance [semigroup α] : add_semigroup (additive α) :=
{ add := ((*) : α → α → α),
  add_assoc := @mul_assoc _ _ }

instance [add_semigroup α] : semigroup (multiplicative α) :=
{ mul := ((+) : α → α → α),
  mul_assoc := @add_assoc _ _ }

instance [comm_semigroup α] : add_comm_semigroup (additive α) :=
{ add_comm := @mul_comm _ _,
  ..additive.add_semigroup }

instance [add_comm_semigroup α] : comm_semigroup (multiplicative α) :=
{ mul_comm := @add_comm _ _,
  ..multiplicative.semigroup }

instance [left_cancel_semigroup α] : add_left_cancel_semigroup (additive α) :=
{ add_left_cancel := @mul_left_cancel _ _,
  ..additive.add_semigroup }

instance [add_left_cancel_semigroup α] : left_cancel_semigroup (multiplicative α) :=
{ mul_left_cancel := @add_left_cancel _ _,
  ..multiplicative.semigroup }

instance [right_cancel_semigroup α] : add_right_cancel_semigroup (additive α) :=
{ add_right_cancel := @mul_right_cancel _ _,
  ..additive.add_semigroup }

instance [add_right_cancel_semigroup α] : right_cancel_semigroup (multiplicative α) :=
{ mul_right_cancel := @add_right_cancel _ _,
  ..multiplicative.semigroup }

instance [monoid α] : add_monoid (additive α) :=
{ zero     := (1 : α),
  zero_add := @one_mul _ _,
  add_zero := @mul_one _ _,
  ..additive.add_semigroup }

instance [add_monoid α] : monoid (multiplicative α) :=
{ one     := (0 : α),
  one_mul := @zero_add _ _,
  mul_one := @add_zero _ _,
  ..multiplicative.semigroup }

instance [comm_monoid α] : add_comm_monoid (additive α) :=
{ add_comm := @mul_comm α _,
  ..additive.add_monoid }

instance [add_comm_monoid α] : comm_monoid (multiplicative α) :=
{ mul_comm := @add_comm α _,
  ..multiplicative.monoid }

instance [group α] : add_group (additive α) :=
{ neg := @has_inv.inv α _,
  add_left_neg := @mul_left_inv _ _,
  ..additive.add_monoid }

instance [add_group α] : group (multiplicative α) :=
{ inv := @has_neg.neg α _,
  mul_left_inv := @add_left_neg _ _,
  ..multiplicative.monoid }

instance [comm_group α] : add_comm_group (additive α) :=
{ add_comm := @mul_comm α _,
  ..additive.add_group }

instance [add_comm_group α] : comm_group (multiplicative α) :=
{ mul_comm := @add_comm α _,
  ..multiplicative.group }

instance additive.is_add_group_hom [group α] [group β] (f : α → β) [is_group_hom f] :
  @is_add_group_hom (additive α) (additive β) _ _ f :=
⟨@is_group_hom.map_mul α β _ _ f _⟩

instance multiplicative.is_group_hom [add_group α] [add_group β] (f : α → β) [is_add_group_hom f] :
  @is_group_hom (multiplicative α) (multiplicative β) _ _ f :=
⟨@is_add_group_hom.map_add α β _ _ f _⟩

attribute [to_additive additive.is_add_group_hom] multiplicative.is_group_hom
