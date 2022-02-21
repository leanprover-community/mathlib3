/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.ulift
import data.equiv.transfer_instance

/-!
# `ulift` instances for ring

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/

universes u v
variables {α : Type u} {x y : ulift.{v} α}

namespace ulift

instance mul_zero_class [mul_zero_class α] : mul_zero_class (ulift α) :=
equiv.ulift.mul_zero_class

instance distrib [distrib α] : distrib (ulift α) :=
equiv.ulift.distrib

instance non_unital_non_assoc_semiring [non_unital_non_assoc_semiring α] :
  non_unital_non_assoc_semiring (ulift α) :=
equiv.ulift.non_unital_non_assoc_semiring

instance non_assoc_semiring [non_assoc_semiring α] : non_assoc_semiring (ulift α) :=
equiv.ulift.non_assoc_semiring

instance non_unital_semiring [non_unital_semiring α] : non_unital_semiring (ulift α) :=
equiv.ulift.non_unital_semiring

instance semiring [semiring α] : semiring (ulift α) :=
equiv.ulift.semiring

/--
The ring equivalence between `ulift α` and `α`.
-/
def ring_equiv [non_unital_non_assoc_semiring α] : ulift α ≃+* α :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_mul' := λ x y, rfl,
  map_add' := λ x y, rfl,
  left_inv := λ ⟨x⟩, rfl,
  right_inv := λ x, rfl, }

instance comm_semiring [comm_semiring α] : comm_semiring (ulift α) :=
equiv.ulift.comm_semiring

instance non_unital_non_assoc_ring [non_unital_non_assoc_ring α] :
  non_unital_non_assoc_ring (ulift α) :=
equiv.ulift.non_unital_non_assoc_ring

instance ring [ring α] : ring (ulift α) :=
equiv.ulift.ring

instance comm_ring [comm_ring α] : comm_ring (ulift α) :=
equiv.ulift.comm_ring

instance field [field α] : field (ulift α) :=
equiv.ulift.field

end ulift
