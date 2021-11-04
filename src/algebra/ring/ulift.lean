/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.ulift
import data.equiv.ring

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
by refine_struct { zero := (0 : ulift α), mul := (*), .. }; tactic.pi_instance_derive_field

instance distrib [distrib α] : distrib (ulift α) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance non_unital_non_assoc_semiring [non_unital_non_assoc_semiring α] :
  non_unital_non_assoc_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*),
  nsmul := λ n f, ⟨nsmul n f.down⟩, };
tactic.pi_instance_derive_field

instance non_assoc_semiring [non_assoc_semiring α] : non_assoc_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := λ n f, ⟨nsmul n f.down⟩ };
tactic.pi_instance_derive_field

instance non_unital_semiring [non_unital_semiring α] : non_unital_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*),
  nsmul := λ n f, ⟨nsmul n f.down⟩, };
tactic.pi_instance_derive_field

instance semiring [semiring α] : semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := λ n f, ⟨nsmul n f.down⟩, npow := λ n f, ⟨npow n f.down⟩ };
tactic.pi_instance_derive_field

/--
The ring equivalence between `ulift α` and `α`.
-/
def ring_equiv [non_unital_non_assoc_semiring α] : ulift α ≃+* α :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_mul' := λ x y, rfl,
  map_add' := λ x y, rfl,
  left_inv := by tidy,
  right_inv := by tidy, }

instance comm_semiring [comm_semiring α] : comm_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := λ n f, ⟨nsmul n f.down⟩, npow := λ n f, ⟨npow n f.down⟩ };
tactic.pi_instance_derive_field

instance ring [ring α] : ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := λ n f, ⟨nsmul n f.down⟩, npow := λ n f, ⟨npow n f.down⟩,
  zsmul := λ n f, ⟨zsmul n f.down⟩ };
tactic.pi_instance_derive_field

instance comm_ring [comm_ring α] : comm_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := λ n f, ⟨nsmul n f.down⟩, npow := λ n f, ⟨npow n f.down⟩,
  zsmul := λ n f, ⟨zsmul n f.down⟩ };
tactic.pi_instance_derive_field

end ulift
