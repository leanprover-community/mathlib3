/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace

/-!
# Monoid representations

This file introduces monoid representations and their characters and proves basic lemmas about them,
including equivalences between different definitions of representations.

## Main definitions

  * `representation.as_module`
  * `representation.as_group_hom`
  * `representation.character`

## Implementation notes

A representation of a monoid `G` over a commutative semiring `k` is implemented as a `k`-module `V`
together with a `distrib_mul_action G V` instance and a `smul_comm_class G k V` instance.

Alternatively, one can use a monoid homomorphism `G →* (V →ₗ[k] V)`. The definitions `as_monoid_hom`
and `rep_space` allow to go back and forth between these two definitions.
-/

open monoid_algebra

namespace representation

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (module.End k V) :=
  (lift k G _) (distrib_mul_action.to_module_End k V)

lemma as_algebra_hom_def :
  as_algebra_hom k G V = (lift k G _) (distrib_mul_action.to_module_End k V) := rfl

@[simp]
lemma as_algebra_hom_single (g : G):
  (as_algebra_hom k G V (finsupp.single g 1)) = (distrib_mul_action.to_module_End k V) g :=
by simp [as_algebra_hom_def]

/--
A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable instance as_module : module (monoid_algebra k G) V :=
  module.comp_hom V (as_algebra_hom k G V).to_ring_hom

lemma as_module_apply (a : monoid_algebra k G) (v : V):
  a • v = (as_algebra_hom k G V a) v := rfl

lemma of_smul (g : G) (v : V) :
  (of k G g) • v =  g • v := by simp [as_module_apply]

instance as_module_scalar_tower : is_scalar_tower k (monoid_algebra k G) V :=
{ smul_assoc := λ r a v, by simp [as_module_apply] }

instance as_module_smul_comm : smul_comm_class k (monoid_algebra k G) V :=
{ smul_comm := λ r a v, by simp [as_module_apply] }

end

section group
variables (k G V : Type*) [comm_semiring k] [group G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def as_group_hom : G →* units (V →ₗ[k] V) :=
  monoid_hom.to_hom_units (distrib_mul_action.to_module_End k V)

end group

section character

variables (k G V : Type*) [field k] [group G] [add_comm_group V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
The character associated to a representation of `G`, which as a map `G → k`
sends each element to the trace of the corresponding linear map.
-/
@[simp]
noncomputable def character (g : G) : k :=
linear_map.trace k V (as_group_hom k G V g)

/-- The evaluation of the character at the identity is the dimension of the representation. -/
theorem char_one : character k G V 1 = finite_dimensional.finrank k V := by simp

/-- The character of a representation is constant on conjugacy classes. -/
theorem char_conj (g : G) (h : G) : (character k G V) (h * g * h⁻¹) = (character k G V) g := by simp

end character

end representation
