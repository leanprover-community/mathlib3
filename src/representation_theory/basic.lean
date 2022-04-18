/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace
import linear_algebra.dual

/-!
# Monoid representations

This file introduces monoid representations and their characters and proves basic lemmas about them,
including equivalences between different definitions of representations.

## Main definitions

  * `representation.as_module`
  * `representation.as_group_hom`
  * `representation.character`
  * `representation.tensor_rep`

## Implementation notes

A representation of a monoid `G` over a commutative semiring `k` is implemented as a `k`-module `V`
together with a `distrib_mul_action G V` instance and a `smul_comm_class G k V` instance.
-/

open monoid_algebra
open linear_map
open distrib_mul_action

namespace representation

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (module.End k V) :=
  (lift k G _) (to_module_End k V)

lemma as_algebra_hom_def :
  as_algebra_hom k G V = (lift k G _) (to_module_End k V) := rfl

@[simp]
lemma as_algebra_hom_single (g : G):
  (as_algebra_hom k G V (finsupp.single g 1)) = (to_module_End k V) g :=
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

/--
The trivial one-dimensional representation of `G` over `k`.
-/
@[derive [add_comm_monoid, module k], nolint unused_arguments]
def trivial_rep : Type* := k

instance trivial_rep_inhabited : inhabited (trivial_rep k) := {default := 0}

instance trivial_rep_distrib_mul_action : distrib_mul_action G (trivial_rep k) :=
{ smul := λ g x, x,
  one_smul := λ x, by simp,
  mul_smul := λ g h x, by simp,
  smul_add := λ g x y, by simp,
  smul_zero := λ g, by simp}

@[simp]
lemma trivial_rep_def (g : G) (x : trivial_rep k) : g • x = x := rfl

instance trivial_rep_smul_comm_class : smul_comm_class G k (trivial_rep k) :=
{smul_comm := λ g r x, by simp}

end

section group
variables (k G V : Type*) [comm_semiring k] [group G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def as_group_hom : G →* units (V →ₗ[k] V) :=
  monoid_hom.to_hom_units (to_module_End k V)

end group

section character

variables (k G V : Type*) [field k] [group G] [add_comm_group V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
The character associated to a representation of `G`, which as a map `G → k`
sends each element to the trace of the corresponding linear map.
-/
@[simp]
noncomputable def character (g : G) : k := trace k V (as_group_hom k G V g)

/-- The evaluation of the character at the identity is the dimension of the representation. -/
theorem char_one : character k G V 1 = finite_dimensional.finrank k V := by simp

/-- The character of a representation is constant on conjugacy classes. -/
theorem char_conj (g : G) (h : G) : (character k G V) (h * g * h⁻¹) = (character k G V) g := by simp

end character

section linear_hom

variables {k G V W : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [add_comm_monoid W]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]
variables [module k W] [distrib_mul_action G W] [smul_comm_class G k W]

/--
Given two `k`-linear representations `V` and `W` of a group `G`,
the space are linear maps `V →ₗ[k] W` is itself a representation of `G`.
-/
instance  linear_hom_distrib_mul_action : distrib_mul_action G (V →ₗ[k] W) :=
{ smul := λ g f, ↑(as_group_hom k G W g) ∘ₗ f ∘ₗ ↑(as_group_hom k G V g)⁻¹,
  one_smul := λ f, by {ext, simp only [map_one, units.coe_one, one_inv, coe_comp, function.comp_app,
                      one_apply]},
  mul_smul := λ g h f, by {ext, simp},
  smul_add := λ g f₁ f₂, by simp only [add_comp, comp_add],
  smul_zero := λ g, by simp only [linear_map.zero_comp, linear_map.comp_zero]}

@[simp]
lemma linear_hom_smul_def (g : G) (f : V →ₗ[k] W) :
  g • f = ↑(as_group_hom k G W g) ∘ₗ f ∘ₗ ↑(as_group_hom k G V g)⁻¹ := rfl

instance linear_hom_smul_comm_class : smul_comm_class G k (V →ₗ[k] W) :=
{smul_comm := λ g r f, by {ext, simp only [linear_hom_smul_def, coe_comp, function.comp_app,
                          smul_apply, map_smulₛₗ, ring_hom.id_apply]}}

instance dual_distrib_mul_action : distrib_mul_action G (module.dual k V)  :=
{ smul := λ g f, f ∘ₗ ↑(as_group_hom k G V g)⁻¹,
  one_smul := λ f, by {ext, simp only [map_one, one_inv, units.coe_one, coe_comp, function.comp_app,
                      one_apply]},
  mul_smul := λ g h f, by {ext, simp only [map_mul, mul_inv_rev, units.coe_mul, coe_comp,
                          function.comp_app, linear_map.mul_apply]},
  smul_add := λ g f₁ f₂, by simp only [add_comp],
  smul_zero := λ g, by simp only [zero_comp]}

@[simp]
lemma dual_smul_def (g : G) (f : module.dual k V) : g • f = f ∘ₗ ↑(as_group_hom k G V g)⁻¹ := rfl

instance dual_smul_comm_class : smul_comm_class G k (module.dual k V) :=
{smul_comm := λ g r f, by {ext, simp only [dual_smul_def, coe_comp, function.comp_app, smul_apply]}}

end linear_hom

section tensor

open_locale tensor_product

variables (k G V W : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V] [add_comm_monoid W]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]
variables [module k W] [distrib_mul_action G W] [smul_comm_class G k W]

/--
Given two `k`-linear representations `V` and `W`, their tensor product over `k` is itself a
representation, characterized by `g • (v ⊗ₜ w) = (g • v) ⊗ₜ (g • w)` for `g : G`, `v : V`, `w : W`.
-/
@[derive [add_comm_monoid, module k, inhabited]]
def tensor_rep : Type* := (V ⊗[k] W)

notation V ` ⊗[` k `,` G `] ` W := tensor_rep k V W

variables {k G V W}

/--
The tensor product representation `V ⊗[k,G] W` is equivalent to `V ⊗[k] W` as a `k`-module
-/
def of_tensor_rep : (V ⊗[k,G] W) ≃ₗ[k] (V ⊗[k] W) :=
  ⟨id, λ _ _, rfl, λ _ _, rfl, id, λ _, rfl, λ _, rfl⟩

/--
The tensor product representation `V ⊗[k,G] W` is equivalent to `V ⊗[k] W` as a `k`-module
-/
def to_tensor_rep : (V ⊗[k] W) ≃ₗ[k] (V ⊗[k,G] W) := (of_tensor_rep).symm

@[simp]
lemma to_tensor_rep_of_tensor_rep (x : V ⊗[k,G] W) : to_tensor_rep (of_tensor_rep x) = x := rfl

@[simp]
lemma of_tensor_rep_to_tensor_rep (x : V ⊗[k] W) : of_tensor_rep (to_tensor_rep x) = x := rfl

notation v ` ⊗ₜ[` k `,` G `] ` w := to_tensor_rep (v ⊗ₜ[k] w)

instance tensor_rep_distrib_mul_action : distrib_mul_action G (V ⊗[k,G] W) :=
{ smul := λ g, tensor_product.map
          (to_module_End k V g) (to_module_End k W g),
  one_smul := λ x, by simp only [monoid_hom.map_one, tensor_product.map_one, one_apply],
  mul_smul := λ g h x, by simp [monoid_hom.map_mul, mul_eq_comp, tensor_product.map_comp],
  smul_add := λ g x₁ x₂, by simp only [map_add],
  smul_zero := λ g, by simp only [map_zero]}

@[simp]
lemma tensor_rep_def (g : G) (x : V ⊗[k,G] W) :
  g • x = to_tensor_rep (tensor_product.map
    (to_module_End k V g) (to_module_End k W g) (of_tensor_rep x)) := rfl

instance tensor_rep_smul_comm_class : smul_comm_class G k (V ⊗[k,G] W) :=
{smul_comm := λ g r x, by simp}

@[simp]
lemma tensor_rep_to_linear_map (g : G) : to_linear_map k (V ⊗[k,G] W) g =
  to_tensor_rep.to_linear_map ∘ₗ (tensor_product.map (to_linear_map k V g) (to_linear_map k W g)) ∘ₗ
  (of_tensor_rep.to_linear_map) :=
by {ext, simp}

@[simp]
lemma tensor_rep_to_module_End (g : G) : to_module_End k (V ⊗[k,G] W) g =
  to_tensor_rep.to_linear_map ∘ₗ (tensor_product.map (to_linear_map k V g) (to_linear_map k W g)) ∘ₗ
  (of_tensor_rep.to_linear_map) :=
by simp only [to_module_End_apply, tensor_rep_to_linear_map]

end tensor

section tensor_rep_group

open_locale tensor_product

variables (k G V W : Type*) [field k] [group G] [add_comm_group V] [add_comm_group W]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]
variables [module k W] [distrib_mul_action G W] [smul_comm_class G k W]

instance add_comm_group_tensor_rep : add_comm_group (V ⊗[k,G] W) := tensor_product.add_comm_group

end tensor_rep_group

end representation
