/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.hom.equiv.basic
import algebra.hom.units

/-!
# Multiplicative and additive equivalence acting on units.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {F α β A B M N P Q G H : Type*}

/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def to_units [group G] : G ≃* Gˣ :=
{ to_fun := λ x, ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩,
  inv_fun := coe,
  left_inv := λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

@[simp, to_additive] lemma coe_to_units [group G] (g : G) :
  (to_units g : G) = g := rfl

namespace units

variables [monoid M] [monoid N] [monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
{ inv_fun := map h.symm.to_monoid_hom,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  .. map h.to_monoid_hom }

@[simp]
lemma map_equiv_symm (h : M ≃* N) : (map_equiv h).symm = map_equiv h.symm :=
rfl

@[simp]
lemma coe_map_equiv (h : M ≃* N) (x : Mˣ) : (map_equiv h x : N) = h x :=
rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps apply {fully_applied := ff}]
def mul_left (u : Mˣ) : equiv.perm M :=
{ to_fun    := λx, u * x,
  inv_fun   := λx, ↑u⁻¹ * x,
  left_inv  := u.inv_mul_cancel_left,
  right_inv := u.mul_inv_cancel_left }

@[simp, to_additive]
lemma mul_left_symm (u : Mˣ) : u.mul_left.symm = u⁻¹.mul_left :=
equiv.ext $ λ x, rfl

@[to_additive]
lemma mul_left_bijective (a : Mˣ) : function.bijective ((*) a : M → M) :=
(mul_left a).bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps apply {fully_applied := ff}]
def mul_right (u : Mˣ) : equiv.perm M :=
{ to_fun    := λx, x * u,
  inv_fun   := λx, x * ↑u⁻¹,
  left_inv  := λ x, mul_inv_cancel_right x u,
  right_inv := λ x, inv_mul_cancel_right x u }

@[simp, to_additive]
lemma mul_right_symm (u : Mˣ) : u.mul_right.symm = u⁻¹.mul_right :=
equiv.ext $ λ x, rfl

@[to_additive]
lemma mul_right_bijective (a : Mˣ) : function.bijective ((* a) : M → M) :=
(mul_right a).bijective

end units

namespace equiv

section group
variables [group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mul_left (a : G) : perm G := (to_units a).mul_left

@[simp, to_additive]
lemma coe_mul_left (a : G) : ⇑(equiv.mul_left a) = (*) a := rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
lemma mul_left_symm_apply (a : G) : ((equiv.mul_left a).symm : G → G) = (*) a⁻¹ := rfl

@[simp, to_additive]
lemma mul_left_symm (a : G) : (equiv.mul_left a).symm = equiv.mul_left a⁻¹ :=
ext $ λ x, rfl

@[to_additive]
lemma _root_.group.mul_left_bijective (a : G) : function.bijective ((*) a) :=
(equiv.mul_left a).bijective

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mul_right (a : G) : perm G := (to_units a).mul_right

@[simp, to_additive]
lemma coe_mul_right (a : G) : ⇑(equiv.mul_right a) = λ x, x * a := rfl

@[simp, to_additive]
lemma mul_right_symm (a : G) : (equiv.mul_right a).symm = equiv.mul_right a⁻¹ :=
ext $ λ x, rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
lemma mul_right_symm_apply (a : G) : ((equiv.mul_right a).symm : G → G) = λ x, x * a⁻¹ := rfl

@[to_additive]
lemma _root_.group.mul_right_bijective (a : G) : function.bijective (* a) :=
(equiv.mul_right a).bijective

/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive /-" A version of `equiv.add_left a (-b)` that is defeq to `a - b`. "-/, simps]
protected def div_left (a : G) : G ≃ G :=
{ to_fun := λ b, a / b,
  inv_fun := λ b, b⁻¹ * a,
  left_inv := λ b, by simp [div_eq_mul_inv],
  right_inv := λ b, by simp [div_eq_mul_inv] }

@[to_additive]
lemma div_left_eq_inv_trans_mul_left (a : G) :
  equiv.div_left a = (equiv.inv G).trans (equiv.mul_left a) :=
ext $ λ _, div_eq_mul_inv _ _

/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive /-" A version of `equiv.add_right (-a) b` that is defeq to `b - a`. "-/, simps]
protected def div_right (a : G) : G ≃ G :=
{ to_fun := λ b, b / a,
  inv_fun := λ b, b * a,
  left_inv := λ b, by simp [div_eq_mul_inv],
  right_inv := λ b, by simp [div_eq_mul_inv] }

@[to_additive]
lemma div_right_eq_mul_right_inv (a : G) : equiv.div_right a = equiv.mul_right a⁻¹ :=
ext $ λ _, div_eq_mul_inv _ _

end group

end equiv

/-- In a `division_comm_monoid`, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`.", simps apply]
def mul_equiv.inv (G : Type*) [division_comm_monoid G] : G ≃* G :=
{ to_fun   := has_inv.inv,
  inv_fun  := has_inv.inv,
  map_mul' := mul_inv,
  ..equiv.inv G }

@[simp] lemma mul_equiv.inv_symm (G : Type*) [division_comm_monoid G] :
  (mul_equiv.inv G).symm = mul_equiv.inv G := rfl
