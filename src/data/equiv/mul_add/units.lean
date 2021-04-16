/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import data.equiv.mul_add.basic

/-!
# Multiplicative and additive equivs on units and groups

In this file we define some `add_equiv`s and `mul_equiv`s that apply to units and groups.
-/

/-- A group is isomorphic to its group of units. -/
@[to_additive to_add_units "An additive group is isomorphic to its group of additive units"]
def to_units {G} [group G] : G ≃* units G :=
{ to_fun := λ x, ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩,
  inv_fun := coe,
  left_inv := λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

protected lemma group.is_unit {G} [group G] (x : G) : is_unit x := (to_units x).is_unit

namespace units

variables [monoid M] [monoid N] [monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv (h : M ≃* N) : units M ≃* units N :=
{ inv_fun := map h.symm.to_monoid_hom,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  .. map h.to_monoid_hom }

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type."]
def mul_left (u : units M) : equiv.perm M :=
{ to_fun    := λx, u * x,
  inv_fun   := λx, ↑u⁻¹ * x,
  left_inv  := u.inv_mul_cancel_left,
  right_inv := u.mul_inv_cancel_left }

@[simp, to_additive]
lemma coe_mul_left (u : units M) : ⇑u.mul_left = (*) u := rfl

@[simp, to_additive]
lemma mul_left_symm (u : units M) : u.mul_left.symm = u⁻¹.mul_left :=
equiv.ext $ λ x, rfl

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type."]
def mul_right (u : units M) : equiv.perm M :=
{ to_fun    := λx, x * u,
  inv_fun   := λx, x * ↑u⁻¹,
  left_inv  := λ x, mul_inv_cancel_right x u,
  right_inv := λ x, inv_mul_cancel_right x u }

@[simp, to_additive]
lemma coe_mul_right (u : units M) : ⇑u.mul_right = λ x : M, x * u := rfl

@[simp, to_additive]
lemma mul_right_symm (u : units M) : u.mul_right.symm = u⁻¹.mul_right :=
equiv.ext $ λ x, rfl

end units

namespace equiv

section group
variables [group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mul_left (a : G) : perm G := (to_units a).mul_left

@[simp, to_additive]
lemma coe_mul_left (a : G) : ⇑(equiv.mul_left a) = (*) a := rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive]
lemma mul_left_symm_apply (a : G) : ((equiv.mul_left a).symm : G → G) = (*) a⁻¹ := rfl

@[simp, to_additive]
lemma mul_left_symm (a : G) : (equiv.mul_left a).symm = equiv.mul_left a⁻¹ :=
ext $ λ x, rfl

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mul_right (a : G) : perm G := (to_units a).mul_right

@[simp, to_additive]
lemma coe_mul_right (a : G) : ⇑(equiv.mul_right a) = λ x, x * a := rfl

@[simp, to_additive]
lemma mul_right_symm (a : G) : (equiv.mul_right a).symm = equiv.mul_right a⁻¹ :=
ext $ λ x, rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this.  -/
@[simp, nolint simp_nf, to_additive]
lemma mul_right_symm_apply (a : G) : ((equiv.mul_right a).symm : G → G) = λ x, x * a⁻¹ := rfl

attribute [nolint simp_nf] add_left_symm_apply add_right_symm_apply

variable (G)

/-- Inversion on a `group` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type."]
protected def inv : perm G :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

variable {G}

@[simp, to_additive]
lemma coe_inv : ⇑(equiv.inv G) = has_inv.inv := rfl

@[simp, to_additive]
lemma inv_symm : (equiv.inv G).symm = equiv.inv G := rfl

end group

section group_with_zero
variables [group_with_zero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
protected def mul_left' (a : G) (ha : a ≠ 0) : perm G :=
{ to_fun := λ x, a * x,
  inv_fun := λ x, a⁻¹ * x,
  left_inv := λ x, by { dsimp, rw [← mul_assoc, inv_mul_cancel ha, one_mul] },
  right_inv := λ x, by { dsimp, rw [← mul_assoc, mul_inv_cancel ha, one_mul] } }

@[simp] lemma coe_mul_left' (a : G) (ha : a ≠ 0) : ⇑(equiv.mul_left' a ha) = (*) a := rfl

@[simp] lemma mul_left'_symm_apply (a : G) (ha : a ≠ 0) :
  ((equiv.mul_left' a ha).symm : G → G) = (*) a⁻¹ := rfl

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
protected def mul_right' (a : G) (ha : a ≠ 0) : perm G :=
{ to_fun := λ x, x * a,
  inv_fun := λ x, x * a⁻¹,
  left_inv := λ x, by { dsimp, rw [mul_assoc, mul_inv_cancel ha, mul_one] },
  right_inv := λ x, by { dsimp, rw [mul_assoc, inv_mul_cancel ha, mul_one] } }

@[simp] lemma coe_mul_right' (a : G) (ha : a ≠ 0) : ⇑(equiv.mul_right' a ha) = λ x, x * a := rfl

@[simp] lemma mul_right'_symm_apply (a : G) (ha : a ≠ 0) :
  ((equiv.mul_right' a ha).symm : G → G) = λ x, x * a⁻¹ := rfl

end group_with_zero
