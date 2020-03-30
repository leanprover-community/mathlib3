/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.equiv.basic algebra.field

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

## Tags

equiv, group, ring, field
-/

universes u v
variables {α : Type u} {β : Type v}

namespace equiv


section instances

variables (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[to_additive "Transfer `has_zero` across an `equiv`"]
protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
@[to_additive] lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

/-- Transfer `has_mul` across an `equiv` -/
@[to_additive "Transfer `has_add` across an `equiv`"]
protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
@[to_additive] lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

/-- Transfer `has_inv` across an `equiv` -/
@[to_additive "Transfer `has_neg` across an `equiv`"]
protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
@[to_additive] lemma inv_def [has_inv β] (x : α) :
  @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

/-- Transfer `semigroup` across an `equiv` -/
@[to_additive add_semigroup  "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

/-- Transfer `comm_semigroup` across an `equiv` -/
@[to_additive add_comm_semigroup "Transfer `add_comm_semigroup` across an `equiv`"]
protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

/-- Transfer `monoid` across an `equiv` -/
@[to_additive add_monoid "Transfer `add_monoid` across an `equiv`"]
protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

/-- Transfer `comm_monoid` across an `equiv` -/
@[to_additive add_comm_monoid "Transfer `add_comm_monoid` across an `equiv`"]
protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

/-- Transfer `group` across an `equiv` -/
@[to_additive add_group "Transfer `add_group` across an `equiv`"]
protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

/-- Transfer `comm_group` across an `equiv` -/
@[to_additive add_comm_group "Transfer `add_comm_group` across an `equiv`"]
protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

/-- Transfer `semiring` across an `equiv` -/
protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

/-- Transfer `comm_semiring` across an `equiv` -/
protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

/-- Transfer `ring` across an `equiv` -/
protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

/-- Transfer `comm_ring` across an `equiv` -/
protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

/-- Transfer `zero_ne_one_class` across an `equiv` -/
protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

/-- Transfer `nonzero_comm_ring` across an `equiv` -/
protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

/-- Transfer `domain` across an `equiv` -/
protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

/-- Transfer `integral_domain` across an `equiv` -/
protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

/-- Transfer `division_ring` across an `equiv` -/
protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  inv_zero := by simp [zero_def, inv_def],
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

/-- Transfer `field` across an `equiv` -/
protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

end instances
end equiv
