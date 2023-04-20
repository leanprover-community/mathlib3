/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.module.basic
import algebra.gcd_monoid.basic
import algebra.group_ring_action.basic
import group_theory.group_action.defs
import order.complete_boolean_algebra

/-!
# Instances on punit

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

universes u

namespace punit
variables {R S : Type*} (x y : punit.{u+1}) (s : set punit.{u+1})

@[to_additive]
instance : comm_group punit :=
by refine_struct
{ mul := λ _ _, star,
  one := star,
  inv := λ _, star,
  div := λ _ _, star,
  npow := λ _ _, star,
  zpow := λ _ _, star,
  .. };
intros; exact subsingleton.elim _ _

@[simp, to_additive] lemma one_eq : (1 : punit) = star := rfl
@[simp, to_additive] lemma mul_eq : x * y = star := rfl
-- `sub_eq` simplifies `punit.sub_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive] lemma div_eq : x / y = star := rfl
-- `neg_eq` simplifies `punit.neg_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive] lemma inv_eq : x⁻¹ = star := rfl

instance : comm_ring punit :=
by refine
{ nat_cast := λ _, punit.star,
  .. punit.comm_group,
  .. punit.add_comm_group,
  .. };
intros; exact subsingleton.elim _ _

instance : cancel_comm_monoid_with_zero punit :=
by refine
{ .. punit.comm_ring,
  .. };
intros; exact subsingleton.elim _ _

instance : normalized_gcd_monoid punit :=
by refine
{ gcd := λ _ _, star,
  lcm := λ _ _, star,
  norm_unit := λ x, 1,
  gcd_dvd_left := λ _ _, ⟨star, subsingleton.elim _ _⟩,
  gcd_dvd_right := λ _ _, ⟨star, subsingleton.elim _ _⟩,
  dvd_gcd := λ _ _ _ _ _, ⟨star, subsingleton.elim _ _⟩,
  gcd_mul_lcm := λ _ _, ⟨1, subsingleton.elim _ _⟩,
  .. };
intros; exact subsingleton.elim _ _

@[simp] lemma gcd_eq : gcd x y = star := rfl
@[simp] lemma lcm_eq : lcm x y = star := rfl
@[simp] lemma norm_unit_eq : norm_unit x = 1 := rfl

instance : canonically_ordered_add_monoid punit :=
by refine
{ exists_add_of_le := λ _ _ _, ⟨star, subsingleton.elim _ _⟩,
  .. punit.comm_ring, .. punit.complete_boolean_algebra, .. };
intros; trivial

instance : linear_ordered_cancel_add_comm_monoid punit :=
{ le_of_add_le_add_left := λ _ _ _ _, trivial,
  .. punit.canonically_ordered_add_monoid, ..punit.linear_order }

instance : linear_ordered_add_comm_monoid_with_top punit :=
{ top_add' := λ _, rfl,
  ..punit.complete_boolean_algebra,
  ..punit.linear_ordered_cancel_add_comm_monoid }

@[to_additive] instance : has_smul R punit := ⟨λ _ _, star⟩

@[simp, to_additive] lemma smul_eq (r : R) : r • y = star := rfl

@[to_additive] instance : is_central_scalar R punit := ⟨λ _ _, rfl⟩
@[to_additive] instance : smul_comm_class R S punit := ⟨λ _ _ _, rfl⟩
@[to_additive] instance [has_smul R S] : is_scalar_tower R S punit := ⟨λ _ _ _, rfl⟩

instance [has_zero R] : smul_with_zero R punit :=
by refine { ..punit.has_smul, .. };
intros; exact subsingleton.elim _ _

instance [monoid R] : mul_action R punit :=
by refine { ..punit.has_smul, .. };
intros; exact subsingleton.elim _ _

instance [monoid R] : distrib_mul_action R punit :=
by refine { ..punit.mul_action, .. };
intros; exact subsingleton.elim _ _

instance [monoid R] : mul_distrib_mul_action R punit :=
by refine { ..punit.mul_action, .. };
intros; exact subsingleton.elim _ _

instance [semiring R] : mul_semiring_action R punit :=
{ ..punit.distrib_mul_action, ..punit.mul_distrib_mul_action }

instance [monoid_with_zero R] : mul_action_with_zero R punit :=
{ .. punit.mul_action, .. punit.smul_with_zero }

instance [semiring R] : module R punit :=
by refine { .. punit.distrib_mul_action, .. };
intros; exact subsingleton.elim _ _

end punit
