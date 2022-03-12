/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.module.basic
import algebra.gcd_monoid.basic
import algebra.group_ring_action
import group_theory.group_action.defs

/-!
# Instances on punit

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
@[simp, to_additive] lemma div_eq : x / y = star := rfl
@[simp, to_additive] lemma inv_eq : x⁻¹ = star := rfl

instance : comm_ring punit :=
by refine
{ .. punit.comm_group,
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

instance : complete_boolean_algebra punit :=
by refine
{ le := λ _ _, true,
  le_antisymm := λ _ _ _ _, subsingleton.elim _ _,
  lt := λ _ _, false,
  lt_iff_le_not_le := λ _ _, iff_of_false not_false (λ H, H.2 trivial),
  top := star,
  bot := star,
  sup := λ _ _, star,
  inf := λ _ _, star,
  Sup := λ _, star,
  Inf := λ _, star,
  compl := λ _, star,
  sdiff := λ _ _, star,
  .. };
intros; trivial <|> simp only [eq_iff_true_of_subsingleton]

@[simp] lemma top_eq : (⊤ : punit) = star := rfl
@[simp] lemma bot_eq : (⊥ : punit) = star := rfl
@[simp] lemma sup_eq : x ⊔ y = star := rfl
@[simp] lemma inf_eq : x ⊓ y = star := rfl
@[simp] lemma Sup_eq : Sup s = star := rfl
@[simp] lemma Inf_eq : Inf s = star := rfl
@[simp] lemma compl_eq : xᶜ = star := rfl
@[simp] lemma sdiff_eq : x \ y = star := rfl
@[simp] protected lemma le : x ≤ y := trivial
@[simp] lemma not_lt : ¬(x < y) := not_false

instance : canonically_ordered_add_monoid punit :=
by refine
{ le_iff_exists_add := λ _ _, iff_of_true _ ⟨star, subsingleton.elim _ _⟩,
  .. punit.comm_ring, .. punit.complete_boolean_algebra, .. };
intros; trivial

instance : linear_ordered_cancel_add_comm_monoid punit :=
{ add_left_cancel := λ _ _ _ _, subsingleton.elim _ _,
  le_of_add_le_add_left := λ _ _ _ _, trivial,
  le_total := λ _ _, or.inl trivial,
  decidable_le := λ _ _, decidable.true,
  decidable_eq := punit.decidable_eq,
  decidable_lt := λ _ _, decidable.false,
  .. punit.canonically_ordered_add_monoid }

instance : has_scalar R punit :=
{ smul := λ _ _, star }

@[simp] lemma smul_eq (r : R) : r • y = star := rfl

instance : is_central_scalar R punit := ⟨λ _ _, rfl⟩

instance : smul_comm_class R S punit := ⟨λ _ _ _, subsingleton.elim _ _⟩

instance [has_scalar R S] : is_scalar_tower R S punit := ⟨λ _ _ _, subsingleton.elim _ _⟩

instance [has_zero R] : smul_with_zero R punit :=
by refine { ..punit.has_scalar, .. };
intros; exact subsingleton.elim _ _

instance [monoid R] : mul_action R punit :=
by refine { ..punit.has_scalar, .. };
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
