/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.module.basic

/-!
# Instances on punit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

universes u

namespace punit
variables (x y : punit.{u+1}) (s : set punit.{u+1})

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

instance : comm_ring punit :=
by refine
{ .. punit.comm_group,
  .. punit.add_comm_group,
  .. };
intros; exact subsingleton.elim _ _

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

instance (R : Type u) [semiring R] : module R punit := module.of_core $
by refine
{ smul := λ _ _, star,
  .. punit.comm_ring, .. };
intros; exact subsingleton.elim _ _

@[simp] lemma zero_eq : (0 : punit) = star := rfl
@[simp, to_additive] lemma one_eq : (1 : punit) = star := rfl
@[simp] lemma add_eq : x + y = star := rfl
@[simp, to_additive] lemma mul_eq : x * y = star := rfl
@[simp, to_additive] lemma div_eq : x / y = star := rfl
@[simp] lemma neg_eq : -x = star := rfl
@[simp, to_additive] lemma inv_eq : x⁻¹ = star := rfl
lemma smul_eq : x • y = star := rfl
@[simp] lemma top_eq : (⊤ : punit) = star := rfl
@[simp] lemma bot_eq : (⊥ : punit) = star := rfl
@[simp] lemma sup_eq : x ⊔ y = star := rfl
@[simp] lemma inf_eq : x ⊓ y = star := rfl
@[simp] lemma Sup_eq : Sup s = star := rfl
@[simp] lemma Inf_eq : Inf s = star := rfl
@[simp] protected lemma le : x ≤ y := trivial
@[simp] lemma not_lt : ¬(x < y) := not_false

end punit
