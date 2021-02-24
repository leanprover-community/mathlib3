/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import data.pi
import tactic.pi_instances
import algebra.group.defs
import algebra.group.hom
/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

@[to_additive]
instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance div_inv_monoid [∀ i, div_inv_monoid $ f i] :
  div_inv_monoid (Π i : I, f i) :=
{ div_eq_mul_inv := λ x y, funext (λ i, div_eq_mul_inv (x i) (y i)),
  .. pi.monoid, .. pi.has_div, .. pi.has_inv }

@[to_additive]
instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div, .. };
  tactic.pi_instance_derive_field

@[to_additive]
instance comm_group [∀ i, comm_group $ f i] : comm_group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div, .. };
  tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

instance mul_zero_class [∀ i, mul_zero_class $ f i] :
  mul_zero_class (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance monoid_with_zero [∀ i, monoid_with_zero $ f i] :
  monoid_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*), .. };
  tactic.pi_instance_derive_field

instance comm_monoid_with_zero [∀ i, comm_monoid_with_zero $ f i] :
  comm_monoid_with_zero (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*), .. };
  tactic.pi_instance_derive_field

section instance_lemmas
open function

variables {α β γ : Type*}

@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 := rfl

@[simp, to_additive] lemma comp_one [has_one β] {f : β → γ} : f ∘ 1 = const α (f 1) := rfl

@[simp, to_additive] lemma one_comp [has_one γ] {f : α → β} : (1 : β → γ) ∘ f = 1 := rfl

end instance_lemmas

end pi

section monoid_hom

variables (f) [Π i, monoid (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
@[to_additive "Evaluation of functions into an indexed collection of additive monoids at a point
is an additive monoid homomorphism."]
def monoid_hom.apply (i : I) : (Π i, f i) →* f i :=
{ to_fun := λ g, g i,
  map_one' := rfl,
  map_mul' := λ x y, rfl, }

@[simp, to_additive]
lemma monoid_hom.apply_apply (i : I) (g : Π i, f i) :
  (monoid_hom.apply f i) g = g i := rfl

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[simps, to_additive "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.

See also `add_monoid_hom.eval`. "]
def monoid_hom.coe_fn (α β : Type*) [monoid α] [comm_monoid β] : (α →* β) →* (α → β) :=
{ to_fun := λ g, g,
  map_one' := rfl,
  map_mul' := λ x y, rfl, }

end monoid_hom

section single
variables [decidable_eq I]
open pi

variables (f)

/-- The zero-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `zero_hom` version of `pi.single`. -/
@[simps] def zero_hom.single [Π i, has_zero $ f i] (i : I) : zero_hom (f i) (Π i, f i) :=
{ to_fun := single i,
  map_zero' := function.update_eq_self i 0 }

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point.

This is the `add_monoid_hom` version of `pi.single`. -/
@[simps] def add_monoid_hom.single [Π i, add_monoid $ f i] (i : I) : f i →+ Π i, f i :=
{ to_fun := single i,
  map_add' := λ x y, funext $ λ j, begin
    refine (apply_single₂ _ (λ _, _) i x y j).symm,
    exact zero_add 0,
  end,
  .. (zero_hom.single f i) }

/-- The multiplicative homomorphism including a single `monoid_with_zero`
into a dependent family of monoid_with_zeros, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps] def mul_hom.single [Π i, monoid_with_zero $ f i] (i : I) : mul_hom (f i) (Π i, f i) :=
{ to_fun := single i,
  map_mul' := λ x y, funext $ λ j, begin
    refine (apply_single₂ _ (λ _, _) i x y j).symm,
    exact zero_mul 0,
  end, }

variables {f}

@[simp]
lemma pi.single_zero [Π i, has_zero $ f i] (i : I) :
  single i (0 : f i) = 0 :=
(zero_hom.single f i).map_zero

lemma pi.single_add [Π i, add_monoid $ f i] (i : I) (x y : f i) :
  single i (x + y) = single i x + single i y :=
(add_monoid_hom.single f i).map_add x y

lemma pi.single_neg [Π i, add_group $ f i] (i : I) (x : f i) :
  single i (-x) = -single i x :=
(add_monoid_hom.single f i).map_neg x

lemma pi.single_sub [Π i, add_group $ f i] (i : I) (x y : f i) :
  single i (x - y) = single i x - single i y :=
(add_monoid_hom.single f i).map_sub x y

lemma pi.single_mul_single [Π i, monoid_with_zero $ f i] (i : I) (x y : f i) :
  single i x * single i y = single i (x * y) :=
((mul_hom.single f i).map_mul x y).symm

end single
