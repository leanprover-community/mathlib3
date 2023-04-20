/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser, Joachim Breitner
-/
import group_theory.free_group
/-!
# Free groups structures on arbitrary types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a type class for type that are free groups, together with the usual operations.
The type class can be instantiated by providing an isomorphim to the canonical free group, or by
proving that the universal property holds.

For the explicit construction of free groups, see `group_theory/free_group`.

## Main definitions

* `is_free_group G` - a typeclass to indicate that `G` is free over some generators
* `is_free_group.of` - the canonical injection of `G`'s generators into `G`
* `is_free_group.lift` - the universal property of the free group

## Main results

* `is_free_group.to_free_group` - any free group with generators `A` is equivalent to
  `free_group A`.
* `is_free_group.unique_lift` - the universal property of a free group
* `is_free_group.of_unique_lift` - constructing `is_free_group` from the universal property

-/

universes u

/-- `is_free_group G` means that `G` isomorphic to a free group. -/
class is_free_group (G : Type u) [group G] :=
(generators : Type u)
(mul_equiv [] : free_group generators ≃* G)

instance (X : Type*) : is_free_group (free_group X) :=
{ generators := X,
  mul_equiv := mul_equiv.refl _ }

namespace is_free_group

variables (G : Type*) [group G] [is_free_group G]

/-- Any free group is isomorphic to "the" free group. -/
@[simps] def to_free_group : G ≃* free_group (generators G) := (mul_equiv G).symm

variable {G}

/-- The canonical injection of G's generators into G -/
def of : generators G → G := (mul_equiv G).to_fun ∘ free_group.of

@[simp] lemma of_eq_free_group_of {A : Type u} : (@of (free_group A) _ _ ) = free_group.of := rfl

variables {H : Type*} [group H]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
def lift : (generators G → H) ≃ (G →* H) :=
free_group.lift.trans
  { to_fun := λ f, f.comp (mul_equiv G).symm.to_monoid_hom,
    inv_fun := λ f, f.comp (mul_equiv G).to_monoid_hom,
    left_inv := λ f, by { ext, simp, },
    right_inv := λ f, by { ext, simp, }, }

@[simp] lemma lift'_eq_free_group_lift {A : Type u} :
  (@lift (free_group A) _ _ H _) = free_group.lift := rfl

@[simp] lemma lift_of (f : generators G → H) (a : generators G) : lift f (of a) = f a :=
congr_fun (lift.symm_apply_apply f) a

@[simp] lemma lift_symm_apply (f : G →* H) (a : generators G) : (lift.symm f) a = f (of a) :=
rfl

@[ext] lemma ext_hom ⦃f g : G →* H⦄ (h : ∀ (a : generators G), f (of a) = g (of a)) : f = g :=
lift.symm.injective (funext h)

/-- The universal property of a free group: A functions from the generators of `G` to another
group extends in a unique way to a homomorphism from `G`.

Note that since `is_free_group.lift` is expressed as a bijection, it already
expresses the universal property.  -/
lemma unique_lift (f : generators G → H) : ∃! F : G →* H, ∀ a, F (of a) = f a :=
by simpa only [function.funext_iff] using lift.symm.bijective.exists_unique f

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `is_free_group.lift` and its properties. -/
def of_lift {G : Type u} [group G] (X : Type u)
  (of : X → G)
  (lift : ∀ {H : Type u} [group H], by exactI (X → H) ≃ (G →* H))
  (lift_of : ∀ {H : Type u} [group H], by exactI ∀ (f : X → H) a, lift f (of a) = f a) :
  is_free_group G :=
{ generators := X,
  mul_equiv := monoid_hom.to_mul_equiv
    (free_group.lift of)
    (lift free_group.of)
    begin
      apply free_group.ext_hom, intro x,
      simp only [monoid_hom.coe_comp, function.comp_app, monoid_hom.id_apply, free_group.lift.of,
        lift_of],
    end
    begin
      let lift_symm_of : ∀ {H : Type u} [group H], by exactI ∀ (f : G →* H) a,
        lift.symm f a = f (of a) := by introsI H _ f a; simp [← lift_of (lift.symm f)],
      apply lift.symm.injective, ext x,
      simp only [monoid_hom.coe_comp, function.comp_app, monoid_hom.id_apply,
        free_group.lift.of, lift_of, lift_symm_of],
    end }

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `is_free_group.unique_lift`.  -/
noncomputable
def of_unique_lift {G : Type u} [group G] (X : Type u)
  (of : X → G)
  (h : ∀ {H : Type u} [group H] (f : X → H), by exactI ∃! F : G →* H, ∀ a, F (of a) = f a) :
  is_free_group G :=
let lift {H : Type u} [group H] : by exactI (X → H) ≃ (G →* H) := by exactI
  { to_fun := λ f, classical.some (h f),
    inv_fun := λ F, F ∘ of,
    left_inv := λ f, funext (classical.some_spec (h f)).left,
    right_inv := λ F, ((classical.some_spec (h (F ∘ of))).right F (λ _, rfl)).symm } in
let lift_of {H : Type u} [group H] (f : X → H) (a : X) : by exactI lift f (of a) = f a :=
  by exactI congr_fun (lift.symm_apply_apply f) a in
of_lift X of @lift @lift_of

/-- Being a free group transports across group isomorphisms. -/
def of_mul_equiv {H : Type*} [group H] (h : G ≃* H) : is_free_group H :=
{ generators := generators G, mul_equiv := (mul_equiv G).trans h }

end is_free_group
