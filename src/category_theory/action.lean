/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import category_theory.elements
import category_theory.single_obj

/-!
# Actions as functors and as categories

From a multiplicative action M ↻ X, we can construct a functor from M to the category of
types, mapping the single object of M to X and an element `m : M` to map `X → X` given by
multiplication by `m`.
  This functor induces a category structure on X -- a special case of the category of elements.
A morphism `x ⟶ y` in this category is simply a scalar `m : M` such that `m • x = y`. In the case
where M is a group, this category is a groupoid -- the `action groupoid'.
-/

open mul_action
namespace category_theory

universes u

variables (M : Type*) [monoid M] (X : Type u) [mul_action M X]

/-- A multiplicative action M ↻ X viewed as a functor mapping the single object of M to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`. -/
@[simps]
def action_as_functor : single_obj M ⥤ Type u :=
{ obj := λ _, X,
  map := λ _ _, (•),
  map_id' := λ _, funext $ mul_action.one_smul,
  map_comp' := λ _ _ _ f g, funext $ λ x, (smul_smul g f x).symm }

/-- A multiplicative action M ↻ X induces a category strucure on X, where a morphism
 from x to y is a scalar taking x to y. Due to implementation details, the object type
 of this category is not equal to X, but is in bijection with X. -/
@[derive category]
def action_category := (action_as_functor M X).elements

namespace action_category

instance (G : Type*) [group G] [mul_action G X] : groupoid (action_category G X) :=
category_theory.groupoid_of_elements _

/-- The projection from the action category to the monoid, mapping a morphism to its
  label. -/
def π : action_category M X ⥤ single_obj M :=
category_of_elements.π _

@[simp]
lemma π_map (p q : action_category M X) (f : p ⟶ q) : (π M X).map f = f.val := rfl

@[simp]
lemma π_obj (p : action_category M X) : (π M X).obj p = single_obj.star M :=
@subsingleton.elim unit _ _ _

/-- An object of the action category given by M ↻ X corresponds to an element of X. -/
def obj_equiv : X ≃ action_category M X :=
{ to_fun := λ x, ⟨single_obj.star M, x⟩,
  inv_fun := λ p, p.2,
  left_inv := by tidy,
  right_inv := by tidy }

lemma hom_as_subtype (p q : action_category M X) :
  (p ⟶ q) = { m : M // m • (obj_equiv M X).symm p = (obj_equiv M X).symm q } := rfl

instance [inhabited X] : inhabited (action_category M X) :=
{ default := obj_equiv M X (default X) }

variables {X} (x : X)
/-- The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent. -/
def stabilizer_iso_End : stabilizer M x ≃* End (obj_equiv M X x) :=
mul_equiv.refl _

@[simp]
lemma stabilizer_iso_End_apply (f : stabilizer M x) :
  (stabilizer_iso_End M x).to_fun f = f := rfl

@[simp]
lemma stabilizer_iso_End_symm_apply (f : End _) :
  (stabilizer_iso_End M x).inv_fun f = f := rfl

end action_category
end category_theory
