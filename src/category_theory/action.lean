/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/

import category_theory.groupoid
import category_theory.endomorphism
import group_theory.group_action
import category_theory.single_obj

/-!
# The action category and the action groupoid.

Defines the action category associated with a multiplicative action
and the action groupoid associated with a group action.
-/

open mul_action
namespace category_theory

variables (M : Type*) [monoid M] (X : Type*) [𝒜 : mul_action M X] (x : X)
include 𝒜

/-- A multiplicative action of `M` on `X` induces a category structure on `X` where
  a morphism `x ⟶ y` is a scalar `m : M` such that `m • x = y`. To prevent conflicts,
  the object type of this category is an inductive type wrapping `X`. -/
structure action_category := (as : X)

namespace action_category

instance [inhabited X] : inhabited (action_category M X) := ⟨{as := default X}⟩

@[simps]
instance : category (action_category M X) :=
{ hom := λ x y, {m : M // m • x.as = y.as },
  id := λ x, ⟨1, mul_action.one_smul _ x.as⟩,
  comp := λ x y z f g, ⟨g.val * f.val, by rw [←smul_smul, f.2, g.2] ⟩,
  assoc' := λ x y z w f g h, by simp only [mul_assoc] }

/-- The functor from the action category to the single object category,
  mapping a morphism to its label. -/
def projection : action_category M X ⥤ single_obj M :=
{ obj := λ _, single_obj.star M,
  map := λ _ _ f, f.val }

instance : faithful (projection M X) := by obviously

/-- The stabilizer of a point is isomorphic to the Endomorphism monoid at
  the corresponding point. In fact they are defeq. -/
def stabilizer_iso_End : stabilizer M x ≃* End ({as := x} : action_category M X) :=
mul_equiv.refl _

omit 𝒜
variables (G : Type*) [group G] [mul_action G X]

/-- The action category associated with a group action is a groupoid. -/
@[simps]
instance : groupoid (action_category G X) :=
{ inv := λ x y f, ⟨f.val⁻¹, calc f.val⁻¹ • y.as = f.val⁻¹ • f.val • x.as : by rw f.2
                                            ... = x.as : by {rw smul_smul, simp} ⟩,
  inv_comp' := by { intros, rw subtype.ext, simp, },
  comp_inv' := by { intros, rw subtype.ext, simp, } }

end action_category
end category_theory
