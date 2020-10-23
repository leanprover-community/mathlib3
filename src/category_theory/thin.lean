/-
Copyright (c) 2019 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.functor_category
import category_theory.isomorphism

/-!
# Thin categories

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.

Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.

To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.

If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁}

section
variables [category_struct.{v₁} C] [∀ X Y : C, subsingleton (X ⟶ Y)]

/-- Construct a category instance from a category_struct, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
def thin_category : category C := {}.
end

-- We don't assume anything about where the category instance on `C` came from.
-- In particular this allows `C` to be a preorder, with the category instance inherited from the
-- preorder structure.
variables [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variable [∀ X Y : C, subsingleton (X ⟶ Y)]

/-- If `C` is a thin category, then `D ⥤ C` is a thin category. -/
instance functor_thin (F₁ F₂ : D ⥤ C) : subsingleton (F₁ ⟶ F₂) :=
⟨λ α β, nat_trans.ext α β (funext (λ _, subsingleton.elim _ _))⟩

/-- To show `X ≅ Y` in a thin category, it suffices to just give any morphism in each direction. -/
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
{ hom := f, inv := g }

instance subsingleton_iso {X Y : C} : subsingleton (X ≅ Y) :=
⟨by { intros i₁ i₂, ext1, apply subsingleton.elim }⟩

end category_theory
