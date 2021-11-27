/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Junyan Xu
-/
import category_theory.lax_functor
import category_theory.elements


/-!
# The Grothendieck construction for lax functors

Given a lax functor `F` from a 1-category `C` to the 2-category `Cat`,
the objects of `grothendieck F` consist of dependent pairs `(b, f)`,
where `b : C` and `f : F.obj c`, and a morphism `(b, f) ⟶ (b', f')` is a
pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`. The forgetful
functor `grothendieck F ⥤ C` is then a Grothendieck fibration, with base
category `C`, total category `grothendieck F`, and fiber categories
`F.obj b` for `b : C`.

Notice that `F` gives a functor `F.map β` between fiber categories
`F.obj b` and `F.obj b'` for each morphism `β : b ⟶ b'` in `C`, which
we call a component functor. We show that if the lax functor is a
pseudofunctor, the base category and all fiber categories have colimits
and the component functors all preserve colimits, then the total category
also has colimits.

https://ncatlab.org/nlab/show/Grothendieck+construction#limits_and_colimits

In case all component functors have right adjoints, we can transfer the
lax functor structure of `F` across the adjunctions to obtain a lax functor
`G` from `Cᵒᵖ` to `Cat` with component functors opposites (`functor.op`) of
the right adjoints. We show that `grothendieck G` is isomorphic to the
opposite of `grothenieck F`, and we may show that `grothendieck F` has
limits by showing that `grothendieck G` has colimits.

(what about left adjoints?)

This will be used to construct the category `PrimedPreringedSpace` and
to show that `PresheafedSpace`, `SheafedSpace` and `PrimedPreringedSpace` has
(co)limits. Fibrations of categories such as `Top` over `Type`, or `PresheafedSpace` over
`Top` are also examples of this construction, and it may be preferable to
have the existence of (co)limits in `Top` refactored to use results here.

## References

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

See also `category_theory.elements` for the category of elements of functor `F : C ⥤ Type`.

-/

universe u

namespace category_theory

variables {C : Type*} [category.{u} C] (F : lax_functor_to_Cat C)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
@[nolint has_inhabited_instance]
structure grothendieck :=
(base : C)
(fiber : F.obj base)

namespace grothendieck

variables {F}

/--
A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure hom (X Y : grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber : (F.map base).obj X.fiber ⟶ Y.fiber)

@[ext] lemma ext {X Y : grothendieck F} (f g : hom X Y)
  (w_base : f.base = g.base) (w_fiber : eq_to_hom (by rw w_base) ≫ f.fiber = g.fiber) : f = g :=
begin
  cases f; cases g,
  congr,
  dsimp at w_base,
  induction w_base,
  refl,
  dsimp at w_base,
  induction w_base,
  simpa using w_fiber,
end

/--
The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : grothendieck F) : hom X X :=
{ base := 𝟙 X.base,
  fiber := (F.map_id X.base).app X.fiber }

instance (X : grothendieck F) : inhabited (hom X X) := ⟨id X⟩

/--
Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : grothendieck F} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ base := f.base ≫ g.base,
  fiber := (F.map_comp f.base g.base).app X.fiber ≫ (F.map g.base).map f.fiber ≫ g.fiber }

instance : category (grothendieck F) :=
{ hom := λ X Y, grothendieck.hom X Y,
  id := λ X, grothendieck.id X,
  comp := λ X Y Z f g, grothendieck.comp f g }
/- id_comp, comp_id, assoc can all be proven by { ext, { dsimp, simp }, simp } -/

@[simp] lemma id_fiber' (X : grothendieck F) :
  hom.fiber (𝟙 X) = (F.map_id X.base).app X.fiber := id_fiber X

lemma congr {X Y : grothendieck F} {f g : X ⟶ Y} (h : f = g) :
  f.fiber = eq_to_hom (by rw h) ≫ g.fiber := by { subst h, simp }

section
variables (F)

/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : grothendieck F ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.1 }

end

universe w
variables (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_functor : grothendieck (G ⋙ Type_to_Cat).to_lax ⥤ G.elements :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, f.2.1.1⟩ }

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieck_Type_to_Cat_inverse : G.elements ⥤ grothendieck (G ⋙ Type_to_Cat).to_lax :=
{ obj := λ X, ⟨X.1, X.2⟩,
  map := λ X Y f, ⟨f.1, ⟨⟨f.2⟩⟩⟩ }

/--
The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps]
def grothendieck_Type_to_Cat : grothendieck (G ⋙ Type_to_Cat).to_lax ≌ G.elements :=
{ functor := grothendieck_Type_to_Cat_functor G,
  inverse := grothendieck_Type_to_Cat_inverse G,
  unit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨base, ⟨⟨f⟩⟩⟩, dsimp at *, subst f, ext, simp, }),
  counit_iso := nat_iso.of_components (λ X, by { cases X, exact iso.refl _, })
    (by { rintro ⟨⟩ ⟨⟩ ⟨f, e⟩, dsimp at *, subst e, ext, simp }),
  functor_unit_iso_comp' := by { rintro ⟨⟩, dsimp, simp, refl, } }

end grothendieck

end category_theory
