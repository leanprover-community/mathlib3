/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Junyan Xu
-/

import category_theory.lax_functor
import category_theory.elements
import category_theory.over
import category_theory.limits.preserves.basic

/-!
# The Grothendieck construction for lax functors

Given a lax functor `F` from a 1-category `C` to the 2-category `Cat`,
the objects of `grothendieck F` consist of dependent pairs `(b, f)`,
where `b : C` and `f : F.obj c`, and a morphism `(b, f) ⟶ (b', f')` is a
pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`. The forgetful
functor `grothendieck F ⥤ C` can be seen as a fibration of categories,
with base category `C`, total category `grothendieck F`, and fiber categories
`F.obj b`, `b : C`. When `F` is a pseudofunctor, this is a Grothendieck
fibration.

Notice that `F` gives a functor `F.map β` between fiber categories `F.obj b`
and `F.obj b'` for each morphism `β : b ⟶ b'` in `C`, which we call a component
functor. We show that if `F` is a pseudofunctor, the base category and all fiber
categories have colimits and the component functors all preserve colimits, then
the total category also has colimits.

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
(co)limits. Fibrations of categories such as `Top` over `Type`, or `PresheafedSpace`
over `Top` are also examples of this construction, and it may be preferable to
have the existence of (co)limits in `Top` refactored to use results here.

## References

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

See also `category_theory.elements` for the category of elements of functor `F : C ⥤ Type`.

-/

universes v u₁ u₂

namespace category_theory

variables {C : Type*} [category.{v} C] (F : lax_functor_to_Cat C)

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

@[simps obj map]
def fiber_push (X : C) : costructured_arrow (forget F) X ⥤ (F.obj X).1 :=
{ obj := λ f, (F.map f.hom).obj f.left.fiber,
  map := λ f₁ f₂ g, (eq_to_hom (by {rw ← costructured_arrow.w g, refl}) ≫
    F.map_comp g.left.base f₂.hom).app f₁.left.fiber ≫ (F.map f₂.hom).map g.left.fiber,
  map_id' := λ f, by {rw [nat_trans.comp_app, category.assoc], erw F.id_comp_components, simp},
  map_comp' := λ f₁ f₂ f₃ g₁ g₂, by {
    rw [category.assoc, nat_trans.naturality_assoc, ←category.assoc], /- RHS -/
    erw comp_fiber, rw [functor.map_comp, ←category.assoc], /- LHS -/
    congr' 1, swap, simp,
    { rw [nat_trans.comp_app, category.assoc], erw F.assoc_components,
      erw eq_to_hom.family_congr (F.map_comp g₁.left.base) (costructured_arrow.w g₂),
      simpa } } }

def fiber_push_comp {X Y : C} (f : X ⟶ Y) :
  costructured_arrow.map f ⋙ fiber_push F Y ⟶ fiber_push F X ⋙ F.map f :=
{ app := λ g, (F.map_comp _ _).app _,
  naturality' := λ g₁ g₂ f', by { dsimp, simp, } }

end

section colimit

open limits

variables {J : Type*} [small_category J] {𝒟 : J ⥤ grothendieck F}
(cb : cocone (𝒟 ⋙ forget F))

@[simp]
def fiber_diagram : J ⥤ (F.obj cb.X).1 :=
costructured_arrow.of_cocone _ _ cb.ι ⋙ costructured_arrow.pre _ _ _ ⋙ fiber_push _ _

variable (cf : cocone (fiber_diagram cb))

def total_cocone : cocone 𝒟 :=
{ X := { base := cb.X, fiber := cf.X },
  ι := { app := λ j, { base := cb.ι.app j, fiber := cf.ι.app j },
    naturality' := λ j j' f, by { erw category.comp_id, ext, swap,
      exact cocone.w cb f, { erw ← cocone.w cf f,
       dunfold fiber_diagram costructured_arrow.of_cocone fiber_push, simpa } } } }

variables {cb} (lb : is_colimit cb)

def desc_base (c : cocone 𝒟) : cb.X ⟶ c.X.base := lb.desc ((forget F).map_cocone c)
--{X := c.X.base, ι := whisker_right c.ι (forget F)}
--#check fiber_diagram 𝒟 cb
--#check grothendieck F

variable [∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), is_iso (F.map_comp f g)]

def fiber_cocone (c : cocone 𝒟) :
  cocone (fiber_diagram cb ⋙ F.map (desc_base lb c)) :=
{ X := c.X.fiber,
  ι := { app := λ j, (inv (F.map_comp _ _)).app _ ≫
    eq_to_hom (by {erw lb.fac, refl}) ≫ (c.ι.app j).fiber, -- (cb.ι.app j) (desc_base lb c)
    naturality' := λ j j' f, by { dsimp, simp, }} }

variable (lf : ∀ {c : C} (f : cb.X ⟶ c), is_colimit (functor.map_cocone (F.map f) cf))
--variable [∀ c, preserves_colimit (fiber_diagram 𝒟 cb) (F.map (desc_base 𝒟 cb lb c))]

def colimit_cocone_is_colimit : is_colimit (total_cocone cb cf) :=
{ desc := λ c,
  { base := desc_base lb c,
    fiber := (lf (desc_base lb c)).desc  },

}

variables [Hb : has_colimits_of_shape J C]
[Hf : ∀ X : C, has_colimits_of_shape J (F.obj X).1]

end colimit

/-
section

variables (G : pseudofunctor_to_Cat C) (X : grothendieck G.to_lax_functor_to_Cat)

@[simps obj map]
noncomputable def cleavage : under X.base ⥤ under X :=
{ obj := λ f, ⟨punit.star, ⟨f.right, (G.map f.hom).obj X.fiber⟩, ⟨f.hom, 𝟙 _⟩⟩,
  map := λ f₁ f₂ g, ⟨𝟙 _,
    ⟨g.right, (inv (G.map_comp f₁.hom g.right) ≫ eq_to_hom (by rw under.w g)).app X.fiber⟩,
    by { erw category.id_comp, ext1, {erw comp_fiber, dsimp, simpa}, exact (under.w g).symm }⟩,
  map_id' := λ f, by {ext1, ext1, {dsimp, simpa}, refl},
  map_comp' := λ f₁ f₂ f₃ g₁ g₂, by { congr, dsimp,
    have h := (G.1.assoc_components f₁.hom g₁.right g₂.right X.fiber).symm,
    let a := λ f, G.map_comp f g₂.right, have b := under.w g₁,
    have h' := eq_to_hom.family_congr a b, dsimp [a] at h',
    rw [h', ← category.assoc, ← is_iso.eq_comp_inv, ← is_iso.inv_eq_inv] at h,
    convert eq_whisker h (eq_to_hom (by simp : _ = (G.map f₃.hom).obj X.fiber)) using 1,
    simp, simpa } }

def cleavage_forget_counit : under.post (forget G.1) ⋙ cleavage G X ⟶ 𝟭 (under X) :=
{ app := λ f, ⟨eq_to_hom (by simp), ⟨𝟙 _, (G.map_id _).app _ ≫ f.hom.fiber⟩,
    by { dsimp, rw category.id_comp, ext,
      { erw comp_fiber, dsimp, simpa }, { erw comp_base, simp } }⟩,
  naturality' := λ f₁ f₂ g, by { ext,
    { dsimp, erw [comp_fiber, comp_fiber], dsimp, simp, } }}


def cleavage_forget_adjunction :
  cleavage G X ⊣ under.post (forget G.1) := adjunction.mk_of_unit_counit
{ unit := eq_to_hom $ by { apply functor.hext, { rintro ⟨⟨_⟩,_⟩, refl },
    { rintros ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩ ⟨⟨_⟩,_⟩, dsimp, congr } },
  counit := ,
  left_triangle' := ,
  right_triangle' := }

end
-/
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
