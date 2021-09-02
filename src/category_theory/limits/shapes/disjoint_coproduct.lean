/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.limits.over

/-!
# Disjoint coproducts

Defines disjoint coproducts: coproducts where the intersection is initial and the coprojections
are monic.
Shows that a category with disjoint coproducts is `initial_mono_class`.

## TODO

* Adapt this to the infinitary (small) version: This is one of the conditions in Giraud's theorem
  characterising sheaf topoi.
* Construct examples (and counterexamples?), eg Type, Vec.
* Define extensive categories, and show every extensive category has disjoint coproducts.
* Define coherent categories and use this to define positive coherent categories.
-/

universes v u u₂

namespace category_theory
namespace limits

open category

variables {C : Type u} [category.{v} C]

/--
Given any pullback diagram of the form

Z  ⟶  X₁
↓      ↓
X₂ ⟶  X

where `X₁ ⟶ X ← X₂` is a coproduct diagram, then `Z` is initial, and both `X₁ ⟶ X` and `X₂ ⟶ X`
are mono.
-/
class coproduct_disjoint (X₁ X₂ : C) :=
(is_initial_of_is_pullback_of_is_coproduct :
  ∀ {X Z} {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} {f : Z ⟶ X₁} {g : Z ⟶ X₂}
    (cX : is_colimit (binary_cofan.mk pX₁ pX₂)) {comm : f ≫ pX₁ = g ≫ pX₂},
    is_limit (pullback_cone.mk _ _ comm) → is_initial Z)
(mono_inl : ∀ X (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (cX : is_colimit (binary_cofan.mk X₁ X₂)), mono X₁)
(mono_inr : ∀ X (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (cX : is_colimit (binary_cofan.mk X₁ X₂)), mono X₂)

/--
If the coproduct of `X₁` and `X₂` is disjoint, then given any pullback square

Z  ⟶  X₁
↓      ↓
X₂ ⟶  X

where `X₁ ⟶ X ← X₂` is a coproduct, then `Z` is initial.
-/
def is_initial_of_is_pullback_of_is_coproduct {Z X₁ X₂ X : C} [coproduct_disjoint X₁ X₂]
  {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} (cX : is_colimit (binary_cofan.mk pX₁ pX₂))
  {f : Z ⟶ X₁} {g : Z ⟶ X₂} {comm : f ≫ pX₁ = g ≫ pX₂}
  (cZ : is_limit (pullback_cone.mk _ _ comm)) :
  is_initial Z :=
coproduct_disjoint.is_initial_of_is_pullback_of_is_coproduct cX cZ

/--
If the coproduct of `X₁` and `X₂` is disjoint, then given any pullback square

Z  ⟶  X₁
↓       ↓
X₂ ⟶  X₁ ⨿ X₂

`Z` is initial.
-/
noncomputable def is_initial_of_is_pullback_of_coproduct {Z X₁ X₂ : C}
  [has_binary_coproduct X₁ X₂] [coproduct_disjoint X₁ X₂]
  {f : Z ⟶ X₁} {g : Z ⟶ X₂} {comm : f ≫ (coprod.inl : X₁ ⟶ _ ⨿ X₂) = g ≫ coprod.inr}
  (cZ : is_limit (pullback_cone.mk _ _ comm)) :
  is_initial Z :=
coproduct_disjoint.is_initial_of_is_pullback_of_is_coproduct (coprod_is_coprod _ _) cZ

/--
If the coproduct of `X₁` and `X₂` is disjoint, then provided `X₁ ⟶ X ← X₂` is a coproduct the
pullback is an initial object:

        X₁
        ↓
X₂ ⟶  X
-/
noncomputable def is_initial_of_pullback_of_is_coproduct {X X₁ X₂ : C} [coproduct_disjoint X₁ X₂]
  {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} [has_pullback pX₁ pX₂]
  (cX : is_colimit (binary_cofan.mk pX₁ pX₂)) :
  is_initial (pullback pX₁ pX₂) :=
coproduct_disjoint.is_initial_of_is_pullback_of_is_coproduct cX (pullback_is_pullback _ _)

/--
If the coproduct of `X₁` and `X₂` is disjoint, the pullback of `X₁ ⟶ X₁ ⨿ X₂` and `X₂ ⟶ X₁ ⨿ X₂`
is initial.
-/
noncomputable def is_initial_of_pullback_of_coproduct {X₁ X₂ : C}
  [has_binary_coproduct X₁ X₂] [coproduct_disjoint X₁ X₂]
    [has_pullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr] :
  is_initial (pullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr) :=
is_initial_of_is_pullback_of_coproduct (pullback_is_pullback _ _)

instance {X₁ X₂ : C} [has_binary_coproduct X₁ X₂] [coproduct_disjoint X₁ X₂] :
  mono (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) :=
coproduct_disjoint.mono_inl _ _ _ (coprod_is_coprod _ _)
instance {X₁ X₂ : C} [has_binary_coproduct X₁ X₂] [coproduct_disjoint X₁ X₂] :
  mono (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) :=
coproduct_disjoint.mono_inr _ _ _ (coprod_is_coprod _ _)

/-- `C` has disjoint coproducts if every coproduct is disjoint. -/
class coproducts_disjoint (C : Type u) [category.{v} C] :=
(coproduct_disjoint : ∀ (X Y : C), coproduct_disjoint X Y)

attribute [instance, priority 999] coproducts_disjoint.coproduct_disjoint

/-- If `C` has disjoint coproducts, any morphism out of initial is mono. Note it isn't true in
general that `C` has strict initial objects, for instance consider the category of types and
partial functions. -/
lemma initial_mono_class_of_disjoint_coproducts [coproducts_disjoint C] : initial_mono_class C :=
{ is_initial_mono_from := λ I X hI,
    coproduct_disjoint.mono_inl _ _ (𝟙 X)
      { desc := λ (s : binary_cofan _ _), s.inr,
        fac' := λ s j, walking_pair.cases_on j (hI.hom_ext _ _) (id_comp _),
        uniq' := λ (s : binary_cofan _ _) m w, (id_comp _).symm.trans (w walking_pair.right) } }

end limits
end category_theory
