/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.functor_category
import category_theory.isomorphism

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `a.app X : F.obj X ≅ G.obj X`,
and building natural isomorphisms from components:
*
```
nat_iso.of_components
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
F ≅ G
```
only needing to check naturality in one direction.

## Implementation

Note that `nat_iso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `iso`
namespace so that they are available using dot notation.
-/

open category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
open nat_trans

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {E : Type u₃} [category.{v₃} E]

namespace iso

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[simps] def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X :=
{ hom := α.hom.app X,
  inv := α.inv.app X,
  hom_inv_id' := begin rw [← comp_app, iso.hom_inv_id], refl end,
  inv_hom_id' := begin rw [← comp_app, iso.inv_hom_id], refl end }

@[simp, reassoc]
lemma hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
  α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
congr_fun (congr_arg nat_trans.app α.hom_inv_id) X

@[simp, reassoc]
lemma inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
  α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) :=
congr_fun (congr_arg nat_trans.app α.inv_hom_id) X

end iso

namespace nat_iso

open category_theory.category category_theory.functor

@[simp] lemma trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
  (α ≪≫ β).app X = α.app X ≪≫ β.app X := rfl

lemma app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).hom = α.hom.app X := rfl
lemma app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).inv = α.inv.app X := rfl

variables {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.hom.app X) :=
⟨⟨α.inv.app X,
  ⟨by rw [←comp_app, iso.hom_inv_id, ←id_app], by rw [←comp_app, iso.inv_hom_id, ←id_app]⟩⟩⟩

instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.inv.app X) :=
⟨⟨α.hom.app X,
  ⟨by rw [←comp_app, iso.inv_hom_id, ←id_app], by rw [←comp_app, iso.hom_inv_id, ←id_app]⟩⟩⟩

section
/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the later, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/

variables (α : F ≅ G)

@[simp] lemma cancel_nat_iso_hom_left {X : C} {Z : D} (g g' : G.obj X ⟶ Z) :
  α.hom.app X ≫ g = α.hom.app X ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_nat_iso_inv_left {X : C} {Z : D} (g g' : F.obj X ⟶ Z) :
  α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_nat_iso_hom_right {X : D} {Y : C} (f f' : X ⟶ F.obj Y) :
  f ≫ α.hom.app Y = f' ≫ α.hom.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_nat_iso_inv_right {X : D} {Y : C} (f f' : X ⟶ G.obj Y) :
  f ≫ α.inv.app Y = f' ≫ α.inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_nat_iso_hom_right_assoc {W X X' : D} {Y : C}
  (f : W ⟶ X) (g : X ⟶ F.obj Y) (f' : W ⟶ X') (g' : X' ⟶ F.obj Y)  :
  f ≫ g ≫ α.hom.app Y = f' ≫ g' ≫ α.hom.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_nat_iso_inv_right_assoc {W X X' : D} {Y : C}
  (f : W ⟶ X) (g : X ⟶ G.obj Y) (f' : W ⟶ X') (g' : X' ⟶ G.obj Y)  :
  f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

end

variables {X Y : C}
lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) :
  (α.inv.app X) ≫ (F.map f) ≫ (α.hom.app Y) = G.map f :=
by rw [naturality, ←category.assoc, ←nat_trans.comp_app, α.inv_hom_id, id_app, category.id_comp]
lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) :
  (α.hom.app X) ≫ (G.map f) ≫ (α.inv.app Y) = F.map f :=
by rw [naturality, ←category.assoc, ←nat_trans.comp_app, α.hom_inv_id, id_app, category.id_comp]

/--
The components of a natural isomorphism are isomorphisms.
-/
instance is_iso_app_of_is_iso (α : F ⟶ G) [is_iso α] (X) : is_iso (α.app X) :=
⟨⟨(inv α).app X,
  ⟨congr_fun (congr_arg nat_trans.app (is_iso.hom_inv_id α)) X,
   congr_fun (congr_arg nat_trans.app (is_iso.inv_hom_id α)) X⟩⟩⟩

@[simp] lemma is_iso_inv_app (α : F ⟶ G) [is_iso α] (X) : (inv α).app X = inv (α.app X) :=
by { ext, rw ←nat_trans.comp_app, simp, }

/--
Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
def of_components (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
  F ≅ G :=
{ hom := { app := λ X, (app X).hom },
  inv :=
  { app := λ X, (app X).inv,
    naturality' := λ X Y f,
    begin
      have h := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (naturality f).symm,
      simp only [iso.inv_hom_id_assoc, iso.hom_inv_id, assoc, comp_id, cancel_mono] at h,
      exact h
    end }, }

@[simp] lemma of_components.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app' naturality).app X = app' X :=
by tidy
@[simp] lemma of_components.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app naturality).hom.app X = (app X).hom := rfl
@[simp] lemma of_components.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app naturality).inv.app X = (app X).inv :=
by simp [of_components]

/--
A natural transformation is an isomorphism if all its components are isomorphisms.
-/
-- Making this an instance would cause a typeclass inference loop with `is_iso_app_of_is_iso`.
lemma is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, is_iso (α.app X)] : is_iso α :=
⟨(is_iso.of_iso (of_components (λ X, as_iso (α.app X)) (by tidy))).1⟩

/-- Horizontal composition of natural isomorphisms. -/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I :=
begin
  refine ⟨α.hom ◫ β.hom, α.inv ◫ β.inv, _, _⟩,
  { ext, rw [←nat_trans.exchange], simp, refl },
  ext, rw [←nat_trans.exchange], simp, refl
end

end nat_iso

end category_theory
