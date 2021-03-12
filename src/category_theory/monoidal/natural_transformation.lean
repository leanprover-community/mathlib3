/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functor
import category_theory.full_subcategory

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/

noncomputable theory

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

open monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
          {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

/--
A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure monoidal_nat_trans (F G : lax_monoidal_functor C D)
  extends nat_trans F.to_functor G.to_functor :=
(unit' : F.ε ≫ app (𝟙_ C) = G.ε . obviously)
(tensor' : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ . obviously)

restate_axiom monoidal_nat_trans.tensor'
attribute [simp, reassoc] monoidal_nat_trans.tensor
restate_axiom monoidal_nat_trans.unit'
attribute [simp, reassoc] monoidal_nat_trans.unit

namespace monoidal_nat_trans

/--
The identity monoidal natural transformation.
-/
@[simps]
def id (F : lax_monoidal_functor C D) : monoidal_nat_trans F F :=
{ ..(𝟙 F.to_functor) }

instance (F : lax_monoidal_functor C D) : inhabited (monoidal_nat_trans F F) := ⟨id F⟩

/--
Vertical composition of monoidal natural transformations.
-/
@[simps]
def vcomp {F G H : lax_monoidal_functor C D}
  (α : monoidal_nat_trans F G) (β : monoidal_nat_trans G H) : monoidal_nat_trans F H :=
{ ..(nat_trans.vcomp α.to_nat_trans β.to_nat_trans) }

instance category_lax_monoidal_functor : category (lax_monoidal_functor C D) :=
{ hom := monoidal_nat_trans,
  id := id,
  comp := λ F G H α β, vcomp α β, }

@[simp] lemma comp_to_nat_trans' {F G H : lax_monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

instance category_monoidal_functor : category (monoidal_functor C D) :=
induced_category.category monoidal_functor.to_lax_monoidal_functor

@[simp] lemma comp_to_nat_trans'' {F G H : monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

variables {E : Type u₃} [category.{v₃} E] [monoidal_category.{v₃} E]

/--
Horizontal composition of monoidal natural transformations.
-/
@[simps]
def hcomp {F G : lax_monoidal_functor C D} {H K : lax_monoidal_functor D E}
  (α : monoidal_nat_trans F G) (β : monoidal_nat_trans H K) :
  monoidal_nat_trans (F ⊗⋙ H) (G ⊗⋙ K) :=
{ unit' :=
  begin
    dsimp, simp,
    conv_lhs { rw [←K.to_functor.map_comp, α.unit], },
  end,
  tensor' := λ X Y,
  begin
    dsimp, simp,
    conv_lhs { rw [←K.to_functor.map_comp, α.tensor, K.to_functor.map_comp], },
  end,
  ..(nat_trans.hcomp α.to_nat_trans β.to_nat_trans) }

end monoidal_nat_trans

namespace monoidal_nat_iso

variables {F G : lax_monoidal_functor C D}

instance is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, is_iso (α.app X)] : is_iso α :=
⟨{ app := λ X, inv (α.app X),
  naturality' := λ X Y f,
  begin
    have h := congr_arg (λ f, inv (α.app X) ≫ (f ≫ inv (α.app Y)))
      (α.to_nat_trans.naturality f).symm,
    simp only [is_iso.inv_hom_id_assoc, is_iso.hom_inv_id, assoc, comp_id, cancel_mono] at h,
    exact h
  end,
  tensor' := λ X Y,
  begin
    dsimp,
    rw [is_iso.comp_inv_eq, assoc, monoidal_nat_trans.tensor, ←inv_tensor,
      is_iso.inv_hom_id_assoc],
  end },
  by tidy⟩

/--
Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction.
-/
def of_components
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f)
  (unit : F.ε ≫ (app (𝟙_ C)).hom = G.ε)
  (tensor : ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).hom = ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y) :
  F ≅ G :=
as_iso { app := λ X, (app X).hom }

@[simp] lemma of_components.hom_app
  (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
  (of_components app naturality unit tensor).hom.app X = (app X).hom := rfl
@[simp] lemma of_components.inv_app
  (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
  (of_components app naturality unit tensor).inv.app X = (app X).inv :=
by simp [of_components]

end monoidal_nat_iso

end category_theory
