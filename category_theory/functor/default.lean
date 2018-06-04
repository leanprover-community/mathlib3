-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..category

open categories

namespace categories.functor
 
universes u₁ v₁ u₂ v₂ u₃ v₃

structure Functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
  (onObjects     : C → D)
  (onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (onObjects X) . obviously)
  (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma Functor.identities
make_lemma Functor.functoriality
attribute [simp,ematch] Functor.functoriality_lemma Functor.identities_lemma

infixr ` +> `:70 := Functor.onObjects
infixr ` &> `:70 := Functor.onMorphisms -- switch to ▹?
infixr ` ↝ `:70 := Functor              -- type as \lea 

definition IdentityFunctor (C : Type u₁) [category.{u₁ v₁} C] : C ↝ C := 
{ onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     refl 
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

instance (C) [category C] : has_one (C ↝ C) :=
{ one := IdentityFunctor C }

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

@[simp] lemma IdentityFunctor.onObjects (X : C) : (IdentityFunctor C) +> X = X := by refl
@[simp] lemma IdentityFunctor.onMorphisms {X Y : C} (f : X ⟶ Y) : (IdentityFunctor C) &> f = f := by refl

variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
variable {E : Type u₃}
variable [ℰ : category.{u₃ v₃} E]
include 𝒟 ℰ

definition FunctorComposition (F : C ↝ D) (G : D ↝ E) : C ↝ E := 
{ onObjects     := λ X, G +> (F +> X),
  onMorphisms   := λ _ _ f, G &> (F &> f),
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     simp,
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     simp
                   end }
infixr ` ⋙ `:80 := FunctorComposition

@[simp] lemma FunctorComposition.onObjects (F : C ↝ D) (G : D ↝ E) (X : C) : (F ⋙ G) +> X = G +> (F +> X) := by refl
@[simp] lemma FunctorComposition.onMorphisms (F : C ↝ D) (G : D ↝ E) (X Y : C) (f : X ⟶ Y) : (F ⋙ G) &> f = G.onMorphisms (F &> f) := by refl

end categories.functor
