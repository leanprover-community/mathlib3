/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines a functor between categories.

(As it is a 'bundled' object rather than the `is_functorial` typeclass parametrised 
by the underlying function on objects, the name is capitalised.)

Introduces notations
  `C ↝ D` for the type of all functors from `C` to `D`. (I would like a better arrow here, unfortunately ⇒ (`\functor`) is taken by core.)
  `F X` (a coercion) for a functor `F` acting on an object `X`.
-/

import .category

namespace category_theory
 
universes u₁ v₁ u₂ v₂ u₃ v₃

structure functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(obj           : C → D)
(map           : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id        : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

make_lemma functor.map_id
make_lemma functor.functoriality
attribute [simp,ematch] functor.map_id_lemma functor.functoriality_lemma

infixr ` ↝ `:70 := functor       -- type as \lea -- 

namespace functor

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

instance : has_coe_to_fun (C ↝ D) :=
{ F   := λ F, C → D,
  coe := λ F, F.obj }

@[simp] lemma coe_def (F : C ↝ D) (X : C) : F X = F.obj X := rfl

end functor

namespace category

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

definition identity : C ↝ C := 
{ obj     := λ X, X,
  map     := λ _ _ f, f,
  map_id  := begin /- `obviously'` says: -/ intros, refl end,
  functoriality := begin /- `obviously'` says: -/ intros, refl end }

instance has_one : has_one (C ↝ C) :=
{ one := identity C }

variable {C}

@[simp] lemma identity.on_objects (X : C) : (identity C) X = X := rfl
@[simp] lemma identity.on_morphisms {X Y : C} (f : X ⟶ Y) : (identity C).map f = f := rfl
@[simp] lemma has_one.on_objects (X : C) : (1 : C ↝ C) X = X := rfl
@[simp] lemma has_one.on_morphisms {X Y : C} (f : X ⟶ Y) : (1 : C ↝ C).map f = f := rfl

end category

namespace functor

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

definition comp (F : C ↝ D) (G : D ↝ E) : C ↝ E := 
{ obj    := λ X, G.obj (F.obj X),
  map    := λ _ _ f, G.map (F.map f),
  map_id := begin /- `obviously'` says: -/ intros, simp end,
  functoriality := begin /- `obviously'` says: -/ intros, simp end }

infixr ` ⋙ `:80 := comp

@[simp] lemma comp.on_objects (F : C ↝ D) (G : D ↝ E) (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma comp.on_morphisms (F : C ↝ D) (G : D ↝ E) (X Y : C) (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f) := rfl

end functor
end category_theory
