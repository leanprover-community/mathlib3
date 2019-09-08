/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines a functor between categories.

(As it is a 'bundled' object rather than the `is_functorial` typeclass parametrised
by the underlying function on objects, the name is capitalised.)

Introduces notations
  `C ⥤ D` for the type of all functors from `C` to `D`.
    (I would like a better arrow here, unfortunately ⇒ (`\functor`) is taken by core.)
-/

import category_theory.category

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

/--
`functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id_lemma` expresses preservation of identities, and
`map_comp_lemma` expresses functoriality.
-/
structure functor (C : Sort u₁) [category.{v₁} C] (D : Sort u₂) [category.{v₂} D] :
  Sort (max v₁ v₂ u₁ u₂ 1) :=
(obj       : C → D)
(map       : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
infixr ` ⥤ `:26 := functor       -- type as \func --

restate_axiom functor.map_id'
attribute [simp] functor.map_id
restate_axiom functor.map_comp'
attribute [simp] functor.map_comp

namespace functor

section
variables (C : Sort u₁) [𝒞 : category.{v₁} C]
include 𝒞

/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C :=
{ obj := λ X, X,
  map := λ _ _ f, f }

notation `𝟭` := functor.id

variable {C}

@[simp] lemma id_obj (X : C) : (𝟭 C).obj X = X := rfl
@[simp] lemma id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl
end

section
variables {C : Sort u₁} [𝒞 : category.{v₁} C]
          {D : Sort u₂} [𝒟 : category.{v₂} D]
          {E : Sort u₃} [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ _ _ f, G.map (F.map f) }

infixr ` ⋙ `:80 := comp

@[simp] lemma comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma comp_map (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := rfl

end

section
variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

@[simp] def ulift_down : (ulift.{u₂} C) ⥤ C :=
{ obj := λ X, X.down,
  map := λ X Y f, f }

@[simp] def ulift_up : C ⥤ (ulift.{u₂} C) :=
{ obj := λ X, ⟨ X ⟩,
  map := λ X Y f, f }

end

end functor

end category_theory
