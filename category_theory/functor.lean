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
import tactic.tidy

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

/--
`functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id_lemma` expresses preservation of identities, and
`map_comp_lemma` expresses functoriality.
-/
structure functor (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :
  Type (max u₁ v₁ u₂ v₂) :=
(obj       : C → D)
(map       : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

infixr ` ⥤ `:70 := functor       -- type as \func --

restate_axiom functor.map_id'
attribute [simp] functor.map_id
restate_axiom functor.map_comp'
attribute [simp] functor.map_comp

namespace functor

section
variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

/-- `functor.id C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C :=
{ obj := λ X, X,
  map := λ _ _ f, f }

variable {C}

@[simp] lemma id_obj (X : C) : (functor.id C).obj X = X := rfl
@[simp] lemma id_map {X Y : C} (f : X ⟶ Y) : (functor.id C).map f = f := rfl
end

section
variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
          {E : Type u₃} [ℰ : category.{v₃} E]
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

def bundled.map {c : Type u → Type v} {d : Type u → Type v} (f : Π{a}, c a → d a) (s : bundled c) :
  bundled d :=
{ α := s.α, str := f s.str }

def concrete_functor
  {C : Type u → Type v} {hC : ∀{α β}, C α → C β → (α → β) → Prop} [concrete_category @hC]
  {D : Type u → Type v} {hD : ∀{α β}, D α → D β → (α → β) → Prop} [concrete_category @hD]
  (m : ∀{α}, C α → D α) (h : ∀{α β} {ia : C α} {ib : C β} {f}, hC ia ib f → hD (m ia) (m ib) f) :
  bundled C ⥤ bundled D :=
{ obj := bundled.map @m,
  map := λ X Y f, ⟨ f, h f.2 ⟩}

end category_theory
