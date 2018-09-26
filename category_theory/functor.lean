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
  `F X` (a coercion) for a functor `F` acting on an object `X`.
-/

import category_theory.category
import tactic.tidy

namespace category_theory

universes u v u₁ v₁ u₂ v₂ u₃ v₃

/--
`functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F X` (which uses a coercion), and to a morphism use `F.map f`.

The axiom `map_id_lemma` expresses preservation of identities, and
`map_comp_lemma` expresses functoriality.

Implementation note: when constructing a `functor`, you need to define the
`map'` field (which does not know about the coercion).
When using a `functor`, use the `map` field (which makes use of the coercion).
-/
structure functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(obj       : C → D)
(map'      : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id'   : ∀ (X : C), map' (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map' (f ≫ g) = (map' f) ≫ (map' g) . obviously)

infixr ` ⥤ `:70 := functor       -- type as \func --

namespace functor

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

instance : has_coe_to_fun (C ⥤ D) :=
{ F   := λ F, C → D,
  coe := λ F, F.obj }

def map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : (F X) ⟶ (F Y) := F.map' f

@[simp] lemma map_id (F : C ⥤ D) (X : C) : F.map (𝟙 X) = 𝟙 (F X) :=
begin unfold functor.map, erw F.map_id', refl end
@[simp] lemma map_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g :=
begin unfold functor.map, erw F.map_comp' end

-- We define a refl lemma 'refolding' the coercion,
-- and two lemmas for the coercion applied to an explicit structure.
@[simp] lemma obj_eq_coe {F : C ⥤ D} (X : C) : F.obj X = F X := rfl
@[simp] lemma mk_obj (o : C → D) (m mi mc) (X : C) :
  ({ functor . obj := o, map' := m, map_id' := mi, map_comp' := mc } : C ⥤ D) X = o X := rfl
@[simp] lemma mk_map (o : C → D) (m mi mc) {X Y : C} (f : X ⟶ Y) :
  functor.map { functor . obj := o, map' := m, map_id' := mi, map_comp' := mc } f = m f := rfl
end

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

/-- `functor.id C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C :=
{ obj      := λ X, X,
  map'     := λ _ _ f, f }

variable {C}

@[simp] lemma id_obj (X : C) : (functor.id C) X = X := rfl
@[simp] lemma id_map {X Y : C} (f : X ⟶ Y) : (functor.id C).map f = f := rfl
end

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
          {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
{ obj      := λ X, G (F X),
  map'      := λ _ _ f, G.map (F.map f) }

infixr ` ⋙ `:80 := comp

@[simp] lemma comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) : (F ⋙ G) X = G (F X) := rfl
@[simp] lemma comp_map (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := rfl
end

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

@[simp] def ulift_down : (ulift.{u₂} C) ⥤ C :=
{ obj := λ X, X.down,
  map' := λ X Y f, f }

@[simp] def ulift_up : C ⥤ (ulift.{u₂} C) :=
{ obj := λ X, ⟨ X ⟩,
  map' := λ X Y f, f }
end

end functor

def bundled.map {c : Type u → Type v} {d : Type u → Type v} (f : Π{a}, c a → d a) (s : bundled c) : bundled d :=
{ α := s.α, str := f s.str }

def concrete_functor
  {C : Type u → Type v} {hC : ∀{α β}, C α → C β → (α → β) → Prop} [concrete_category @hC]
  {D : Type u → Type v} {hD : ∀{α β}, D α → D β → (α → β) → Prop} [concrete_category @hD]
  (m : ∀{α}, C α → D α) (h : ∀{α β} {ia : C α} {ib : C β} {f}, hC ia ib f → hD (m ia) (m ib) f) :
  bundled C ⥤ bundled D :=
{ obj := bundled.map @m,
  map' := λ X Y f, ⟨ f, h f.2 ⟩}

end category_theory
