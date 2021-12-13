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
import tactic.reassoc_axiom
import tactic.monotonicity

namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v v₁ v₂ v₃ u u₁ u₂ u₃

section

set_option old_structure_cmd true

/--
`functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See https://stacks.math.columbia.edu/tag/001B.
-/
structure functor (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]
  extends prefunctor C D : Type (max v₁ v₂ u₁ u₂) :=
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc functor.to_prefunctor

end

-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
infixr ` ⥤ `:26 := functor       -- type as \func --

restate_axiom functor.map_id'
attribute [simp] functor.map_id
restate_axiom functor.map_comp'
attribute [reassoc, simp] functor.map_comp

namespace functor

section
variables (C : Type u₁) [category.{v₁} C]

/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C :=
{ obj := λ X, X,
  map := λ _ _ f, f }

notation `𝟭` := functor.id -- Type this as `\sb1`

instance : inhabited (C ⥤ C) := ⟨functor.id C⟩

variable {C}

@[simp] lemma id_obj (X : C) : (𝟭 C).obj X = X := rfl
@[simp] lemma id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl
end

section
variables {C : Type u₁} [category.{v₁} C]
          {D : Type u₂} [category.{v₂} D]
          {E : Type u₃} [category.{v₃} E]

/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ _ _ f, G.map (F.map f) }

infixr ` ⋙ `:80 := comp

@[simp] lemma comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := rfl

-- These are not simp lemmas because rewriting along equalities between functors
-- is not necessarily a good idea.
-- Natural isomorphisms are also provided in `whiskering.lean`.
protected lemma comp_id (F : C ⥤ D) : F ⋙ (𝟭 D) = F := by cases F; refl
protected lemma id_comp (F : C ⥤ D) : (𝟭 C) ⋙ F = F := by cases F; refl

@[simp] lemma map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [decidable P]
  (f : P → (X ⟶ Y)) (g : ¬P → (X ⟶ Y)) :
  F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) :=
by { split_ifs; refl, }

end

end functor

end category_theory
