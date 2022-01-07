/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (obj a ⟶ obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (map f ⟶ map g)`,
* a family of 2-morphisms `F.map_id a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.map_comp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `oplax_functor B C` : an oplax functor between bicategories `B` and `C`
* `oplax_functor.comp F G` : the composition of oplax functors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `map_id` and `map_comp`. We may need both in mathlib in the future, but for
now we only define oplax functors.

In addition, if we require `map_id` and `map_comp` to be isomorphisms, we obtain the definition
of pseudofunctors. There are several possible design choices to implement pseudofunctors,
but the choice is left to future development.
-/

set_option old_structure_cmd true

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section
variables (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables (C : Type u₂) [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]

/--
A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `oplax_functor`.
-/
structure prelax_functor extends prefunctor B C : Type (max w₁ w₂ v₁ v₂ u₁ u₂) :=
(map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g))

/-- The prefunctor between the underlying quivers. -/
add_decl_doc prelax_functor.to_prefunctor

namespace prelax_functor

variables {B C} {D : Type u₃} [quiver.{v₃+1} D] [∀ a b : D, quiver.{w₃+1} (a ⟶ b)]
variables (F : prelax_functor B C) (G : prelax_functor C D)

@[simp] lemma to_prefunctor_obj : F.to_prefunctor.obj = F.obj := rfl
@[simp] lemma to_prefunctor_map : F.to_prefunctor.map = F.map := rfl

variables (B)

/-- The identity prelax functor. -/
@[simps]
def id : prelax_functor B B :=
{ map₂ := λ a b f g η, η, .. prefunctor.id B }

instance : inhabited (prelax_functor B B) := ⟨prelax_functor.id B⟩

variables {B}

/-- Composition of prelax functors. -/
@[simps]
def comp : prelax_functor B D :=
{ map₂ := λ a b f g η, G.map₂ (F.map₂ η), .. F.to_prefunctor.comp G.to_prefunctor }

end prelax_functor

end

section
variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]

/--
This auxiliary definition states that oplax functors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
We use this auxiliary definition instead of writing it directly in the definition
of oplax functors because doing so will cause a timeout.
-/
@[simp]
def oplax_functor.map₂_associator_aux
  (obj : B → C) (map : Π {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (map₂ : Π {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
  (map_comp : Π {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ⟶ map f ≫ map g)
  {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
map₂ (α_ f g h).hom ≫ map_comp f (g ≫ h) ≫ (map f ◁ map_comp g h) =
  map_comp (f ≫ g) h ≫ (map_comp f g ▷ map h) ≫ (α_ (map f) (map g) (map h)).hom

variables (B C)

/--
An oplax functor `F` between bicategories `B` and `C` consists of functions between objects,
1-morphisms, and 2-morphisms.

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve the identity. Instead, there are
specified 2-morphisms `F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

Functions between 2-morphisms strictly commute with compositions and preserve the identity.
They also preserve the associator, the left unitor, and the right unitor modulo some adjustments
of domains and codomains of 2-morphisms.
-/
structure oplax_functor extends prelax_functor B C : Type (max w₁ w₂ v₁ v₂ u₁ u₂) :=
(map_id (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g)
(map_comp_naturality_left' : ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  map₂ (η ▷ g) ≫ map_comp f' g = map_comp f g ≫ (map₂ η ▷ map g) . obviously)
(map_comp_naturality_right' : ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
  map₂ (f ◁ η) ≫ map_comp f g' = map_comp f g ≫ (map f ◁ map₂ η) . obviously)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  oplax_functor.map₂_associator_aux obj (λ a b, map) (λ a b f g, map₂) (λ a b c, map_comp) f g h
    . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (λ_ f).hom = map_comp (𝟙 a) f ≫ (map_id a ▷ map f) ≫ (λ_ (map f)).hom . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (ρ_ f).hom = map_comp f (𝟙 b) ≫ (map f ◁ map_id b) ≫ (ρ_ (map f)).hom . obviously)

restate_axiom oplax_functor.map_comp_naturality_left'
restate_axiom oplax_functor.map_comp_naturality_right'
restate_axiom oplax_functor.map₂_id'
restate_axiom oplax_functor.map₂_comp'
restate_axiom oplax_functor.map₂_associator'
restate_axiom oplax_functor.map₂_left_unitor'
restate_axiom oplax_functor.map₂_right_unitor'
attribute [simp]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right
  oplax_functor.map₂_id oplax_functor.map₂_associator
attribute [reassoc]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right
  oplax_functor.map₂_comp oplax_functor.map₂_associator
  oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor
attribute [simp]
  oplax_functor.map₂_comp oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor

namespace oplax_functor

variables {B} {C} {D : Type u₃} [bicategory.{w₃ v₃} D]
variables (F : oplax_functor B C) (G : oplax_functor C D)

/-- Function between 1-morphisms as a functor. -/
@[simps]
def map_functor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
{ obj := λ f, F.map f,
  map := λ f g η, F.map₂ η }

/-- The prelax functor between the underlying quivers. -/
add_decl_doc oplax_functor.to_prelax_functor

@[simp] lemma to_prelax_functor_obj : F.to_prelax_functor.obj = F.obj := rfl
@[simp] lemma to_prelax_functor_map : F.to_prelax_functor.map = F.map := rfl
@[simp] lemma to_prelax_functor_map₂ : F.to_prelax_functor.map₂ = F.map₂ := rfl

variables (B)

/-- The identity oplax functor. -/
@[simps]
def id : oplax_functor B B :=
{ map_id := λ a, 𝟙 (𝟙 a),
  map_comp := λ a b c f g, 𝟙 (f ≫ g),
  .. prelax_functor.id B }

instance : inhabited (oplax_functor B B) := ⟨id B⟩

variables {B}

/-- Composition of oplax functors. -/
@[simps]
def comp : oplax_functor B D :=
{ map_id := λ a,
    (G.map_functor _ _).map (F.map_id a) ≫ G.map_id (F.obj a),
  map_comp := λ a b c f g,
    (G.map_functor _ _).map (F.map_comp f g) ≫ G.map_comp (F.map f) (F.map g),
  map_comp_naturality_left' := λ a b c f f' η g, by
  { dsimp,
    rw [←map₂_comp_assoc, map_comp_naturality_left, map₂_comp_assoc, map_comp_naturality_left,
      assoc] },
  map_comp_naturality_right' := λ a b c f g g' η, by
  { dsimp,
    rw [←map₂_comp_assoc, map_comp_naturality_right, map₂_comp_assoc, map_comp_naturality_right,
      assoc] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    simp only [map₂_associator, ←map₂_comp_assoc, ←map_comp_naturality_right_assoc,
      whisker_left_comp, assoc],
    simp only [map₂_associator, map₂_comp, map_comp_naturality_left_assoc,
      whisker_right_comp, assoc] },
  map₂_left_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_left_unitor, map₂_comp, map_comp_naturality_left_assoc,
      whisker_right_comp, assoc] },
  map₂_right_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_right_unitor, map₂_comp, map_comp_naturality_right_assoc,
      whisker_left_comp, assoc] },
  .. F.to_prelax_functor.comp G.to_prelax_functor }

end oplax_functor

end

end category_theory
