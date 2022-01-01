/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

/-!
# Pseudofunctors

A pseudofunctor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (obj a ⟶ obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (map f ⟶ map g)`,
* a family of isomorphisms `F.map_id a : 𝟙 (obj a) ≅ map (𝟙 a)`,
* a family of isomorphisms `F.map_comp f g : map f ≫ map g ≅ map (f ≫ g)`, and
* certain consistency conditions on them.

The direction of isomorphisms `map_comp` and `map_id` here is the lax direction.

## TODO

* Lax and oplax functors.
-/

set_option old_structure_cmd true

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

/--
A prepseudofunctor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `pseudofunctor`.
-/
structure prepseudofunctor
  (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
  (C : Type u₂) [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]
  extends prefunctor B C : Type (max w₁ w₂ v₁ v₂ u₁ u₂) :=
(map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g))

/-- The prefunctor between the underlying quivers. -/
add_decl_doc prepseudofunctor.to_prefunctor

variables {B : Type u₁} [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables {C : Type u₂} [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]
variables (F : prepseudofunctor B C)

@[simp] lemma prepseudofunctor.to_prefunctor_obj : F.to_prefunctor.obj = F.obj := rfl
@[simp] lemma prepseudofunctor.to_prefunctor_map : F.to_prefunctor.map = F.map := rfl

end

namespace prepseudofunctor

section
variables (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]

/-- The identity prepseudofunctor. -/
@[simps]
def id : prepseudofunctor B B :=
{ map₂ := λ a b f g η, η, .. prefunctor.id B }

instance : inhabited (prepseudofunctor B B) := ⟨prepseudofunctor.id B⟩

end

section
variables {B : Type u₁} [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables {C : Type u₂} [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]
variables {D : Type u₃} [quiver.{v₃+1} D] [∀ a b : D, quiver.{w₃+1} (a ⟶ b)]
variables (F : prepseudofunctor B C) (G : prepseudofunctor C D)

/-- Composition of prepseudofunctors. -/
@[simps]
def comp : prepseudofunctor B D :=
{ map₂ := λ a b f g η, G.map₂ (F.map₂ η), .. F.to_prefunctor.comp G.to_prefunctor }

end

end prepseudofunctor

section

/--
A pseudofunctor `F` between bicategories `B` and `C` consists of functions between objects,
1-morphisms, and 2-morphisms.

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve the identity. Instead, there are
specified isomorphisms `𝟙 (F.obj a) ≅ F.map (𝟙 a)` and `F.map f ≫ F.map g ≅ F.map (f ≫ g)`.

Functions between 2-morphisms strictly commute with compositions and preserve the identity.
They also preserve the associator, the left unitor, and the right unitor modulo some adjustments
of domains and codomains of 2-morphisms.
-/
structure pseudofunctor (B : Type u₁) [bicategory.{w₁ v₁} B] (C : Type u₂) [bicategory.{w₂ v₂} C]
  extends prepseudofunctor B C : Type (max w₁ w₂ v₁ v₂ u₁ u₂) :=
(map_id (a : B) : 𝟙 (obj a) ≅ map (𝟙 a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ≅ map (f ≫ g))
(map_comp_naturality_left' : ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  (map₂ η ▷ map g) ≫ (map_comp f' g).hom = (map_comp f g).hom ≫ map₂ (η ▷ g) . obviously)
(map_comp_naturality_right' : ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
  (map f ◁ map₂ η) ≫ (map_comp f g').hom = (map_comp f g).hom ≫ map₂ (f ◁ η) . obviously)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  ((map_comp f g).hom ▷ map h) ≫ (map_comp (f ≫ g) h).hom ≫ map₂ (α_ f g h).hom =
    (α_ (map f) (map g) (map h)).hom ≫ (map f ◁ (map_comp g h).hom) ≫
      (map_comp f (g ≫ h)).hom . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  ((map_id a).hom ▷ map f) ≫ (map_comp (𝟙 a) f).hom ≫ map₂ (λ_ f).hom =
    (λ_ (map f)).hom . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  (map f ◁ (map_id b).hom) ≫ (map_comp f (𝟙 b)).hom ≫ map₂ (ρ_ f).hom =
    (ρ_ (map f)).hom . obviously)

set_option trace.class_instances false

restate_axiom pseudofunctor.map_comp_naturality_left'
restate_axiom pseudofunctor.map_comp_naturality_right'
restate_axiom pseudofunctor.map₂_id'
restate_axiom pseudofunctor.map₂_comp'
restate_axiom pseudofunctor.map₂_associator'
restate_axiom pseudofunctor.map₂_left_unitor'
restate_axiom pseudofunctor.map₂_right_unitor'
attribute [simp]
  pseudofunctor.map_comp_naturality_left pseudofunctor.map_comp_naturality_right
  pseudofunctor.map₂_id pseudofunctor.map₂_associator
  pseudofunctor.map₂_left_unitor pseudofunctor.map₂_right_unitor
attribute [reassoc]
  pseudofunctor.map_comp_naturality_left pseudofunctor.map_comp_naturality_right
  pseudofunctor.map₂_comp pseudofunctor.map₂_associator
  pseudofunctor.map₂_left_unitor pseudofunctor.map₂_right_unitor
attribute [simp]
  pseudofunctor.map₂_comp

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables (F : pseudofunctor B C)

/-- Function on 1-morphisms as a functor. -/
@[simps]
def pseudofunctor.map_functor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
{ obj := λ f, F.map f,
  map := λ f g η, F.map₂ η }

/-- The prepseudofunctor between the underlying quivers. -/
add_decl_doc pseudofunctor.to_prepseudofunctor

@[simp] lemma pseudofunctor.to_prepseudofunctor_obj : F.to_prepseudofunctor.obj = F.obj := rfl
@[simp] lemma pseudofunctor.to_prepseudofunctor_map : F.to_prepseudofunctor.map = F.map := rfl
@[simp] lemma pseudofunctor.to_prepseudofunctor_map₂ : F.to_prepseudofunctor.map₂ = F.map₂ := rfl

end

namespace pseudofunctor

section
variables (B : Type u₁) [bicategory.{w₁ v₁} B]

/-- The identity pseudofunctor. -/
@[simps]
def id : pseudofunctor B B :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, iso.refl (f ≫ g),
  .. prepseudofunctor.id B }

instance : inhabited (pseudofunctor B B) := ⟨id B⟩

end

section
variables {B : Type u₁} [bicategory.{w₁ v₁} B]
variables {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {D : Type u₃} [bicategory.{w₃ v₃} D]
variables (F : pseudofunctor B C) (G : pseudofunctor C D)

/-- Composition of pseudofunctors. -/
@[simps]
def comp : pseudofunctor B D :=
{ map_id := λ a,
    G.map_id (F.obj a) ≪≫ (G.map_functor _ _).map_iso (F.map_id a),
  map_comp := λ a b c f g,
    G.map_comp (F.map f) (F.map g) ≪≫ (G.map_functor _ _).map_iso (F.map_comp f g),
  map_comp_naturality_left' := λ a b c f f' η g, by
  { dsimp,
    rw [map_comp_naturality_left_assoc, ←map₂_comp, map_comp_naturality_left],
    simp only [map₂_comp, assoc] },
  map_comp_naturality_right' := λ a b c f g g' η, by
  { dsimp,
    rw [map_comp_naturality_right_assoc, ←map₂_comp, map_comp_naturality_right],
    simp only [map₂_comp, assoc] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp, simp only [whisker_right_comp, whisker_left_comp, assoc],
    rw [map_comp_naturality_left_assoc, map_comp_naturality_right_assoc, ←map₂_associator_assoc],
    simp only [←map₂_comp],
    rw ←map₂_associator },
  map₂_left_unitor' := λ a b f, by
  { dsimp, simp only [whisker_right_comp, assoc],
    rw [map_comp_naturality_left_assoc, ←map₂_left_unitor],
    simp only [←map₂_comp],
    rw ←map₂_left_unitor },
  map₂_right_unitor' := λ a b f, by
  { dsimp, simp only [whisker_left_comp, assoc],
    rw [map_comp_naturality_right_assoc, ←map₂_right_unitor],
    simp only [←map₂_comp],
    rw ←map₂_right_unitor },
  .. F.to_prepseudofunctor.comp G.to_prepseudofunctor }

end

end pseudofunctor

end category_theory
