/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.functor
import category_theory.isomorphism
import category_theory.core

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/-- A unbundled functor. -/
-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the
-- immediate plan.
class functorial (F : C → D) : Type (max v₁ v₂ u₁ u₂) :=
(map          : Π {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y))
(map_id' []   : ∀ (X : C), map (𝟙 X) = 𝟙 (F X) . obviously)
(map_comp' [] : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

restate_axiom functorial.map_id'
attribute [simp] functorial.map_id
restate_axiom functorial.map_comp'
attribute [simp] functorial.map_comp

section
variables (F : C → D) [functorial.{v₁ v₂} F]
/--
If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
functorial.map.{v₁ v₂} f

@[simp]
lemma map_id (X : C) : map F (𝟙 X) = 𝟙 (F X) := functorial.map_id F X
@[simp]
lemma map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : map F (f ≫ g) = map F f ≫ map F g :=
functorial.map_comp F _ _

/--
If `F : C → D` (just a function) has `[functorial F]`,
we can write `map_iso F f : F X ≅ F Y` for the action of `F` on an isomorphism `f : X ≅ Y`.
-/
@[simps]
def map_iso (F : C → D) [functorial.{v₁ v₂} F] {X Y : C} (f : X ≅ Y) : F X ≅ F Y :=
{ hom := map F f.hom,
  inv := map F f.inv,
  hom_inv_id' := begin rw [←map_comp, f.hom_inv_id, map_id], end,
  inv_hom_id' := begin rw [←map_comp, f.inv_hom_id, map_id], end }
end

namespace functor

/--
Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : functorial.{v₁ v₂} F] : C ⥤ D :=
{ obj := F,
  ..I }

end functor

instance (F : C ⥤ D) : functorial.{v₁ v₂} (F.obj) := { .. F }

@[simp]
lemma map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f := rfl

instance functorial_id : functorial.{v₁ v₁} (id : C → C) :=
{ map := λ X Y f, f }

section
variables {E : Type u₃} [category.{v₃} E]

/--
`G ∘ F` is a functorial if both `F` and `G` are.
-/
-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
def functorial_comp (F : C → D) [functorial.{v₁ v₂} F] (G : D → E) [functorial.{v₂ v₃} G] :
  functorial.{v₁ v₃} (G ∘ F) :=
{ ..(functor.of F ⋙ functor.of G) }

end

/-- Evidence that a function `F : C → D` is the object part of a functor `(core C ⥤ D)`. -/
class iso_functorial (F : C → D) : Type (max v₁ v₂ u₁ u₂) :=
(map     []   : Π {X Y : C}, (X ≅ Y) → (F X ⟶ F Y))
(map_id' []   : ∀ (X : C), map (iso.refl X) = 𝟙 (F X) . obviously)
(map_comp' [] : ∀ {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z), map (f ≪≫ g) = (map f) ≫ (map g) . obviously)

restate_axiom iso_functorial.map_id'
attribute [simp] iso_functorial.map_id
restate_axiom iso_functorial.map_comp'
attribute [simp] iso_functorial.map_comp

@[simps]
def iso_functorial.map_iso (F : C → D) [iso_functorial.{v₁ v₂} F] {X Y : C} (i : X ≅ Y) :
  F X ≅ F Y :=
{ hom := iso_functorial.map.{v₁ v₂} F i,
  inv := iso_functorial.map.{v₁ v₂} F i.symm,
  hom_inv_id' := by rw [←iso_functorial.map_comp, iso.self_symm_id, iso_functorial.map_id],
  inv_hom_id' := by rw [←iso_functorial.map_comp, iso.symm_self_id, iso_functorial.map_id], }

@[simp]
lemma iso_functorial.map_iso_id (F : C → D) [iso_functorial.{v₁ v₂} F] (X : C) :
  iso_functorial.map_iso F (iso.refl X) = iso.refl (F X) :=
by tidy

@[simp]
lemma iso_functorial.map_iso_comp (F : C → D) [iso_functorial.{v₁ v₂} F]
  {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
  iso_functorial.map_iso F (f ≪≫ g) = iso_functorial.map_iso F f ≪≫ iso_functorial.map_iso F g :=
by tidy

namespace functor

/--
Bundle an iso_functorial function `C → D` as a functor from `core C`.
-/
def of_iso_functorial (F : C → D) [I : iso_functorial.{v₁ v₂} F] : (core C) ⥤ D :=
{ obj := λ X, F (core.desc X),
  map := λ X Y f, iso_functorial.map.{v₁ v₂} F (core.desc_hom f) }

@[simp]
lemma of_iso_functorial_obj (F : C → D) [I : iso_functorial.{v₁ v₂} F] (X : core C) :
  (of_iso_functorial F).obj X = F (core.desc X) := rfl

end functor

end category_theory
