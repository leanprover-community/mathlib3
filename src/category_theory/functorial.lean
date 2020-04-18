/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.functor

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/-- A unbundled functor. -/
-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the
-- immediate plan.
class functorial (F : C → D) : Type (max v₁ v₂ u₁ u₂) :=
(map       : Π {X Y : C}, (X ⟶ Y) → ((F X) ⟶ (F Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (F X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

restate_axiom functorial.map_id'
attribute [simp] functorial.map_id
restate_axiom functorial.map_comp'
attribute [simp] functorial.map_comp

/--
If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f  : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map (F : C → D) [functorial.{v₁ v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
functorial.map.{v₁ v₂} f

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

section
omit 𝒟

instance functorial_id : functorial.{v₁ v₁} (id : C → C) :=
{ map := λ X Y f, f }
end

section
variables {E : Type u₃} [ℰ : category.{v₃} E]
include ℰ

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

end category_theory
