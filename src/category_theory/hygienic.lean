/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.functor
import category_theory.isomorphism

/-!
-/

namespace category_theory

universes v u

variables {C : Type u} [category.{v} C]

class hygienic (p : C → Prop) : Prop :=
(map : Π {X Y : C}, (X ≅ Y) → (p X → p Y))

def hygienic.map_iso (p : C → Prop) [hygienic.{v} p] {X Y : C} (φ : X ≅ Y) : p X ↔ p Y :=
⟨hygienic.map.{v} φ, hygienic.map.{v} φ.symm⟩

instance subsingleton_hygienic (p : C → Prop) : subsingleton (hygienic.{v} p) :=
⟨by { rintros ⟨a⟩ ⟨b⟩, congr }⟩

end category_theory
