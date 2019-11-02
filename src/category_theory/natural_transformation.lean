/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

Defines natural transformations between functors.

Introduces notations
  `τ.app X` for the components of natural transformations,
  `F ⟶ G` for the type of natural transformations between functors `F` and `G`,
  `σ ≫ τ` for vertical compositions, and
  `σ ◫ τ` for horizontal compositions.
-/

import category_theory.functor

namespace category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/--
`nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality_lemma`.
-/
structure nat_trans (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F.obj X) ⟶ (G.obj X))
(naturality' : ∀ {{X Y : C}} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f) . obviously)

restate_axiom nat_trans.naturality'
attribute [simp] nat_trans.naturality

namespace nat_trans

/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : nat_trans F F :=
{ app := λ X, 𝟙 (F.obj X) }

@[simp] lemma id_app' (F : C ⥤ D) (X : C) : (nat_trans.id F).app X = 𝟙 (F.obj X) := rfl

open category
open category_theory.functor

section
variables {F G H I : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
{ app         := λ X, (α.app X) ≫ (β.app X),
  naturality' :=
  begin
    /- `obviously'` says: -/
    intros, simp, rw [←assoc, naturality, assoc, ←naturality],
  end }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[extensionality] lemma ext {α β : nat_trans F G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
begin
  induction α with α_components α_naturality,
  induction β with β_components β_naturality,
  have hc : α_components = β_components := funext w,
  subst hc
end

@[simp] lemma vcomp_app (α : nat_trans F G) (β : nat_trans G H) (X : C) :
  (vcomp α β).app X = (α.app X) ≫ (β.app X) := rfl

end

end nat_trans

end category_theory
