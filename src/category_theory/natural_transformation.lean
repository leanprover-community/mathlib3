/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

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

variables {C : Sort u₁} [𝒞 : category.{v₁} C] {D : Sort u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/--
`nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality_lemma`.
-/
-- Unfortunately the universe level here needs a `(max ... 1)`,
-- so Lean can be sure that we're not in Prop.
structure nat_trans (F G : C ⥤ D) : Sort (max u₁ v₂ 1) :=
(app : Π X : C, (F.obj X) ⟶ (G.obj X))
(naturality' : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f) . obviously)

restate_axiom nat_trans.naturality'

namespace nat_trans

/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : nat_trans F F :=
{ app := λ X, 𝟙 (F.obj X) }

@[simp] lemma id_app (F : C ⥤ D) (X : C) : (nat_trans.id F).app X = 𝟙 (F.obj X) := rfl

open category
open category_theory.functor

section
variables {F G H I : C ⥤ D}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[extensionality] lemma ext (α β : nat_trans F G) (w : ∀ X : C, α.app X = β.app X) : α = β :=
begin
  induction α with α_components α_naturality,
  induction β with β_components β_naturality,
  have hc : α_components = β_components := funext w,
  subst hc
end

lemma congr_app {α β : nat_trans F G} (h : α = β) (X : C) : α.app X = β.app X := by rw h

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
{ app         := λ X, (α.app X) ≫ (β.app X),
  naturality' :=
  begin
    /- `obviously'` says: -/
    intros, simp, rw [←assoc, naturality, assoc, ←naturality],
  end }

@[simp] lemma vcomp_app (α : nat_trans F G) (β : nat_trans G H) (X : C) :
  (vcomp α β).app X = (α.app X) ≫ (β.app X) :=
rfl
@[simp] lemma vcomp_assoc (α : nat_trans F G) (β : nat_trans G H) (γ : nat_trans H I) :
  vcomp (vcomp α β) γ = vcomp α (vcomp β γ) :=
by tidy
end

variables {E : Sort u₃} [ℰ : category.{v₃} E]
include ℰ

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : nat_trans F G) (β : nat_trans H I) : nat_trans (F ⋙ H) (G ⋙ I) :=
{ app         := λ X : C, (β.app (F.obj X)) ≫ (I.map (α.app X)),
  naturality' := begin
                   /- `obviously'` says: -/
                   intros,
                   dsimp,
                   simp,
                   -- Actually, obviously doesn't use exactly this sequence of rewrites, but achieves the same result
                   rw [← assoc, naturality, assoc],
                   conv { to_rhs, rw [← map_comp, ← α.naturality, map_comp] }
                 end }

infix ` ◫ `:80 := hcomp

@[simp] lemma hcomp_app {F G : C ⥤ D} {H I : D ⥤ E} (α : nat_trans F G) (β : nat_trans H I) (X : C) :
  (α ◫ β).app X = (β.app (F.obj X)) ≫ (I.map (α.app X)) := rfl

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we need to use associativity of functor composition

lemma exchange {F G H : C ⥤ D} {I J K : D ⥤ E} (α : nat_trans F G) (β : nat_trans G H) (γ : nat_trans I J) (δ : nat_trans J K) :
  ((vcomp α β) ◫ (vcomp γ δ)) = (vcomp (α ◫ γ) (β ◫ δ)) :=
begin
  -- `obviously'` says:
  ext,
  intros,
  dsimp,
  simp,
  -- again, this isn't actually what obviously says, but it achieves the same effect.
  conv { to_lhs, congr, skip, rw [←assoc, ←naturality, assoc] }
end

end nat_trans

end category_theory
