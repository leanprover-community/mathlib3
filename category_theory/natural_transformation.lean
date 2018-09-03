/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines natural transformations between functors.

Introduces notations
  `F ⟹ G` for the type of natural transformations between functors `F` and `G`,
  `τ X` (a coercion) for the components of natural transformations,
  `σ ⊟ τ` for vertical compositions, and
  `σ ◫ τ` for horizontal compositions.
-/

import category_theory.functor

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

/--
`nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation, and there is a
coercion available so you can write `α X` for the component of a transformation `α` at an object `X`.

Naturality is expressed by `α.naturality_lemma`.
-/
structure nat_trans (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F X) ⟶ (G X))
(naturality' : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f) . obviously)

infixr ` ⟹ `:50  := nat_trans             -- type as \==> or ⟹

namespace nat_trans

instance {F G : C ⥤ D} : has_coe_to_fun (F ⟹ G) :=
{ F   := λ α, Π X : C, (F X) ⟶ (G X),
  coe := λ α, α.app }

@[simp] lemma app_eq_coe {F G : C ⥤ D} (α : F ⟹ G) (X : C) : α.app X = α X := by unfold_coes
@[simp] lemma mk_app {F G : C ⥤ D} (app : Π X : C, (F X) ⟶ (G X)) (naturality) (X : C) : 
  { nat_trans . app := app, naturality' := naturality } X = app X := rfl 

lemma naturality {F G : C ⥤ D} (α : F ⟹ G) {X Y : C} (f : X ⟶ Y) : 
  (F.map f) ≫ (α Y) = (α X) ≫ (G.map f) := 
begin 
  /- `obviously'` says: -/ 
  erw nat_trans.naturality', refl
end

/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : F ⟹ F :=
{ app := λ X, 𝟙 (F X) }

@[simp] lemma id_app (F : C ⥤ D) (X : C) : (nat_trans.id F) X = 𝟙 (F X) := rfl

open category
open category_theory.functor

section
variables {F G H I : C ⥤ D}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[extensionality] lemma ext (α β : F ⟹ G) (w : ∀ X : C, α X = β X) : α = β :=
begin
  induction α with α_components α_naturality,
  induction β with β_components β_naturality,
  have hc : α_components = β_components := funext w,
  subst hc
end

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H :=
{ app         := λ X, (α X) ≫ (β X),
  naturality' := begin /- `obviously'` says: -/ intros, simp, rw [←assoc, naturality, assoc, ←naturality], end }

notation α `⊟` β:80 := vcomp α β

@[simp] lemma vcomp_app (α : F ⟹ G) (β : G ⟹ H) (X : C) : (α ⊟ β) X = (α X) ≫ (β X) := rfl
@[simp] lemma vcomp_assoc (α : F ⟹ G) (β : G ⟹ H) (γ : H ⟹ I) : (α ⊟ β) ⊟ γ = (α ⊟ (β ⊟ γ)) := by tidy
end

variables {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include ℰ

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ⟹ G) (β : H ⟹ I) : (F ⋙ H) ⟹ (G ⋙ I) :=
{ app         := λ X : C, (β (F X)) ≫ (I.map (α X)),
  naturality' := begin
                   /- `obviously'` says: -/
                   intros,
                   dsimp,
                   simp,
                   -- Actually, obviously doesn't use exactly this sequence of rewrites, but achieves the same result
                   rw [← assoc, naturality, assoc],
                   conv { to_rhs, rw [← map_comp, ← α.naturality, map_comp] }
                 end }

notation α `◫` β:80 := hcomp α β

@[simp] lemma hcomp_app {F G : C ⥤ D} {H I : D ⥤ E} (α : F ⟹ G) (β : H ⟹ I) (X : C) : 
  (α ◫ β) X = (β (F X)) ≫ (I.map (α X)) := rfl

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we need to use associativity of functor composition

lemma exchange {F G H : C ⥤ D} {I J K : D ⥤ E} (α : F ⟹ G) (β : G ⟹ H) (γ : I ⟹ J) (δ : J ⟹ K) : 
  ((α ⊟ β) ◫ (γ ⊟ δ)) = ((α ◫ γ) ⊟ (β ◫ δ)) :=
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