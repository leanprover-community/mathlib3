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

import .functor

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

structure NaturalTransformation (F G : C ↝ D) : Type (max u₁ v₂) :=
(components : Π X : C, (F X) ⟶ (G X))
(naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (components Y) = (components X) ≫ (G.map f) . obviously)

make_lemma NaturalTransformation.naturality
attribute [ematch] NaturalTransformation.naturality_lemma

infixr ` ⟹ `:50  := NaturalTransformation             -- type as \==> or ⟹

namespace NaturalTransformation

instance {F G : C ↝ D} : has_coe_to_fun (F ⟹ G) :=
{ F   := λ α, Π X : C, (F X) ⟶ (G X),
  coe := λ α, α.components }

@[simp] lemma unfold_components_coercion {F G : C ↝ D} (α : F ⟹ G) (X : C) : α X = α.components X := rfl

end NaturalTransformation

namespace Functor
definition identity (F : C ↝ D) : F ⟹ F := 
{ components := λ X, 𝟙 (F X),
  naturality := begin /- `obviously'` says: -/ intros, dsimp, simp end }

instance has_one (F : C ↝ D) : has_one (F ⟹ F) := 
{ one := identity F }

@[simp] lemma identity.components (F : C ↝ D) (X : C) : (identity F) X = 𝟙 (F X) := rfl
@[simp] lemma has_one.components (F : C ↝ D) (X : C) : (1 : F ⟹ F) X = 𝟙 (F X) := rfl

end Functor

namespace NaturalTransformation

open category Functor

section
variables {F G H : C ↝ D}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[extensionality] lemma componentwise_equal (α β : F ⟹ G) (w : ∀ X : C, α X = β X) : α = β :=
begin
  induction α with α_components α_naturality,
  induction β with β_components β_naturality,
  have hc : α_components = β_components := funext w,
  subst hc
end

definition vcomp (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H := 
{ components := λ X, (α X) ≫ (β X),
  naturality := begin /- `obviously'` says: -/ intros, simp, rw [←assoc_lemma, naturality_lemma, assoc_lemma, ←naturality_lemma], end }

notation α `⊟` β:80 := vcomp α β    

@[simp] lemma vcomp.components (α : F ⟹ G) (β : G ⟹ H) (X : C) : (α ⊟ β) X = (α X) ≫ (β X) := rfl
end

variable {E : Type u₃}
variable [ℰ : category.{u₃ v₃} E]
include ℰ

definition hcomp {F G : C ↝ D} {H I : D ↝ E} (α : F ⟹ G) (β : H ⟹ I) : (F ⋙ H) ⟹ (G ⋙ I) :=
{ components := λ X : C, (β (F X)) ≫ (I.map (α X)), 
  naturality := begin 
                  /- `obviously'` says: -/
                  intros,
                  dsimp,
                  simp,
                  -- Actually, obviously doesn't use exactly this sequence of rewrites, but achieves the same result
                  rw [← assoc_lemma, naturality_lemma, assoc_lemma],
                  conv { to_rhs, rw [← functoriality_lemma, ← α.naturality_lemma, functoriality_lemma] }
                end }

notation α `◫` β:80 := hcomp α β

@[simp] lemma hcomp.components {F G : C ↝ D} {H I : D ↝ E} (α : F ⟹ G) (β : H ⟹ I) (X : C) : (α ◫ β) X = (β (F X)) ≫ (I.map (α X)) := rfl

@[ematch] lemma exchange {F G H : C ↝ D} {I J K : D ↝ E} (α : F ⟹ G) (β : G ⟹ H) (γ : I ⟹ J) (δ : J ⟹ K) : ((α ⊟ β) ◫ (γ ⊟ δ)) = ((α ◫ γ) ⊟ (β ◫ δ)) := 
begin
  -- `obviously'` says:
  apply componentwise_equal,
  intros,
  dsimp,
  simp,
  -- again, this isn't actually what obviously says, but it achieves the same effect.
  conv { to_lhs, congr, skip, rw [←assoc_lemma, ←naturality_lemma, assoc_lemma] }
end

end NaturalTransformation
end category_theory