/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines natural transformations between functors.

Introduces notations
  `F ⟹ G` for the type of natural transformations between functors `F` and `G`,
  `τ @> X` for the components of natural transformations,
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
(components: Π X : C, (F +> X) ⟶ (G +> X))
(naturality: ∀ {X Y : C} (f : X ⟶ Y), (F &> f) ≫ (components Y) = (components X) ≫ (G &> f) . obviously)

make_lemma NaturalTransformation.naturality
attribute [ematch] NaturalTransformation.naturality_lemma

infixr ` ⟹ `:50  := NaturalTransformation             -- type as \==> or ⟹

instance {F G : C ↝ D} : has_coe_to_fun (F ⟹ G) :=
{ F   := λ α, Π X : C, (F +> X) ⟶ (G +> X),
  coe := λ α, α.components }

definition identity_natural_transformation (F : C ↝ D) : F ⟹ F := 
{ components := λ X, 𝟙 (F +> X),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp
                end }

@[simp] lemma identity_natural_transformation.components (F : C ↝ D) (X : C) : (identity_natural_transformation F) X = 𝟙 (F +> X) := by refl

instance NaturalTransform.has_one (F : C ↝ D) : has_one (F ⟹ F) := 
{ one := identity_natural_transformation F }

section
variables {F G H : C ↝ D}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[extensionality] lemma NaturalTransformations_componentwise_equal (α β : F ⟹ G) (w : ∀ X : C, α X = β X) : α = β :=
begin
  induction α with α_components α_naturality,
  induction β with β_components β_naturality,
  have hc : α_components = β_components := funext w,
  subst hc
end

definition vertical_composition_of_NaturalTransformations (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H := 
{ components := λ X, (α X) ≫ (β X),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp,
                  erw [←category.associativity_lemma, NaturalTransformation.naturality_lemma, category.associativity_lemma, ←NaturalTransformation.naturality_lemma],
                  refl,
                end }

notation α `⊟` β:80 := vertical_composition_of_NaturalTransformations α β    

@[simp,ematch] lemma vertical_composition_of_NaturalTransformations.components (α : F ⟹ G) (β : G ⟹ H) (X : C) : (α ⊟ β) X = (α X) ≫ (β X) := by refl
end

variable {E : Type u₃}
variable [ℰ : category.{u₃ v₃} E]
include ℰ

definition horizontal_composition_of_NaturalTransformations {F G : C ↝ D} {H I : D ↝ E} (α : F ⟹ G) (β : H ⟹ I) : (F ⋙ H) ⟹ (G ⋙ I) :=
{ components := λ X : C, (β (F +> X)) ≫ (I &> (α X)), 
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp at *,
                  unfold_coes,
                  -- Actually, obviously doesn't use exactly this sequence of rewrites, but achieves the same result
                  rw [← category.associativity_lemma],
                  rw [NaturalTransformation.naturality_lemma],
                  rw [category.associativity_lemma],
                  conv { to_rhs, rw [← Functor.functoriality_lemma] },
                  rw [← α.naturality_lemma],
                  rw [Functor.functoriality_lemma],
                end }

notation α `◫` β:80 := horizontal_composition_of_NaturalTransformations α β

@[simp,ematch] lemma horizontal_composition_of_NaturalTransformations.components {F G : C ↝ D} {H I : D ↝ E} (α : F ⟹ G) (β : H ⟹ I) (X : C) : (α ◫ β) X = (β (F +> X)) ≫ (I &> (α X)) := by refl

@[ematch] lemma NaturalTransformation.exchange {F G H : C ↝ D} {I J K : D ↝ E} (α : F ⟹ G) (β : G ⟹ H) (γ : I ⟹ J) (δ : J ⟹ K) : ((α ⊟ β) ◫ (γ ⊟ δ)) = ((α ◫ γ) ⊟ (β ◫ δ)) := 
begin
  -- `obviously'` says:
  apply category_theory.NaturalTransformations_componentwise_equal,
  intros,
  simp at *,
  unfold_coes,
  -- again, this isn't actually what obviously says, but it achieves the same effect.
  conv {to_lhs, congr, skip, rw [←category.associativity_lemma] },
  rw [←NaturalTransformation.naturality_lemma],
  rw [category.associativity_lemma],
end

end category_theory