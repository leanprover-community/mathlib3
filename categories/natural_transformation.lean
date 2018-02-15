-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .functor

open categories
open categories.functor

namespace categories.natural_transformation

universes u v w
variable {C : Type u}
variable [category C]
variable {D : Type v}
variable [category D]
variable {E : Type w}
variable [category E]

structure NaturalTransformation (F G : Functor C D) :=
  (components: Π X : C, Hom (F.onObjects X) (G.onObjects X))
  (naturality: ∀ {X Y : C} (f : Hom X Y),
     (F.onMorphisms f) >> (components Y) = (components X) >> (G.onMorphisms f) . obviously)

variables {F G H: Functor C D}

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components : has_coe_to_fun (NaturalTransformation F G) :=
{F   := λ f, Π X : C, Hom (F.onObjects X) (G.onObjects X),
  coe := NaturalTransformation.components}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  (α β : NaturalTransformation F G)
  (w : ∀ X : C, α.components X = β.components X) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components := funext w,
    subst hc
  end

definition IdentityNaturalTransformation (F : Functor C D) : NaturalTransformation F F :=
{
    components := λ X, 𝟙 (F.onObjects X)
}

definition vertical_composition_of_NaturalTransformations
  (α : NaturalTransformation F G)
  (β : NaturalTransformation G H) : NaturalTransformation F H :=
{
    components := λ X, (α.components X) >> (β.components X)
}

notation α `∘̬` β := vertical_composition_of_NaturalTransformations α β

open categories.functor

@[simp] lemma FunctorComposition.onObjects (F : Functor C D) (G : Functor D E) (X : C) : (FunctorComposition F G).onObjects X = G.onObjects (F.onObjects X) := by obviously

definition horizontal_composition_of_NaturalTransformations
  {F G : Functor C D}
  {H I : Functor D E}
  (α : NaturalTransformation F G)
  (β : NaturalTransformation H I) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
{
    components := λ X : C, (β.components (F.onObjects X)) >> (I.onMorphisms (α.components X))
}

notation α `∘ₕ` β := horizontal_composition_of_NaturalTransformations α β

definition whisker_on_left
  (F : Functor C D)
  {G H : Functor D E}
  (α : NaturalTransformation G H) :
  NaturalTransformation (FunctorComposition F G) (FunctorComposition F H) :=
  (IdentityNaturalTransformation F) ∘ₕ α

definition whisker_on_right
  {F G : Functor C D}
  (α : NaturalTransformation F G)
  (H : Functor D E) :
  NaturalTransformation (FunctorComposition F H) (FunctorComposition G H) :=
  α ∘ₕ (IdentityNaturalTransformation H)

end categories.natural_transformation
