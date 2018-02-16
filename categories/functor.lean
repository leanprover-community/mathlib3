-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .isomorphism

open categories
open categories.isomorphism

namespace categories.functor

universes u₁ u₂ u₃ 

structure Functor (C : Type u₁) [category C] (D : Type u₂) [category D] :=
  (onObjects   : C → D)
  (onMorphisms : Π {X Y : C},
                Hom X Y → Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C),
    onMorphisms (𝟙 X) = 𝟙 (onObjects X) . obviously)
  (functoriality : ∀ {X Y Z : C} (f : Hom X Y) (g : Hom Y Z),
    onMorphisms (f >> g) = (onMorphisms f) >> (onMorphisms g) . obviously)

definition IdentityFunctor (C) [category C] : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f
}

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]
variable {E : Type u₃}
variable [category E]
variables {X Y : C}

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects : has_coe_to_fun (Functor C D) :=
{F   := λ f, C → D,
  coe := Functor.onObjects}

definition FunctorComposition (F : Functor C D) (G : Functor D E) : Functor C E :=
{
  onObjects     := λ X, G.onObjects (F.onObjects X),
  onMorphisms   := λ _ _ f, G.onMorphisms (F.onMorphisms f)
}

-- Functors preserve isomorphisms
definition Functor.onIsomorphisms (F : Functor C D) (g : Isomorphism X Y) : Isomorphism (F.onObjects X) (F.onObjects Y) :=
{
    morphism := F.onMorphisms g.morphism,
    inverse := F.onMorphisms g.inverse,
}

class ReflectsIsomorphisms (F : Functor C D) :=
  (reflects : Π (f : Hom X Y) (w : is_Isomorphism (F.onMorphisms f)), is_Isomorphism f)

end categories.functor
