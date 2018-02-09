-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.functor

universes u1 u2 u3 v1 v2 v3

structure Functor (C : Category.{u1 v1}) (D : Category.{u2 v2}) :=
(onObjects   : C.Obj → D.Obj)
(onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
(identities : ∀ (X : C.Obj),
    onMorphisms (C.identity X) = D.identity (onObjects X) )
(functoriality : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g) )

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects {C D : Category}: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C.Obj → D.Obj,
  coe := Functor.onObjects }

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if to_onObjects is already in scope.
-- instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
-- { F   := λ f, Π ⦃X Y : C.Obj⦄, C.Hom X Y → D.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

definition IdentityFunctor (C: Category.{u1 v1}) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := begin dsimp, intros, refl end,
  functoriality := begin dsimp, intros, refl end,
}

definition FunctorComposition {C : Category.{u1 v1}} {D : Category.{u2 v2}} {E : Category.{u3 v3}} (F : Functor C D) (G : Functor D E) : Functor C E :=
{
  onObjects     := λ X, G.onObjects (F.onObjects X),
  onMorphisms   := λ _ _ f, G.onMorphisms (F.onMorphisms f),
  identities    := begin intros, simp end,
  functoriality := begin intros, simp end,
}

end categories.functor
