/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/

import data.equiv.basic
import category.bifunctor

universes u v w

variables {α β : Type u}
open equiv

namespace functor

variables {f : Type u → Type v} [functor f] [is_lawful_functor f]

def map_equiv (h : α ≃ β) : f α ≃ f β :=
{ to_fun    := map h,
  inv_fun   := map h.symm,
  left_inv  := λ x,
    by { rw map_map, convert is_lawful_functor.id_map x, ext a, apply symm_apply_apply },
  right_inv := λ x,
    by { rw map_map, convert is_lawful_functor.id_map x, ext a, apply apply_symm_apply } }

@[simp]
lemma map_equiv_apply (h : α ≃ β) (x : f α) :
  (map_equiv h : f α ≃ f β) x = map h x := rfl

@[simp]
lemma map_equiv_symm_apply (h : α ≃ β) (y : f β) :
  (map_equiv h : f α ≃ f β).symm y = map h.symm y := rfl

end functor

namespace bifunctor

variables {α' β' : Type v} {F : Type u → Type v → Type w} [bifunctor F] [is_lawful_bifunctor F]

def map_equiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' :=
{ to_fun    := bimap h h',
  inv_fun   := bimap h.symm h'.symm,
  left_inv  := λ x,
    by { rw bimap_bimap, convert is_lawful_bifunctor.id_bimap x; { ext a, apply symm_apply_apply } },
  right_inv := λ x,
    by { rw bimap_bimap, convert is_lawful_bifunctor.id_bimap x; { ext a, apply apply_symm_apply } } }

@[simp]
lemma map_equiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
  (map_equiv h h' : F α α' ≃ F β β') x = bimap h h' x := rfl

@[simp]
lemma map_equiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
  (map_equiv h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y := rfl

end bifunctor
