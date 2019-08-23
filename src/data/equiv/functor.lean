/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/

import data.equiv.basic data.option.basic

universes u v u' v'

variables {α β : Type u} {f : Type u → Type v} [functor f] [is_lawful_functor f]
open functor equiv function is_lawful_functor

def functor.map_equiv (h : α ≃ β) : f α ≃ f β :=
{ to_fun    := map h,
  inv_fun   := map h.symm,
  left_inv  := λ x,
    by { rw map_map, convert is_lawful_functor.id_map x, ext a, apply symm_apply_apply },
  right_inv := λ x,
    by { rw map_map, convert is_lawful_functor.id_map x, ext a, apply apply_symm_apply } }

class ufunctor (F : Type u → Type v) (G : Type u' → Type v') :=
(map_equiv : ∀ {α β}, α ≃ β → F α ≃ G β)

instance : ufunctor option.{u} option.{v} :=
{ map_equiv := λ α β h,
   { to_fun := option.map h.to_fun,
     inv_fun := option.map h.inv_fun,
     left_inv := λ x, by cases x; simp [h.left_inv _],
     right_inv := λ x, by cases x; simp [h.right_inv _] } }

instance : ufunctor list.{u} list.{v} :=
{ map_equiv := λ α β h,
   { to_fun := list.map h.to_fun,
     inv_fun := list.map h.inv_fun,
     left_inv := λ x, by simp [h.left_inv _,(∘)]; apply list.map_id,
     right_inv := λ x, by simp [h.right_inv _,(∘)]; apply list.map_id } }
