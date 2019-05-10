/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/

import data.equiv.basic

universes u v

variables {α β : Type u} {f : Type u → Type v} [functor f] [is_lawful_functor f]
open functor equiv function is_lawful_functor

def functor.map_equiv (h : α ≃ β) : f α ≃ f β :=
{ to_fun    := map h,
  inv_fun   := map h.symm,
  left_inv  := λ x, by { rw map_map, transitivity id <$> x,
                        { congr, ext a, simp only [id.def, symm_apply_apply, comp_app] },
                        { simp only [is_lawful_functor.id_map] } },
  right_inv := λ x, by { rw map_map, transitivity id <$> x,
                        { congr, ext a, simp only [id.def, apply_symm_apply, comp_app] },
                        { simp only [is_lawful_functor.id_map] } } }
