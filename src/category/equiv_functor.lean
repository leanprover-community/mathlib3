/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/

import category_theory.category
import data.equiv.functor

/-!
# Functions functorial with respect to equivalences

An `equiv_functor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/

universes u₀ u₁ u₂ v₀ v₁ v₂

open function

class equiv_functor (f : Type u₀ → Type u₁) :=
(map_equiv : Π {α β}, (α ≃ β) → (f α ≃ f β))
(id_map' : Π α, map_equiv (equiv.refl α) = equiv.refl (f α) . obviously)
(map_map' : Π {α β γ} (k : α ≃ β) (h : β ≃ γ),
  (map_equiv k).trans (map_equiv h) = map_equiv (k.trans h) . obviously)

restate_axiom equiv_functor.id_map'
restate_axiom equiv_functor.map_map'
attribute [simp] equiv_functor.id_map

namespace equiv_functor

@[priority 100]
instance of_is_lawful_functor
  (f : Type u₀ → Type u₁) [functor f] [is_lawful_functor f] : equiv_functor f :=
{ map_equiv := λ α β e, functor.map_equiv e,
  id_map' := λ α, by { ext, apply is_lawful_functor.id_map, },
  map_map' := λ α β γ k h, by { ext x, apply (is_lawful_functor.comp_map k h x).symm, } }

-- TODO Include more examples here
instance equiv_functor_inhabited : equiv_functor inhabited :=
{ map_equiv := λ α β, equiv.inhabited_congr, }
instance equiv_functor_unique : equiv_functor unique :=
{ map_equiv := λ α β, equiv.unique_congr, }

end equiv_functor
