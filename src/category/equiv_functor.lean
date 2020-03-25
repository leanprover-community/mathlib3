/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Functors with two arguments
-/

import category.basic category.functor
       data.equiv.functor

universes u₀ u₁ u₂ v₀ v₁ v₂

open function

class equiv_functor (f : Type u₀ → Type u₁) :=
(map_equiv : Π {α β}, (α ≃ β) → (f α ≃ f β))
(id_map : Π α, map_equiv (equiv.refl α) = equiv.refl (f α))
(map_map : Π {α β γ} (k : α ≃ β) (h : β ≃ γ),
  (map_equiv k).trans (map_equiv h) = map_equiv (k.trans h))

namespace equiv_functor
@[priority 100]
instance of_is_lawful_functor
  (f : Type u₀ → Type u₁) [functor f] [is_lawful_functor f] : equiv_functor f :=
{ map_equiv := λ α β e, functor.map_equiv e,
  id_map := λ α, begin ext, dsimp, end }
