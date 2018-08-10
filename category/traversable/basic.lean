/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type classes for traversing collections. The concepts and laws are taken from
http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html
-/

import tactic.cache
import category.applicative

open function (hiding comp)

universes u v w

section applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

structure applicative_transformation : Type (max (u+1) v w) :=
(app : ∀ {α : Type u}, F α → G α)
(preserves_pure' : ∀ {α : Type u} (x : α), app (pure x) = pure x)
(preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app (x <*> y) = app x <*> app y)

end applicative_transformation

namespace applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

instance : has_coe_to_fun (applicative_transformation F G) := ⟨_, λ m, m.app⟩

variables {F G}
variables (η : applicative_transformation F G)

@[functor_norm]
lemma preserves_pure : ∀ {α} (x : α), η (pure x) = pure x := η.preserves_pure'

@[functor_norm]
lemma preserves_seq :
  ∀ {α β : Type u} (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
η.preserves_seq'

@[functor_norm]
lemma preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y :=
by rw [← pure_seq_eq_map, η.preserves_seq]; simp with functor_norm

end applicative_transformation

open applicative_transformation

class traversable (t : Type u → Type u) extends functor t :=
(traverse : Π {m : Type u → Type u} [applicative m] {α β},
   (α → m β) → t α → m (t β))

open functor

export traversable (traverse)

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}


variables {f : Type u → Type u} [applicative f]

def sequence [traversable t] : t (f α) → f (t α) := traverse id

end functions

class is_lawful_traversable (t : Type u → Type u) [traversable t]
  extends is_lawful_functor t : Type (u+1) :=
(id_traverse : ∀ {α} (x : t α), traverse id.mk x = x )
(comp_traverse : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    {α β γ} (f : β → F γ) (g : α → G β) (x : t α),
  traverse (comp.mk ∘ map f ∘ g) x =
  comp.mk (map (traverse f) (traverse g x)))
(traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α),
  traverse (id.mk ∘ f) x = id.mk (f <$> x))
(naturality : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    (η : applicative_transformation F G) {α β} (f : α → F β) (x : t α),
  η (traverse f x) = traverse (@η _ ∘ f) x)
