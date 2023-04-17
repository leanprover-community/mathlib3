/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.set.lattice

/-!
# Functoriality of `set`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the functor structure of `set`.
-/

universes u

open function

namespace set
variables {α β : Type u} {s : set α} {f : α → set β} {g : set (α → β)}

instance : monad.{u} set :=
{ pure       := λ α a, {a},
  bind       := λ α β s f, ⋃ i ∈ s, f i,
  seq        := λ α β, set.seq,
  map        := λ α β, set.image }

@[simp] lemma bind_def : s >>= f = ⋃ i ∈ s, f i := rfl
@[simp] lemma fmap_eq_image (f : α → β) : f <$> s = f '' s := rfl
@[simp] lemma seq_eq_set_seq (s : set (α → β)) (t : set α) : s <*> t = s.seq t := rfl
@[simp] lemma pure_def (a : α) : (pure a : set α) = {a} := rfl

/-- `set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
lemma image2_def {α β γ : Type*} (f : α → β → γ) (s : set α) (t : set β) :
  image2 f s t = f <$> s <*> t :=
by { ext, simp }

instance : is_lawful_monad set :=
{ id_map                := λ α, image_id,
  comp_map              := λ α β γ f g s, image_comp _ _ _,
  pure_bind             := λ α β, bUnion_singleton,
  bind_assoc            := λ α β γ s f g, by simp only [bind_def, bUnion_Union],
  bind_pure_comp_eq_map := λ α β f s, (image_eq_Union _ _).symm,
  bind_map_eq_seq       := λ α β s t, seq_def.symm }

instance : is_comm_applicative (set : Type u → Type u) :=
⟨ λ α β s t, prod_image_seq_comm s t ⟩

instance : alternative set :=
{ orelse := λ α, (∪),
  failure := λ α, ∅,
  .. set.monad }

end set
