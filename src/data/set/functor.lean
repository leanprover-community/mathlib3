/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.set.lattice

/-!
# Functoriality of `set`

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

instance : is_lawful_monad set :=
{ pure_bind             := λ α β x f, by simp,
  bind_assoc            := λ α β γ s f g, set.ext $ λ a,
    by simp [exists_and_distrib_right.symm, -exists_and_distrib_right,
             exists_and_distrib_left.symm, -exists_and_distrib_left, and_assoc];
       exact exists_swap,
  id_map                := λ α, id_map,
  bind_pure_comp_eq_map := λ α β f s, set.ext $ by simp [set.image, eq_comm],
  bind_map_eq_seq       := λ α β s t, by simp [seq_def] }

instance : is_comm_applicative (set : Type u → Type u) :=
⟨ λ α β s t, prod_image_seq_comm s t ⟩

instance : alternative set :=
{ orelse := λ α, (∪),
  failure := λ α, ∅,
  .. set.monad }

end set
