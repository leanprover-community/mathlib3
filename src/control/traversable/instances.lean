/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.traversable.lemmas
import data.list.forall2
import data.set.lattice

/-!
# Traversable instances

This file provides instances of `traversable` for types from the core library: `option`, `list` and
`sum`.
-/

universes u v

section option

open functor

variables {F G : Type u → Type u}
variables [applicative F] [applicative G]
variables [is_lawful_applicative F] [is_lawful_applicative G]

lemma option.id_traverse {α} (x : option α) : option.traverse id.mk x = x :=
by cases x; refl

@[nolint unused_arguments]
lemma option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : option α) :
  option.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (option.traverse f <$> option.traverse g x) :=
by cases x; simp! with functor_norm; refl

lemma option.traverse_eq_map_id {α β} (f : α → β) (x : option α) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by cases x; refl

variable (η : applicative_transformation F G)

lemma option.naturality {α β} (f : α → F β) (x : option α) :
  η (option.traverse f x) = option.traverse (@η _ ∘ f) x :=
by cases x with x; simp! [*] with functor_norm

end option

instance : is_lawful_traversable option :=
{ id_traverse := @option.id_traverse,
  comp_traverse := @option.comp_traverse,
  traverse_eq_map_id := @option.traverse_eq_map_id,
  naturality := @option.naturality,
  .. option.is_lawful_monad }

namespace list

variables {F G : Type u → Type u}
variables [applicative F] [applicative G]

section
variables [is_lawful_applicative F] [is_lawful_applicative G]

open applicative functor
open list (cons)

protected lemma id_traverse {α} (xs : list α) :
  list.traverse id.mk xs = xs :=
by induction xs; simp! * with functor_norm; refl

@[nolint unused_arguments]
protected lemma comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : list α) :
  list.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (list.traverse f <$> list.traverse g x) :=
by induction x; simp! * with functor_norm; refl

protected lemma traverse_eq_map_id {α β} (f : α → β) (x : list α) :
  list.traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by induction x; simp! * with functor_norm; refl

variable (η : applicative_transformation F G)

protected lemma naturality {α β} (f : α → F β) (x : list α) :
  η (list.traverse f x) = list.traverse (@η _ ∘ f) x :=
by induction x; simp! * with functor_norm
open nat

instance : is_lawful_traversable.{u} list :=
{ id_traverse := @list.id_traverse,
  comp_traverse := @list.comp_traverse,
  traverse_eq_map_id := @list.traverse_eq_map_id,
  naturality := @list.naturality,
  .. list.is_lawful_monad }
end

section traverse
variables {α' β' : Type u} (f : α' → F β')

@[simp] lemma traverse_nil : traverse f ([] : list α') = (pure [] : F (list β')) := rfl

@[simp] lemma traverse_cons (a : α') (l : list α') :
  traverse f (a :: l) = (::) <$> f a <*> traverse f l := rfl

variables [is_lawful_applicative F]

@[simp] lemma traverse_append :
  ∀ (as bs : list α'), traverse f (as ++ bs) = (++) <$> traverse f as <*> traverse f bs
| [] bs :=
  have has_append.append ([] : list β') = id, by funext; refl,
  by simp [this] with functor_norm
| (a :: as) bs := by simp [traverse_append as bs] with functor_norm; congr

lemma mem_traverse {f : α' → set β'} :
  ∀(l : list α') (n : list β'), n ∈ traverse f l ↔ forall₂ (λb a, b ∈ f a) n l
| []      []      := by simp
| (a::as) []      := by simp
| []      (b::bs) := by simp
| (a::as) (b::bs) := by simp [mem_traverse as bs]

end traverse

end list

namespace sum

section traverse
variables {σ : Type u}
variables {F G : Type u → Type u}
variables [applicative F] [applicative G]

open applicative functor
open list (cons)

protected lemma traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : σ ⊕ α) :
  sum.traverse f (g <$> x) = sum.traverse (f ∘ g) x :=
by cases x; simp [sum.traverse, id_map] with functor_norm; refl

variables [is_lawful_applicative F] [is_lawful_applicative G]

protected lemma id_traverse {σ α} (x : σ ⊕ α) : sum.traverse id.mk x = x :=
by cases x; refl

@[nolint unused_arguments]
protected lemma comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : σ ⊕ α) :
  sum.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (sum.traverse f <$> sum.traverse g x) :=
by cases x; simp! [sum.traverse,map_id] with functor_norm; refl

protected lemma traverse_eq_map_id {α β} (f : α → β) (x : σ ⊕ α) :
  sum.traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by induction x; simp! * with functor_norm; refl

protected lemma map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : σ ⊕ α) :
  (<$>) f <$> sum.traverse g x = sum.traverse ((<$>) f ∘ g) x :=
by cases x; simp [sum.traverse, id_map] with functor_norm; congr; refl

variable (η : applicative_transformation F G)

protected lemma naturality {α β} (f : α → F β) (x : σ ⊕ α) :
  η (sum.traverse f x) = sum.traverse (@η _ ∘ f) x :=
by cases x; simp! [sum.traverse] with functor_norm

end traverse

instance {σ : Type u} : is_lawful_traversable.{u} (sum σ) :=
{ id_traverse := @sum.id_traverse σ,
  comp_traverse := @sum.comp_traverse σ,
  traverse_eq_map_id := @sum.traverse_eq_map_id σ,
  naturality := @sum.naturality σ,
  .. sum.is_lawful_monad }

end sum
