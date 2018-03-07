/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances of `traversable` for types from the core library
-/

import category.traversable.basic
import category.basic
import category.functor
import category.applicative

universe variables w u v w' u' v'

open function

section identity

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

def id.traverse {α β : Type u} (g : α → f β) : id α → f (id β) := g

instance : traversable id :=
⟨ @id.traverse ⟩

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma id.id_traverse (x : id α) :
  id.traverse id.mk x = x :=
by refl
lemma id.comp_traverse (g : α → f β) (h : β → f' γ) (x : id α) :
  id.traverse (comp.mk ∘ map h ∘ g) x =
  comp.mk (id.traverse h <$> id.traverse g x) :=
by simp! [id.traverse,functor.map_id] with norm

lemma id.map_traverse
   (g : α → f' β) (f : β → γ)
   (x : id α) :
  map f <$> id.traverse g x = id.traverse (map f ∘ g) x :=
by simp [map,id.traverse,id_map] with norm

lemma id.traverse_map
   (g : α → β) (f : β → f' γ)
   (x : id α) :
  id.traverse f (g <$> x) = id.traverse (f ∘ g) x :=
by simp [map,id.traverse,id_map] with norm

variable (eta : applicative_transformation f f')

lemma id.naturality {α β : Type u}
  (F : α → f β) (x : id α) :
  eta (id.traverse F x) = id.traverse (@eta _ ∘ F) x :=
by simp! [id.traverse] with norm; refl

end identity

instance : is_lawful_traversable id :=
{ id_traverse := λ α x, @id.id_traverse α x,
  comp_traverse := @id.comp_traverse,
  map_traverse := @id.map_traverse,
  traverse_map := @id.traverse_map,
  naturality := @id.naturality }

section option

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

protected def option.traverse {α β : Type u} (g : α → f β) : option α → f (option β)
| none := pure none
| (some x) := some <$> g x

instance : traversable option :=
{ traverse := @option.traverse }

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma option.id_traverse (x : option α) :
  option.traverse id.mk x = x :=
by cases x; unfold option.traverse; refl

lemma option.comp_traverse (g : α → f β) (h : β → f' γ) :
  ∀ (x : option α),
        option.traverse (comp.mk ∘ map h ∘ g) x =
        comp.mk (option.traverse h <$> option.traverse g x) :=
by intro x; cases x; simp! with norm; refl

lemma option.map_traverse (g : α -> f' β) (f : β → γ)
  (x : option α) :
  map f <$> option.traverse g x = option.traverse (map f ∘ g) x :=
by cases x; simp! with norm; refl

lemma option.traverse_map (g : α -> β) (f : β → f' γ)
  (x : option α) :
  option.traverse f (g <$> x) = option.traverse (f ∘ g) x :=
by cases x; simp! with norm; refl

variable (eta : applicative_transformation f f')

lemma option.naturality {α β : Type u} (g : α → f β) (x : option α) :
  eta (option.traverse g x) = option.traverse (@eta _ ∘ g) x :=
by cases x with x; simp! [*] with norm

end option

instance : is_lawful_traversable option :=
{ id_traverse := @option.id_traverse,
  comp_traverse := @option.comp_traverse,
  map_traverse := @option.map_traverse,
  traverse_map := @option.traverse_map,
  naturality := @option.naturality }

section list

variables {f : Type u → Type v}
variables [applicative f]
variables {α β : Type u}

open applicative functor
open list (cons)

protected def list.traverse (g : α → f β) : list α → f (list β)
| [] := pure []
| (x :: xs) := cons <$> g x <*> list.traverse xs

end list

section list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

open applicative functor
open list (cons)

lemma list.id_traverse (xs : list α) :
  list.traverse id.mk xs = xs :=
by induction xs; simp! [*] with norm; refl

lemma list.comp_traverse (g : α → f β) (h : β → f' γ) (x : list α) :
  list.traverse (comp.mk ∘ map h ∘ g) x =
  comp.mk (list.traverse h <$> list.traverse g x) :=
by induction x; simp! [*] with norm; refl

lemma list.map_traverse {α β γ : Type u} (g : α → f' β) (f : β → γ)
  (x : list α) :
  map f <$> list.traverse g x = list.traverse (map f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih;
  simp! [*] with norm; refl
end

lemma list.traverse_map {α β γ : Type u} (g : α → β) (f : β → f' γ)
  (x : list α) :
  list.traverse f (g <$> x) = list.traverse (f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih;
  simp! [*] with norm; refl
end

variable (eta : applicative_transformation f f')

lemma list.naturality {α β : Type u} (g : α → f β) (x : list α) :
  eta (list.traverse g x) = list.traverse (@eta _ ∘ g) x :=
by induction x; simp! [*] with norm
open nat

end list

instance : traversable list :=
{ traverse := @list.traverse }

instance : is_lawful_traversable list :=
{ id_traverse := @list.id_traverse,
  comp_traverse := @list.comp_traverse,
  map_traverse := @list.map_traverse,
  traverse_map := @list.traverse_map,
  naturality := @list.naturality }

namespace sum

section traverse
variables {γ : Type u}
variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

open applicative functor
open list (cons)

protected def traverse {α β : Type u} (g : α → f β) : γ ⊕ α → f (γ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> g x

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β η : Type u}

protected lemma id_traverse (x : γ ⊕ α) :
  sum.traverse id.mk x = x :=
by cases x; refl

protected lemma comp_traverse (g : α → f β) (h : β → f' η) (x : γ ⊕ α) :
        sum.traverse (comp.mk ∘ map h ∘ g) x =
        comp.mk (sum.traverse h <$> sum.traverse g x) :=
by casesm _ ⊕ _; simp! [sum.traverse,map_id] with norm; refl

protected lemma map_traverse
   (g : α → f' β) (f : β → η)
   (x : γ ⊕ α) :
  map f <$> sum.traverse g x = sum.traverse (map f ∘ g) x :=
by casesm _ ⊕ _; simp [map,sum.mapr,sum.traverse,id_map] with norm; congr

protected lemma traverse_map
   (g : α → β) (f : β → f' η)
   (x : γ ⊕ α) :
  sum.traverse f (g <$> x) = sum.traverse (f ∘ g) x :=
by casesm _ ⊕ _; simp [map,sum.mapr,sum.traverse,id_map] with norm

variable (eta : applicative_transformation f f')

protected lemma naturality {α β : Type u}
  (F : α → f β) (x : γ ⊕ α) :
  eta (sum.traverse F x) = sum.traverse (@eta _ ∘ F) x :=
by cases x; simp! [sum.traverse] with norm; refl

end traverse

instance {γ : Type u} : traversable.{u} (sum γ) :=
{ traverse := @sum.traverse.{u} γ }

instance {γ : Type u} : is_lawful_traversable.{u} (sum γ) :=
{ id_traverse := @sum.id_traverse γ,
  comp_traverse := @sum.comp_traverse γ,
  map_traverse := @sum.map_traverse γ,
  traverse_map := @sum.traverse_map γ,
  naturality := @sum.naturality γ }

end sum
