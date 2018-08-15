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

universes u v

open function

section identity

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']


instance : traversable id :=
⟨ λ _ _ _ _, id ⟩

variables [is_lawful_applicative f] [is_lawful_applicative f']

lemma id.id_traverse {α : Type*} (x : id α) :
  traverse id.mk x = x :=
rfl

lemma id.comp_traverse {α β γ : Type*} (g : α → f β) (h : β → f' γ) (x : id α) :
  traverse (comp.mk ∘ (<$>) h ∘ g) x =
  comp.mk (traverse h <$> traverse g x) :=
by simp! [traverse,functor.map_id] with functor_norm

lemma id.map_traverse {α β γ : Type*}
   (g : α → f' β) (f : β → γ)
   (x : id α) :
  (<$>) f <$> traverse g x = traverse ((<$>) f ∘ g) x :=
by simp [(<$>),id_bind,traverse] with functor_norm

lemma id.traverse_map {α β γ : Type*}
   (g : α → β) (f : β → f' γ)
   (x : id α) :
  traverse f (g <$> x) = traverse (f ∘ g) x :=
by simp [(<$>),id_bind,traverse] with functor_norm

variable (η : applicative_transformation f f')

lemma id.naturality {α β : Type*}
  (F : α → f β) (x : id α) :
  η (traverse F x) = traverse (@η _ ∘ F) x :=
by simp! [traverse] with functor_norm; refl

end identity

instance : is_lawful_traversable id :=
{ id_traverse := λ α x, @id.id_traverse α x,
  comp_traverse := @id.comp_traverse,
  map_traverse := @id.map_traverse,
  traverse_map := @id.traverse_map,
  naturality := @id.naturality }

section option

open function functor

section inst

variables {f : Type u → Type v} [applicative f]

instance : traversable option :=
{ traverse := @option.traverse }

end inst

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

variables [is_lawful_applicative f] [is_lawful_applicative f']

lemma option.id_traverse {α : Type*} (x : option α) :
  option.traverse id.mk x = x :=
by cases x; unfold option.traverse; refl

lemma option.comp_traverse {α β γ : Type*} (g : α → f β) (h : β → f' γ) :
  ∀ (x : option α),
        option.traverse (comp.mk ∘ (<$>) h ∘ g) x =
        comp.mk (option.traverse h <$> option.traverse g x) :=
by intro x; cases x; simp! with functor_norm; refl

lemma option.map_traverse {α β γ : Type*} (g : α -> f β) (h : β → γ)
  (x : option α) :
  option.map h <$> option.traverse g x = option.traverse ((<$>) h ∘ g) x :=
by cases x; simp! with functor_norm; refl

lemma option.traverse_map {α β γ : Type*} (g : α -> β) (f : β → f' γ)
  (x : option α) :
  option.traverse f (g <$> x) = option.traverse (f ∘ g) x :=
by cases x; simp! with functor_norm; refl

variable (η : applicative_transformation f f')

lemma option.naturality {α β : Type*} (g : α → f β) (x : option α) :
  η (option.traverse g x) = option.traverse (@η _ ∘ g) x :=
by cases x with x; simp! [*] with functor_norm

end option

instance : is_lawful_traversable option :=
{ id_traverse := @option.id_traverse,
  comp_traverse := @option.comp_traverse,
  map_traverse := @option.map_traverse,
  traverse_map := @option.traverse_map,
  naturality := @option.naturality }

section list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables [is_lawful_applicative f] [is_lawful_applicative f']

open applicative functor
open list (cons)

lemma list.id_traverse {α : Type*}
  (xs : list α) :
  list.traverse id.mk xs = xs :=
by induction xs; simp! [*] with functor_norm; refl

lemma list.comp_traverse {α β γ : Type*}
  (g : α → f β) (h : β → f' γ) (x : list α) :
  list.traverse (comp.mk ∘ (<$>) h ∘ g) x =
  comp.mk (list.traverse h <$> list.traverse g x) :=
by induction x; simp! [*] with functor_norm; refl

lemma list.map_traverse {α β γ : Type*}
  (g : α → f' β) (f : β → γ)
  (x : list α) :
  (<$>) f <$> list.traverse g x = list.traverse ((<$>) f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih;
  simp! [*] with functor_norm; refl
end

lemma list.traverse_map {α β γ : Type*}
  (g : α → β) (f : β → f' γ)
  (x : list α) :
  list.traverse f (g <$> x) = list.traverse (f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih;
  simp! [*] with functor_norm; refl
end

variable (η : applicative_transformation f f')

lemma list.naturality {α β : Type*} (g : α → f β) (x : list α) :
  η (list.traverse g x) = list.traverse (@η _ ∘ g) x :=
by induction x; simp! [*] with functor_norm
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

protected def traverse {α β : Type*} (g : α → f β) : γ ⊕ α → f (γ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> g x

variables [is_lawful_applicative f] [is_lawful_applicative f']

protected lemma id_traverse {φ α : Type*} (x : φ ⊕ α) :
  sum.traverse id.mk x = x :=
by cases x; refl

protected lemma comp_traverse {α β φ : Type*} (g : α → f β) (h : β → f' φ) (x : γ ⊕ α) :
        sum.traverse (comp.mk ∘ (<$>) h ∘ g) x =
        comp.mk (sum.traverse h <$> sum.traverse g x) :=
by casesm _ ⊕ _; simp! [sum.traverse,map_id] with functor_norm; refl

protected lemma map_traverse {α β φ : Type*}
   (g : α → f' β) (f : β → φ)
   (x : γ ⊕ α) :
  (<$>) f <$> sum.traverse g x = sum.traverse ((<$>) f ∘ g) x :=
by casesm _ ⊕ _; simp [(<$>),sum.mapr,sum.traverse,id_map] with functor_norm; congr

protected lemma traverse_map {α : Type u} {β φ : Type*}
   (g : α → β) (f : β → f' φ)
   (x : γ ⊕ α) :
  sum.traverse f (g <$> x) = sum.traverse (f ∘ g) x :=
by casesm _ ⊕ _; simp [(<$>),sum.mapr,sum.traverse,id_map] with functor_norm

variable (η : applicative_transformation f f')

protected lemma naturality {α β : Type*}
  (F : α → f β) (x : γ ⊕ α) :
  η (sum.traverse F x) = sum.traverse (@η _ ∘ F) x :=
by cases x; simp! [sum.traverse] with functor_norm; refl

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
