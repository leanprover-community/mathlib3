/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Fold on finite sets
-/
import data.list.set data.list.perm tactic.finish data.finset.basic
open list subtype nat finset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list

@[congr] lemma map_congr {f g : α → β} : ∀ {l : list α}, (∀ x ∈ l, f x = g x) → map f l = map g l
| [] _     := rfl
| (a::l) h :=
  have f a = g a, from h _ (mem_cons_self _ _),
  have map f l = map g l, from map_congr $ assume a', h _ ∘ mem_cons_of_mem _,
  show f a :: map f l = g a :: map g l, by simp [*]

variables {op : α → α → α} [ha : is_associative α op] [hc : is_commutative α op]
local notation a * b := op a b
local notation l <*> a := foldl op a l

section associative
include ha

lemma foldl_assoc : ∀{l : list α} {a₁ a₂}, l <*> (a₁ * a₂) = a₁ * (l <*> a₂)
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ :=
  calc a::l <*> (a₁ * a₂) = l <*> (a₁ * (a₂ * a)) : by simp [ha.assoc]
    ... = a₁ * (a::l <*> a₂) : by rw [foldl_assoc]; simp

lemma foldl_op_eq_op_foldr_assoc : ∀{l : list α} {a₁ a₂}, (l <*> a₁) * a₂ = a₁ * l.foldr (*) a₂
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ := by simp [foldl_assoc, ha.assoc]; rw [foldl_op_eq_op_foldr_assoc]
end associative

section commutative
include ha hc

lemma foldl_assoc_comm_cons {l : list α} {a₁ a₂} : (a₁ :: l) <*> a₂ = a₁ * (l <*> a₂) :=
by rw [foldl_cons, hc.comm, foldl_assoc]

lemma fold_op_eq_of_perm {l₁ l₂ : list α} {a : α} (h : perm l₁ l₂) : l₁ <*> a = l₂ <*> a :=
by induction h; simp [*, -foldl_cons, foldl_assoc_comm_cons]; cc

end commutative

end list

namespace finset

section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

def fold (b : β) (f : α → β) (s : finset α) : β :=
quot.lift_on s (λl, (l.val.map f).foldl op b) (λl₁ l₂, list.fold_op_eq_of_perm ∘ perm.perm_map _)

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] lemma fold_to_finset_of_nodup {l : list α} (hl : nodup l) :
  (to_finset_of_nodup l hl).fold op b f = (l.map f).foldl op b := rfl

@[simp] lemma fold_empty : (∅:finset α).fold op b f = b := rfl

variables [decidable_eq α]

@[simp] lemma fold_insert : a ∉ s → (insert a s).fold op b f = f a * s.fold op b f :=
finset.induction_on_to_finset s $ assume l hl (h : a ∉ l),
  show ((if a ∈ l then l else a :: l).map f).foldl op b = f a * (l.map f).foldl op b,
    begin rw [if_neg h], simp [-foldl_map, -foldl_cons], exact list.foldl_assoc_comm_cons end

@[simp] lemma fold_singleton : ({a}:finset α).fold op b f = f a * b :=
calc ({a}:finset α).fold op b f = f a * (∅:finset α).fold op b f : fold_insert $ by simp
  ... = f a * b : by rw [fold_empty]

@[simp] lemma fold_image [decidable_eq γ] {g : γ → α} {s : finset γ} :
  (∀ (x ∈ s) (y ∈ s), g x = g y → x = y) → (s.image g).fold op b f = s.fold op b (f ∘ g) :=
finset.induction_on_to_finset s $ assume l hl hg, by rw [image_to_finset_of_nodup hl hg]; simp

@[congr] lemma fold_congr {g : α → β} : (∀ x ∈ s, f x = g x) → s.fold op b f = s.fold op b g :=
finset.induction_on_to_finset s $ assume l hl (hg : ∀x∈l, f x = g x),
  by simp [-foldl_map]; rw [list.map_congr hg]

lemma fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
  s.fold op (b₁ * b₂) (λx, f x * g x) = s.fold op b₁ f * s.fold op b₂ g :=
s.induction_on (by simp) (by simp {contextual := tt}; cc)

lemma fold_hom {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op']
  {m : β → γ} (hm : ∀x y, m (op x y) = op' (m x) (m y)) :
  s.fold op' (m b) (λx, m (f x)) = m (s.fold op b f) :=
s.induction_on (by simp) (by simp [hm] {contextual := tt})

lemma fold_union_inter {s₁ s₂ : finset α} {b₁ b₂ : β} :
  (s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f = s₁.fold op b₂ f * s₂.fold op b₁ f :=
s₁.induction_on
  (by simp [empty_union, empty_inter]; cc)
  (assume a s h, by by_cases a ∈ s₂; simp [*]; cc)

end fold
end finset
