/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Fold on finite sets
-/
import data.list.set data.list.perm data.finset.basic data.sigma tactic.finish
open list subtype nat finset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section logic

lemma heq_iff_eq {a₁ a₂ : α} : a₁ == a₂ ↔ a₁ = a₂ :=
iff.intro eq_of_heq heq_of_eq

end logic

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

@[simp] lemma fold_insert_idem [hi : is_idempotent β op] :
  (insert a s).fold op b f = f a * s.fold op b f :=
if h : a ∈ s then
  calc (insert a s).fold op b f = (insert a (s.erase a)).fold op b f : by simp [insert_erase, h]
    ... = (f a * f a) * (s.erase a).fold op b f : by rw [fold_insert, hi.idempotent]; simp
    ... = f a * (insert a (s.erase a)).fold op b f : by rw [fold_insert]; simp [ha.assoc]
    ... = f a * s.fold op b f : by simp [insert_erase, h]
else
  fold_insert h

end fold

section bind
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ] {s : finset α} {t : α → finset β}

protected def bind (s : finset α) (t : α → finset β) : finset β := s.fold (∪) ∅ t

@[simp] lemma bind_empty : finset.bind ∅ t = ∅ := rfl

@[simp] lemma bind_insert {a : α} : (insert a s).bind t = t a ∪ s.bind t := fold_insert_idem

lemma mem_bind_iff {b : β} : b ∈ s.bind t ↔ (∃a∈s, b ∈ t a) :=
s.induction_on (by simp [not_exists]) $ assume a s has ih,
  calc b ∈ (insert a s).bind t ↔ b ∈ t a ∨ (∃a∈s, b ∈ t a) : by simp [ih]
    ... ↔ _ : by rw [bex_def, bex_def, exists_mem_insert_iff]

lemma image_bind {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bind t = s.bind (λa, t (f a)) :=
s.induction_on (by simp) (by simp {contextual := tt})

lemma bind_image {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bind t).image f = s.bind (λa, (t a).image f) :=
s.induction_on (by simp) (by simp [image_union] {contextual := tt})

end bind

section prod
variables [decidable_eq α] [decidable_eq β] {s : finset α} {t : finset β}

protected def product (s : finset α) (t : finset β) : finset (α × β) :=
s.bind $ λa, t.image $ λb, (a, b)

lemma mem_product_iff : ∀{p : α × β}, p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
by simp [finset.product, mem_bind_iff, mem_image_iff]

end prod

section sigma
variables {σ : α → Type*} [decidable_eq α] [∀a, decidable_eq (σ a)]
  {s : finset α} {t : Πa, finset (σ a)}

protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
s.bind $ λa, (t a).image $ λb, ⟨a, b⟩

lemma mem_sigma_iff {p : sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) :=
by cases p with a b;
   simp [finset.sigma, mem_bind_iff, mem_image_iff, iff_def, sigma.mk_eq_mk_iff, heq_iff_eq]
        {contextual := tt}

lemma sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)} :
  s₁ ⊆ s₂ → (∀a, t₁ a ⊆ t₂ a) → s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
by simp [subset_iff, mem_sigma_iff] {contextual := tt}

end sigma

end finset
