/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Fold on finite sets
-/
import data.list.perm data.finset.basic data.sigma tactic.finish
open multiset nat finset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset

section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

def fold (b : β) (f : α → β) (s : finset α) : β := (s.1.map f).fold op b 

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] theorem fold_empty : (∅ : finset α).fold op b f = b := rfl

variables [decidable_eq α]

@[simp] theorem fold_insert (h : a ∉ s) : (insert a s).fold op b f = f a * s.fold op b f :=
by simp [fold, ndinsert_of_not_mem h]

@[simp] theorem fold_singleton : ({a}:finset α).fold op b f = f a * b :=
by simp [fold]

@[simp] theorem fold_image [decidable_eq γ] {g : γ → α} {s : finset γ}
  (H : ∀ (x ∈ s) (y ∈ s), g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) :=
by simp [fold, image_val_of_inj_on H, map_map]

@[congr] theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g :=
by rw [fold, fold, map_congr H]

theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
  s.fold op (b₁ * b₂) (λx, f x * g x) = s.fold op b₁ f * s.fold op b₂ g :=
by simp [fold, fold_distrib]

theorem fold_hom {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op']
  {m : β → γ} (hm : ∀x y, m (op x y) = op' (m x) (m y)) :
  s.fold op' (m b) (λx, m (f x)) = m (s.fold op b f) :=
by rw [fold, fold, ← fold_hom op hm, map_map]

theorem fold_union_inter {s₁ s₂ : finset α} {b₁ b₂ : β} :
  (s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f = s₁.fold op b₂ f * s₂.fold op b₁ f :=
by unfold fold; rw [← fold_add op, ← map_add, union_val,
     inter_val, union_add_inter, map_add, hc.comm, fold_add]

@[simp] theorem fold_insert_idem [hi : is_idempotent β op] :
  (insert a s).fold op b f = f a * s.fold op b f :=
by have : decidable_eq β := (λ _ _, classical.prop_decidable _);
   rw [fold, insert_val', ← fold_erase_dup_idem op, erase_dup_map_erase_dup_eq,
       fold_erase_dup_idem op]; simp [fold]

end fold

section bind
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ] {s : finset α} {t : α → finset β}

protected def bind (s : finset α) (t : α → finset β) : finset β := s.fold (∪) ∅ t

@[simp] theorem bind_empty : finset.bind ∅ t = ∅ := rfl

@[simp] theorem bind_insert {a : α} : (insert a s).bind t = t a ∪ s.bind t := fold_insert_idem

@[simp] theorem mem_bind {b : β} : b ∈ s.bind t ↔ (∃a∈s, b ∈ t a) :=
finset.induction_on s (by simp) $ assume a s has ih,
  calc b ∈ (insert a s).bind t ↔ b ∈ t a ∨ (∃a∈s, b ∈ t a) : by simp [ih]
    ... ↔ _ : by rw [bex_def, bex_def, exists_mem_insert]

theorem image_bind {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bind t = s.bind (λa, t (f a)) :=
finset.induction_on s (by simp) (by simp {contextual := tt})

theorem bind_image {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bind t).image f = s.bind (λa, (t a).image f) :=
finset.induction_on s (by simp) (by simp [image_union] {contextual := tt})

theorem bind_to_finset (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bind (λa, (t a).to_finset) :=
ext.2 $ by simp

end bind

section prod
variables [decidable_eq α] [decidable_eq β] {s : finset α} {t : finset β}

protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, nodup_product s.2 t.2⟩

@[simp] theorem product_val : (s.product t).1 = s.1.product t.1 := rfl

@[simp] theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

theorem product_eq_bind (s : finset α) (t : finset β) :
 s.product t = s.bind (λa, t.image $ λb, (a, b)) :=
ext.2 $ by simp

end prod

section sigma
variables {σ : α → Type*} [decidable_eq α] [∀a, decidable_eq (σ a)]
  {s : finset α} {t : Πa, finset (σ a)}

protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
s.bind $ λa, (t a).image $ λb, ⟨a, b⟩

theorem mem_sigma : ∀ {p : sigma σ}, p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1)
| ⟨a, b⟩ := by simp [finset.sigma]

theorem sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)} :
  s₁ ⊆ s₂ → (∀a, t₁ a ⊆ t₂ a) → s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
by simp [subset_iff, mem_sigma] {contextual := tt}

end sigma

end finset
