/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Finite types.
-/
import data.finset data.equiv
universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

class fintype (α : Type*) :=
(elems : finset α)
(complete : ∀ x : α, x ∈ elems)

namespace finset
variable [fintype α]

def univ : finset α := fintype.elems α

@[simp] theorem mem_univ [fintype α] (x : α) : x ∈ (univ : finset α) :=
fintype.complete x

@[simp] theorem mem_univ_val [fintype α] : ∀ x, x ∈ (univ : finset α).1 := mem_univ

theorem subset_univ (s : finset α) : s ⊆ univ := λ a _, mem_univ a
end finset

open finset

namespace fintype

def of_multiset [decidable_eq α] (s : multiset α)
  (H : ∀ x : α, x ∈ s) : fintype α :=
⟨s.to_finset, by simpa using H⟩

def of_list [decidable_eq α] (l : list α)
  (H : ∀ x : α, x ∈ l) : fintype α :=
⟨l.to_finset, by simpa using H⟩

instance (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr; simp [finset.ext, h₁, h₂]⟩

instance subtype {p : α → Prop} (s : finset α)
  (H : ∀ x : α, x ∈ s ↔ p x) : fintype {x // p x} :=
⟨⟨multiset.pmap subtype.mk s.1 (λ x, (H x).1),
  multiset.nodup_pmap (λ a _ b _, congr_arg subtype.val) s.2⟩,
λ ⟨x, px⟩, multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

def of_bijective [fintype α] (f : α → β) (H : function.bijective f) : fintype β :=
⟨⟨univ.1.map f, multiset.nodup_map H.1 univ.2⟩,
λ b, let ⟨a, e⟩ := H.2 b in e ▸ multiset.mem_map_of_mem _ (mem_univ _)⟩

def of_surjective [fintype α] [decidable_eq β] (f : α → β) (H : function.surjective f) : fintype β :=
⟨univ.image f, λ b, let ⟨a, e⟩ := H b in e ▸ mem_image_of_mem _ (mem_univ _)⟩

def of_equiv (α : Type*) [fintype α] (f : α ≃ β) : fintype β := of_bijective _ f.bijective 

end fintype

instance (n : ℕ) : fintype (fin n) :=
⟨⟨list.pmap fin.mk (list.range n) (λ a, list.mem_range.1),
  list.nodup_pmap (λ a _ b _, congr_arg fin.val) (list.nodup_range _)⟩,
λ ⟨m, h⟩, list.mem_pmap.2 ⟨m, list.mem_range.2 h, rfl⟩⟩

instance : fintype empty := ⟨∅, empty.rec _⟩

instance : fintype unit := ⟨⟨()::0, by simp⟩, λ ⟨⟩, by simp⟩

instance : fintype bool := ⟨⟨tt::ff::0, by simp⟩, λ x, by cases x; simp⟩

instance {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] : fintype (sigma β) :=
⟨univ.sigma (λ _, univ), λ ⟨a, b⟩, by simp⟩

instance (α β : Type*) [fintype α] [fintype β] : fintype (α × β) :=
⟨univ.product univ, λ ⟨a, b⟩, by simp⟩

instance (α : Type*) [fintype α] : fintype (ulift α) :=
fintype.of_equiv _ equiv.ulift.symm

instance (α : Type u) (β : Type v) [fintype α] [fintype β] : fintype (α ⊕ β) :=
@fintype.of_equiv _ _ (@sigma.fintype _
    (λ b, cond b (ulift.{(max u v) u} α) (ulift.{(max u v) v} β)) _
    (λ b, by cases b; apply ulift.fintype))
  ((equiv.sum_equiv_sigma_bool _ _).symm.trans
    (equiv.sum_congr equiv.ulift equiv.ulift))

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩
