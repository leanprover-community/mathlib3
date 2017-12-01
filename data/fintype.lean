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

def card (α) [fintype α] : ℕ := (@univ α _).card

def equiv_fin (α) [fintype α] [decidable_eq α] : trunc (α ≃ fin (card α)) :=
by unfold card finset.card; exact
quot.rec_on_subsingleton (@univ α _).1
  (λ l (h : ∀ x:α, x ∈ l) (nd : l.nodup), trunc.mk
   ⟨λ a, ⟨_, list.index_of_lt_length.2 (h a)⟩,
    λ i, l.nth_le i.1 i.2,
    λ a, by simp,
    λ ⟨i, h⟩, fin.eq_of_veq $ list.nodup_iff_nth_le_inj.1 nd _ _
      (list.index_of_lt_length.2 (list.nth_le_mem _ _ _)) h $ by simp⟩)
  mem_univ_val univ.2

theorem exists_equiv_fin (α) [fintype α] : ∃ n, nonempty (α ≃ fin n) :=
by have := classical.dec_eq α; exact ⟨card α, nonempty_of_trunc (equiv_fin α)⟩

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
    (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) _
    (λ b, by cases b; apply ulift.fintype))
  ((equiv.sum_equiv_sigma_bool _ _).symm.trans
    (equiv.sum_congr equiv.ulift equiv.ulift))

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩

instance plift.fintype (p : Prop) [decidable p] : fintype (plift p) :=
⟨if h : p then finset.singleton ⟨h⟩ else ∅, λ ⟨h⟩, by simp [h]⟩

instance Prop.fintype : fintype Prop :=
⟨⟨true::false::0, by simp [true_ne_false]⟩,
 classical.cases (by simp) (by simp)⟩
