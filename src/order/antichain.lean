/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.pairwise

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.adj` for `G : simple_graph α`, this corresponds to independent sets of `G`.

## Definitions

* `is_antichain r s`: Any two elements of `s : set α` are unrelated by `r : α → α → Prop`.
* `is_antichain.mk r s`: Turns `s` into an antichain by keeping only the "maximal" elements.
-/

open function set

variables {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : set α} {a : α}

protected lemma symmetric.compl (h : symmetric r) : symmetric rᶜ := λ x y hr hr', hr $ h hr'

/-- An antichain is a set such that no two distinct elements are related. -/
def is_antichain (r : α → α → Prop) (s : set α) : Prop := s.pairwise rᶜ

namespace is_antichain

protected lemma subset (hs : is_antichain r s) (h : t ⊆ s) : is_antichain r t := hs.mono h

lemma mono (hs : is_antichain r₁ s) (h : r₂ ≤ r₁) : is_antichain r₂ s := hs.mono' $ compl_le_compl h

lemma mono_on (hs : is_antichain r₁ s) (h : s.pairwise (λ ⦃a b⦄, r₂ a b → r₁ a b)) :
  is_antichain r₂ s :=
hs.imp_on $ h.imp $ λ a b h h₁ h₂, h₁ $ h h₂

lemma eq_of_related (hs : is_antichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) :
  a = b :=
of_not_not $ λ hab, hs _ ha _ hb hab h

protected lemma is_antisymm (h : is_antichain r univ) : is_antisymm α r :=
⟨λ a b ha _, h.eq_of_related trivial trivial ha⟩

protected lemma subsingleton [is_trichotomous α r] (h : is_antichain r s) : s.subsingleton :=
begin
  rintro a ha b hb,
  obtain hab | hab | hab := trichotomous_of r a b,
  { exact h.eq_of_related ha hb hab },
  { exact hab },
  { exact (h.eq_of_related hb ha hab).symm }
end

protected lemma flip (hs : is_antichain r s) : is_antichain (flip r) s :=
λ a ha b hb h, hs _ hb _ ha h.symm

lemma swap (hs : is_antichain r s) : is_antichain (swap r) s := hs.flip

lemma image (hs : is_antichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
  is_antichain r' (f '' s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr,
  exact hs _ hb _ hc (ne_of_apply_ne _ hbc) (h hr),
end

lemma preimage (hs : is_antichain r s) {f : β → α} (hf : injective f)
  (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) :
  is_antichain r' (f ⁻¹' s) :=
λ b hb c hc hbc hr, hs _ hb _ hc (hf.ne hbc) $ h hr

lemma _root_.is_antichain_insert :
  is_antichain r (insert a s) ↔ is_antichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b ∧ ¬ r b a :=
set.pairwise_insert

protected lemma insert (hs : is_antichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r b a)
  (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b) :
  is_antichain r (insert a s) :=
is_antichain_insert.2 ⟨hs, λ b hb hab, ⟨hr hb hab, hl hb hab⟩⟩

lemma _root_.is_antichain_insert_of_symmetric (hr : symmetric r) :
  is_antichain r (insert a s) ↔ is_antichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b :=
pairwise_insert_of_symmetric hr.compl

lemma insert_of_symmetric (hs : is_antichain r s) (hr : symmetric r)
  (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b) :
  is_antichain r (insert a s) :=
(is_antichain_insert_of_symmetric hr).2 ⟨hs, h⟩

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
protected def mk (r : α → α → Prop) (s : set α) : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → a = b}

lemma mk_is_antichain (r : α → α → Prop) (s : set α) : is_antichain r (is_antichain.mk r s) :=
λ a ha b hb hab h, hab $ ha.2 hb.1 h

lemma mk_subset : is_antichain.mk r s ⊆ s := sep_subset _ _

/-- If `is_antichain.mk r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
lemma mk_max (ht : is_antichain r t) (h : is_antichain.mk r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ is_antichain.mk r s, r a b) :
  t = is_antichain.mk r s :=
begin
  refine subset.antisymm (λ a ha, _) h,
  obtain ⟨b, hb, hr⟩ := hs ha,
  rwa of_not_not (λ hab, ht _ ha _ (h hb) hab hr),
end

end is_antichain

lemma set.subsingleton.is_antichain (hs : s.subsingleton) (r : α → α → Prop): is_antichain r s :=
hs.pairwise _
