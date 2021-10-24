/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.basic
import order.basic

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

/-- An antichain is a set such that no two distinct elements are related. -/
def is_antichain (r : α → α → Prop) (s : set α) : Prop := ∀ ⦃a b⦄, a ∈ s → b ∈ s → r a b → a = b

namespace is_antichain

lemma mono (hs : is_antichain r₁ s) (h : r₂ ≤ r₁) : is_antichain r₂ s :=
λ a b ha hb hab, hs ha hb $ h _ _ hab

protected lemma subset (hs : is_antichain r s) (h : t ⊆ s) : is_antichain r t :=
λ a b ha hb, hs (h ha) (h hb)

protected lemma is_antisymm (h : is_antichain r univ) : is_antisymm α r :=
⟨λ a b ha _, h trivial trivial ha⟩

protected lemma subsingleton [is_trichotomous α r] (h : is_antichain r s) : s.subsingleton :=
begin
  rintro a ha b hb,
  obtain hab | hab | hab := trichotomous_of r a b,
  { exact h ha hb hab },
  { exact hab },
  { exact (h hb ha hab).symm }
end

protected lemma flip (hs : is_antichain r s) : is_antichain (flip r) s :=
λ a b ha hb h, (hs hb ha h).symm

lemma swap (hs : is_antichain r s) : is_antichain (swap r) s := hs.flip

lemma image (hs : is_antichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
  is_antichain r' (f '' s) :=
begin
  rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ hbc,
  exact congr_arg f (hs hb hc $ h hbc),
end

lemma preimage (hs : is_antichain r s) {f : β → α} (hf : injective f)
  (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) :
  is_antichain r' (f ⁻¹' s) :=
λ b c hb hc hbc, hf $ hs hb hc $ h hbc

protected lemma insert (hs : is_antichain r s) (hl : ∀ ⦃b⦄, b ∈ s → ¬ r b a)
  (hr : ∀ ⦃b⦄, b ∈ s → ¬ r a b) :
  is_antichain r (insert a s) :=
begin
  rintro b c hb hc,
  rw mem_insert_iff at hb hc,
  obtain rfl | hb := hb; obtain rfl | hc := hc,
  { exact λ _, rfl },
  { exact λ hbc, (hr hc hbc).elim },
  { exact λ hbc, (hl hb hbc).elim },
  { exact hs hb hc }
end

lemma insert_of_symmetric (hs : is_antichain r s) (hr : symmetric r) (h : ∀ ⦃b⦄, b ∈ s → ¬ r a b) :
  is_antichain r (insert a s) :=
hs.insert (λ b hb hba, h hb $ hr hba) h

lemma insert_of_is_symm [is_symm α r] (hs : is_antichain r s) (h : ∀ ⦃b⦄, b ∈ s → ¬ r a b) :
  is_antichain r (insert a s) :=
hs.insert (λ b hb hba, h hb $ symm hba) h

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
protected def mk (r : α → α → Prop) (s : set α) : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → a = b}

lemma mk_is_antichain (r : α → α → Prop) (s : set α) : is_antichain r (is_antichain.mk r s) :=
λ a b ha hb, ha.2 hb.1

lemma mk_subset : is_antichain.mk r s ⊆ s := sep_subset _ _

lemma mk_max (ht : is_antichain r t) (h : is_antichain.mk r s ⊆ t)
  (hs : ∀ a, ∃ b ∈ is_antichain.mk r s, r a b) :
  t = is_antichain.mk r s :=
begin
  refine subset.antisymm (λ a ha, _) h,
  obtain ⟨b, hb, hab⟩ := hs a,
  rwa ht ha (h hb) hab,
end

end is_antichain
