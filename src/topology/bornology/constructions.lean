/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.bornology.basic

/-!
# Bornology structure on products and subtypes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `bornology` and `bounded_space` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `bornology.cobounded` and `bornology.is_bounded`
on these types.
-/

open set filter bornology function
open_locale filter

variables {α β ι : Type*} {π : ι → Type*} [fintype ι] [bornology α] [bornology β]
  [Π i, bornology (π i)]

instance : bornology (α × β) :=
{ cobounded := (cobounded α).coprod (cobounded β),
  le_cofinite := @coprod_cofinite α β ▸ coprod_mono ‹bornology α›.le_cofinite
    ‹bornology β›.le_cofinite }

instance : bornology (Π i, π i) :=
{ cobounded := filter.Coprod (λ i, cobounded (π i)),
  le_cofinite := @Coprod_cofinite ι π _ ▸ (filter.Coprod_mono $ λ i, bornology.le_cofinite _) }

/-- Inverse image of a bornology. -/
@[reducible] def bornology.induced {α β : Type*} [bornology β] (f : α → β) : bornology α :=
{ cobounded := comap f (cobounded β),
  le_cofinite := (comap_mono (bornology.le_cofinite β)).trans (comap_cofinite_le _) }

instance {p : α → Prop} : bornology (subtype p) := bornology.induced (coe : subtype p → α)

namespace bornology

/-!
### Bounded sets in `α × β`
-/

lemma cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) := rfl

lemma is_bounded_image_fst_and_snd {s : set (α × β)} :
  is_bounded (prod.fst '' s) ∧ is_bounded (prod.snd '' s) ↔ is_bounded s :=
compl_mem_coprod.symm

variables {s : set α} {t : set β} {S : Π i, set (π i)}

lemma is_bounded.fst_of_prod (h : is_bounded (s ×ˢ t)) (ht : t.nonempty) :
  is_bounded s :=
fst_image_prod s ht ▸ (is_bounded_image_fst_and_snd.2 h).1

lemma is_bounded.snd_of_prod (h : is_bounded (s ×ˢ t)) (hs : s.nonempty) :
  is_bounded t :=
snd_image_prod hs t ▸ (is_bounded_image_fst_and_snd.2 h).2

lemma is_bounded.prod (hs : is_bounded s) (ht : is_bounded t) : is_bounded (s ×ˢ t) :=
is_bounded_image_fst_and_snd.1
  ⟨hs.subset $ fst_image_prod_subset _ _, ht.subset $ snd_image_prod_subset _ _⟩

lemma is_bounded_prod_of_nonempty (hne : set.nonempty (s ×ˢ t)) :
  is_bounded (s ×ˢ t) ↔ is_bounded s ∧ is_bounded t :=
⟨λ h, ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, λ h, h.1.prod h.2⟩

lemma is_bounded_prod : is_bounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ is_bounded s ∧ is_bounded t :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hs, { simp },
  rcases t.eq_empty_or_nonempty with rfl|ht, { simp },
  simp only [hs.ne_empty, ht.ne_empty, is_bounded_prod_of_nonempty (hs.prod ht), false_or]
end

lemma is_bounded_prod_self : is_bounded (s ×ˢ s) ↔ is_bounded s :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hs, { simp },
  exact (is_bounded_prod_of_nonempty (hs.prod hs)).trans (and_self _)
end

/-!
### Bounded sets in `Π i, π i`
-/

lemma cobounded_pi : cobounded (Π i, π i) = filter.Coprod (λ i, cobounded (π i)) := rfl

lemma forall_is_bounded_image_eval_iff {s : set (Π i, π i)} :
  (∀ i, is_bounded (eval i '' s)) ↔ is_bounded s :=
compl_mem_Coprod.symm

lemma is_bounded.pi (h : ∀ i, is_bounded (S i)) : is_bounded (pi univ S) :=
forall_is_bounded_image_eval_iff.1 $ λ i, (h i).subset eval_image_univ_pi_subset

lemma is_bounded_pi_of_nonempty (hne : (pi univ S).nonempty) :
  is_bounded (pi univ S) ↔ ∀ i, is_bounded (S i) :=
⟨λ H i, @eval_image_univ_pi _ _ _ i hne ▸ forall_is_bounded_image_eval_iff.2 H i, is_bounded.pi⟩

lemma is_bounded_pi : is_bounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, is_bounded (S i) :=
begin
  by_cases hne : ∃ i, S i = ∅,
  { simp [hne, univ_pi_eq_empty_iff.2 hne] },
  { simp only [hne, false_or],
    simp only [not_exists, ← ne.def, ←nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne,
    exact is_bounded_pi_of_nonempty hne }
end

/-!
### Bounded sets in `{x // p x}`
-/

lemma is_bounded_induced {α β : Type*} [bornology β] {f : α → β} {s : set α} :
  @is_bounded α (bornology.induced f) s ↔ is_bounded (f '' s) :=
compl_mem_comap

lemma is_bounded_image_subtype_coe {p : α → Prop} {s : set {x // p x}} :
  is_bounded (coe '' s : set α) ↔ is_bounded s :=
is_bounded_induced.symm

end bornology

/-!
### Bounded spaces
-/

open bornology

instance [bounded_space α] [bounded_space β] : bounded_space (α × β) :=
by simp [← cobounded_eq_bot_iff, cobounded_prod]

instance [∀ i, bounded_space (π i)] : bounded_space (Π i, π i) :=
by simp [← cobounded_eq_bot_iff, cobounded_pi]

lemma bounded_space_induced_iff {α β : Type*} [bornology β] {f : α → β} :
  @bounded_space α (bornology.induced f) ↔ is_bounded (range f) :=
by rw [← is_bounded_univ, is_bounded_induced, image_univ]

lemma bounded_space_subtype_iff {p : α → Prop} : bounded_space (subtype p) ↔ is_bounded {x | p x} :=
by rw [bounded_space_induced_iff, subtype.range_coe_subtype]

lemma bounded_space_coe_set_iff {s : set α} : bounded_space s ↔ is_bounded s :=
bounded_space_subtype_iff

alias bounded_space_subtype_iff ↔ _ bornology.is_bounded.bounded_space_subtype
alias bounded_space_coe_set_iff ↔ _ bornology.is_bounded.bounded_space_coe

instance [bounded_space α] {p : α → Prop} : bounded_space (subtype p) :=
(is_bounded.all {x | p x}).bounded_space_subtype

/-!
### `additive`, `multiplicative`

The bornology on those type synonyms is inherited without change.
-/

instance : bornology (additive α) := ‹bornology α›
instance : bornology (multiplicative α) := ‹bornology α›
instance [bounded_space α] : bounded_space (additive α) := ‹bounded_space α›
instance [bounded_space α] : bounded_space (multiplicative α) := ‹bounded_space α›

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/

instance : bornology αᵒᵈ := ‹bornology α›
instance [bounded_space α] : bounded_space αᵒᵈ := ‹bounded_space α›
