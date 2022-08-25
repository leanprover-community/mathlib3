/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import order.filter.basic
import data.pfun

/-!
# `tendsto` for relations and partial functions

This file generalizes `filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `function.graph f`.

A partial function `f : α →. β` can be considered as the relation `rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`pfun.graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `filter` definitions from functions to partial
functions and relations.

## Notes

`set.preimage` can be generalized to relations in two ways:
* `rel.preimage` returns the image of the set under the inverse relation.
* `rel.core` returns the set of elements that are only related to those in the set.
Both generalizations are sensible in the context of filters, so `filter.comap` and `filter.tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/

universes u v w
namespace filter
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale filter

/-! ### Relations -/

/-- The forward map of a filter under a relation. Generalization of `filter.map` to relations. Note
that `rel.core` generalizes `set.preimage`. -/
def rmap (r : rel α β) (l : filter α) : filter β :=
{ sets             := {s | r.core s ∈ l},
  univ_sets        := by simp,
  sets_of_superset := λ s t hs st, mem_of_superset hs $ rel.core_mono _ st,
  inter_sets       := λ s t hs ht, by simp [rel.core_inter, inter_mem hs ht] }

theorem rmap_sets (r : rel α β) (l : filter α) : (l.rmap r).sets = r.core ⁻¹' l.sets := rfl

@[simp]
theorem mem_rmap (r : rel α β) (l : filter α) (s : set β) :
  s ∈ l.rmap r ↔ r.core s ∈ l :=
iff.rfl

@[simp]
theorem rmap_rmap (r : rel α β) (s : rel β γ) (l : filter α) :
  rmap s (rmap r l) = rmap (r.comp s) l :=
filter_eq $
by simp [rmap_sets, set.preimage, rel.core_comp]

@[simp]
lemma rmap_compose (r : rel α β) (s : rel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
funext $ rmap_rmap _ _

/-- Generic "limit of a relation" predicate. `rtendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-core of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to relations. -/
def rtendsto (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁.rmap r ≤ l₂

theorem rtendsto_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ ∀ s ∈ l₂, r.core s ∈ l₁ :=
iff.rfl

/-- One way of taking the inverse map of a filter under a relation. One generalization of
`filter.comap` to relations. Note that `rel.core` generalizes `set.preimage`. -/
def rcomap (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.core s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem, set.subset_univ _⟩,
  sets_of_superset := λ a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', ma'a.trans ab⟩,
  inter_sets       := λ a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
                        ⟨a' ∩ b', inter_mem ha₁ hb₁,
                          (r.core_inter a' b').subset.trans (set.inter_subset_inter ha₂ hb₂)⟩ }

theorem rcomap_sets (r : rel α β) (f : filter β) :
  (rcomap r f).sets = rel.image (λ s t, r.core s ⊆ t) f.sets := rfl


theorem rcomap_rcomap (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap r (rcomap s l) = rcomap (r.comp s) l :=
filter_eq $
begin
  ext t, simp [rcomap_sets, rel.image, rel.core_comp], split,
  { rintros ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, set.subset.trans (rel.core_mono _ hv) h⟩ },
  rintros ⟨t, tsets, ht⟩,
  exact ⟨rel.core s t, ⟨t, tsets, set.subset.rfl⟩, ht⟩
end

@[simp]
lemma rcomap_compose (r : rel α β) (s : rel β γ) : rcomap r ∘ rcomap s = rcomap (r.comp s) :=
funext $ rcomap_rcomap _ _

theorem rtendsto_iff_le_rcomap (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r :=
begin
  rw rtendsto_def,
  change (∀ (s : set β), s ∈ l₂.sets → r.core s ∈ l₁) ↔ l₁ ≤ rcomap r l₂,
  simp [filter.le_def, rcomap, rel.mem_image], split,
  { exact λ h s t tl₂, mem_of_superset (h t tl₂) },
  { exact λ h t tl₂, h _ t tl₂ set.subset.rfl }
end

-- Interestingly, there does not seem to be a way to express this relation using a forward map.
-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if
-- and only if `s ∈ f'`. But the intersection of two sets satisfying the lhs may be empty.

/-- One way of taking the inverse map of a filter under a relation. Generalization of `filter.comap`
to relations. -/
def rcomap' (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.preimage s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem, set.subset_univ _⟩,
  sets_of_superset := λ a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', ma'a.trans ab⟩,
  inter_sets       := λ a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
                        ⟨a' ∩ b', inter_mem ha₁ hb₁,
                         (@rel.preimage_inter _ _ r _ _).trans (set.inter_subset_inter ha₂ hb₂)⟩ }

@[simp]
lemma mem_rcomap' (r : rel α β) (l : filter β) (s : set α) :
  s ∈ l.rcomap' r ↔ ∃ t ∈ l, r.preimage t ⊆ s :=
iff.rfl

theorem rcomap'_sets (r : rel α β) (f : filter β) :
  (rcomap' r f).sets = rel.image (λ s t, r.preimage s ⊆ t) f.sets := rfl

@[simp]
theorem rcomap'_rcomap' (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
filter.ext $ λ t,
begin
  simp [rcomap'_sets, rel.image, rel.preimage_comp], split,
  { rintro ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, (rel.preimage_mono _ hv).trans h⟩ },
  rintro ⟨t, tsets, ht⟩,
  exact ⟨s.preimage t, ⟨t, tsets, set.subset.rfl⟩, ht⟩
end

@[simp]
lemma rcomap'_compose (r : rel α β) (s : rel β γ) : rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
funext $ rcomap'_rcomap' _ _

/-- Generic "limit of a relation" predicate. `rtendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to relations. -/
def rtendsto' (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap' r

theorem rtendsto'_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁ :=
begin
  unfold rtendsto' rcomap', simp [le_def, rel.mem_image], split,
  { exact λ h s hs, h _ _ hs set.subset.rfl },
  { exact λ h s t ht, mem_of_superset (h t ht) }
end

theorem tendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto (function.graph f) l₁ l₂ :=
by { simp [tendsto_def, function.graph, rtendsto_def, rel.core, set.preimage] }

theorem tendsto_iff_rtendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto' (function.graph f) l₁ l₂ :=
by { simp [tendsto_def, function.graph, rtendsto'_def, rel.preimage_def, set.preimage] }

/-! ### Partial functions -/

/-- The forward map of a filter under a partial function. Generalization of `filter.map` to partial
functions. -/
def pmap (f : α →. β) (l : filter α) : filter β :=
filter.rmap f.graph' l

@[simp]
lemma mem_pmap (f : α →. β) (l : filter α) (s : set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
iff.rfl

/-- Generic "limit of a partial function" predicate. `ptendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-core of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to partial function. -/
def ptendsto (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f.core s ∈ l₁ :=
iff.rfl

theorem ptendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α →. β) :
  ptendsto f l₁ l₂ ↔ rtendsto f.graph' l₁ l₂ :=
iff.rfl

theorem pmap_res (l : filter α) (s : set α) (f : α → β) :
  pmap (pfun.res f s) l = map f (l ⊓ 𝓟 s) :=
begin
  ext t,
  simp only [pfun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or],
  refl
end

theorem tendsto_iff_ptendsto (l₁ : filter α) (l₂ : filter β) (s : set α) (f : α → β) :
  tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ ptendsto (pfun.res f s) l₁ l₂ :=
by simp only [tendsto, ptendsto, pmap_res]

theorem tendsto_iff_ptendsto_univ (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ ptendsto (pfun.res f set.univ) l₁ l₂ :=
by { rw ← tendsto_iff_ptendsto, simp [principal_univ] }

/-- Inverse map of a filter under a partial function. One generalization of `filter.comap` to
partial functions. -/
def pcomap' (f : α →. β) (l : filter β) : filter α :=
filter.rcomap' f.graph' l

/-- Generic "limit of a partial function" predicate. `ptendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to partial functions. -/
def ptendsto' (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap' f.graph'

theorem ptendsto'_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁ :=
rtendsto'_def _ _ _

theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : filter α} {l₂ : filter β} :
  ptendsto' f l₁ l₂ → ptendsto f l₁ l₂ :=
begin
  rw [ptendsto_def, ptendsto'_def],
  exact λ h s sl₂, mem_of_superset (h s sl₂) (pfun.preimage_subset_core _ _),
end

theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : filter α} {l₂ : filter β} (h : f.dom ∈ l₁) :
  ptendsto f l₁ l₂ → ptendsto' f l₁ l₂ :=
begin
  rw [ptendsto_def, ptendsto'_def],
  intros h' s sl₂,
  rw pfun.preimage_eq,
  exact inter_mem (h' s sl₂) h
end

end filter
