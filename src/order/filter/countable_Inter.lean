/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import order.filter.basic
import data.set.countable

/-!
# Filters with countable intersection property

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.metric_space.baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.

We reformulate the definition in terms of indexed intersection and in terms of `filter.eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `filter.principal`, `filter.map`,
`filter.comap`, `has_inf.inf`). We also provide a custom constructor `filter.of_countable_Inter`
that deduces two axioms of a `filter` from the countable intersection property.

## Tags
filter, countable
-/

open set filter
open_locale filter

variables {ι : Sort*} {α β : Type*}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class countable_Inter_filter (l : filter α) : Prop :=
(countable_sInter_mem' :
  ∀ {S : set (set α)} (hSc : S.countable) (hS : ∀ s ∈ S, s ∈ l), ⋂₀ S ∈ l)

variables {l : filter α} [countable_Inter_filter l]

lemma countable_sInter_mem {S : set (set α)} (hSc : S.countable) :
  ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
⟨λ hS s hs, mem_of_superset hS (sInter_subset_of_mem hs),
  countable_Inter_filter.countable_sInter_mem' hSc⟩

lemma countable_Inter_mem [countable ι] {s : ι → set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_range_iff

lemma countable_bInter_mem {ι : Type*} {S : set ι} (hS : S.countable) {s : Π i ∈ S, set α} :
  (⋂ i ∈ S, s i ‹_›) ∈ l ↔  ∀ i ∈ S, s i ‹_› ∈ l :=
begin
  rw [bInter_eq_Inter],
  haveI := hS.to_encodable,
  exact countable_Inter_mem.trans subtype.forall
end

lemma eventually_countable_forall [countable ι] {p : α → ι → Prop} :
  (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i :=
by simpa only [filter.eventually, set_of_forall]
  using @countable_Inter_mem _ _ l _ _ (λ i, {x | p x i})

lemma eventually_countable_ball {ι : Type*} {S : set ι} (hS : S.countable)
  {p : Π (x : α) (i ∈ S), Prop} :
  (∀ᶠ x in l, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᶠ x in l, p x i ‹_› :=
by simpa only [filter.eventually, set_of_forall]
  using @countable_bInter_mem _ l _ _ _ hS (λ i hi, {x | p x i hi})

lemma eventually_le.countable_Union [countable ι] {s t : ι → set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
  (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
(eventually_countable_forall.2 h).mono $ λ x hst hs, mem_Union.2 $
  (mem_Union.1 hs).imp hst

lemma eventually_eq.countable_Union [countable ι] {s t : ι → set α} (h : ∀ i, s i =ᶠ[l] t i) :
  (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
(eventually_le.countable_Union (λ i, (h i).le)).antisymm
  (eventually_le.countable_Union (λ i, (h i).symm.le))

lemma eventually_le.countable_bUnion {ι : Type*} {S : set ι} (hS : S.countable)
  {s t : Π i ∈ S, set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
  (⋃ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
begin
  simp only [bUnion_eq_Union],
  haveI := hS.to_encodable,
  exact eventually_le.countable_Union (λ i, h i i.2)
end

lemma eventually_eq.countable_bUnion {ι : Type*} {S : set ι} (hS : S.countable)
  {s t : Π i ∈ S, set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
  (⋃ i ∈ S, s i ‹_›) =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
(eventually_le.countable_bUnion hS (λ i hi, (h i hi).le)).antisymm
  (eventually_le.countable_bUnion hS (λ i hi, (h i hi).symm.le))

lemma eventually_le.countable_Inter [countable ι] {s t : ι → set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
  (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
(eventually_countable_forall.2 h).mono $ λ x hst hs, mem_Inter.2 $ λ i, hst _ (mem_Inter.1 hs i)

lemma eventually_eq.countable_Inter [countable ι] {s t : ι → set α} (h : ∀ i, s i =ᶠ[l] t i) :
  (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
(eventually_le.countable_Inter (λ i, (h i).le)).antisymm
  (eventually_le.countable_Inter (λ i, (h i).symm.le))

lemma eventually_le.countable_bInter {ι : Type*} {S : set ι} (hS : S.countable)
  {s t : Π i ∈ S, set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
  (⋂ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
begin
  simp only [bInter_eq_Inter],
  haveI := hS.to_encodable,
  exact eventually_le.countable_Inter (λ i, h i i.2)
end

lemma eventually_eq.countable_bInter {ι : Type*} {S : set ι} (hS : S.countable)
 {s t : Π i ∈ S, set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
 (⋂ i ∈ S, s i ‹_›) =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
(eventually_le.countable_bInter hS (λ i hi, (h i hi).le)).antisymm
  (eventually_le.countable_bInter hS (λ i hi, (h i hi).symm.le))

/-- Construct a filter with countable intersection property. This constructor deduces
`filter.univ_sets` and `filter.inter_sets` from the countable intersection property. -/
def filter.of_countable_Inter (l : set (set α))
  (hp : ∀ S : set (set α), S.countable → S ⊆ l → (⋂₀ S) ∈ l)
  (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
  filter α :=
{ sets := l,
  univ_sets := @sInter_empty α ▸ hp _ countable_empty (empty_subset _),
  sets_of_superset := h_mono,
  inter_sets := λ s t hs ht, sInter_pair s t ▸
    hp _ ((countable_singleton _).insert _) (insert_subset.2 ⟨hs, singleton_subset_iff.2 ht⟩) }

instance filter.countable_Inter_of_countable_Inter (l : set (set α))
  (hp : ∀ S : set (set α), S.countable → S ⊆ l → (⋂₀ S) ∈ l)
  (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
  countable_Inter_filter (filter.of_countable_Inter l hp h_mono) := ⟨hp⟩

@[simp] lemma filter.mem_of_countable_Inter {l : set (set α)}
  (hp : ∀ S : set (set α), S.countable → S ⊆ l → (⋂₀ S) ∈ l)
  (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) {s : set α} :
  s ∈ filter.of_countable_Inter l hp h_mono ↔ s ∈ l :=
iff.rfl

instance countable_Inter_filter_principal (s : set α) : countable_Inter_filter (𝓟 s) :=
⟨λ S hSc hS, subset_sInter hS⟩

instance countable_Inter_filter_bot : countable_Inter_filter (⊥ : filter α) :=
by { rw ← principal_empty, apply countable_Inter_filter_principal }

instance countable_Inter_filter_top : countable_Inter_filter (⊤ : filter α) :=
by { rw ← principal_univ, apply countable_Inter_filter_principal }

instance (l : filter β) [countable_Inter_filter l] (f : α → β) :
  countable_Inter_filter (comap f l) :=
begin
  refine ⟨λ S hSc hS, _⟩,
  choose! t htl ht using hS,
  have : (⋂ s ∈ S, t s) ∈ l, from (countable_bInter_mem hSc).2 htl,
  refine ⟨_, this, _⟩,
  simpa [preimage_Inter] using (Inter₂_mono ht)
end

instance (l : filter α) [countable_Inter_filter l] (f : α → β) :
  countable_Inter_filter (map f l) :=
begin
  constructor, intros S hSc hS,
  simp only [mem_map, sInter_eq_bInter, preimage_Inter₂] at hS ⊢,
  exact (countable_bInter_mem hSc).2 hS
end

/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countable_Inter_filter_inf (l₁ l₂ : filter α) [countable_Inter_filter l₁]
  [countable_Inter_filter l₂] :
  countable_Inter_filter (l₁ ⊓ l₂) :=
begin
  refine ⟨λ S hSc hS, _⟩,
  choose s hs t ht hst using hS,
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs,
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht,
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter $ λ i hi, _),
  rw hst i hi,
  apply inter_subset_inter ; exact Inter_subset_of_subset i (Inter_subset _ _)
end

/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
instance countable_Inter_filter_sup (l₁ l₂ : filter α) [countable_Inter_filter l₁]
  [countable_Inter_filter l₂] :
  countable_Inter_filter (l₁ ⊔ l₂) :=
begin
  refine ⟨λ S hSc hS, ⟨_, _⟩⟩; refine (countable_sInter_mem hSc).2 (λ s hs, _),
  exacts [(hS s hs).1, (hS s hs).2]
end
