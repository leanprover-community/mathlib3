/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import order.filter.basic
import data.set.countable

/-!
# Filters with countable intersection property

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.metric_space.baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.
-/

open set filter

variables {ι α : Type*}

/-- A filter `l` has countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class countable_Inter_filter (l : filter α) : Prop :=
(countable_sInter_mem_sets' :
  ∀ {S : set (set α)} (hSc : countable S) (hS : ∀ s ∈ S, s ∈ l), ⋂₀ S ∈ l)

variables {l : filter α} [countable_Inter_filter l]

lemma countable_sInter_mem_sets {S : set (set α)} (hSc : countable S) :
  ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
⟨λ hS s hs, mem_sets_of_superset hS (sInter_subset_of_mem hs),
  countable_Inter_filter.countable_sInter_mem_sets' hSc⟩

lemma countable_Inter_mem_sets [encodable ι] {s : ι → set α} :
  (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
sInter_range s ▸ (countable_sInter_mem_sets (countable_range _)).trans forall_range_iff

lemma countable_bInter_mem_sets {S : set ι} (hS : countable S) {s : Π i ∈ S, set α} :
  (⋂ i ∈ S, s i ‹_›) ∈ l ↔  ∀ i ∈ S, s i ‹_› ∈ l :=
begin
  rw [bInter_eq_Inter],
  haveI := hS.to_encodable,
  exact countable_Inter_mem_sets.trans subtype.forall
end

lemma eventually_countable_forall [encodable ι] {p : α → ι → Prop} :
  (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i :=
by simpa only [filter.eventually, set_of_forall]
  using @countable_Inter_mem_sets _ _ l _ _ (λ i, {x | p x i})

lemma eventually_countable_ball {S : set ι} (hS : countable S) {p : Π (x : α) (i ∈ S), Prop} :
  (∀ᶠ x in l, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᶠ x in l, p x i ‹_› :=
by simpa only [filter.eventually, set_of_forall]
  using @countable_bInter_mem_sets _ _ l _ _ hS (λ i hi, {x | p x i hi})

instance countable_Inter_filter_principal (s : set α) : countable_Inter_filter (principal s) :=
⟨λ S hSc hS, subset_sInter hS⟩

instance countable_Inter_filter_bot : countable_Inter_filter (⊥ : filter α) :=
by { rw ← principal_empty, apply countable_Inter_filter_principal }

instance countable_Inter_filter_top : countable_Inter_filter (⊤ : filter α) :=
by { rw ← principal_univ, apply countable_Inter_filter_principal }
