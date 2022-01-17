/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import topology.basic
/-
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhds_set s` consisting of all neighborhoods of a set
`s`.
-/

open set filter
open_locale topological_space

variables {α : Type*} [topological_space α] {s t s₁ s₂ t₁ t₂ : set α} {x : α}

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set α) : filter α :=
Sup (nhds '' s)

localized "notation `𝓝ˢ` := nhds_set" in topological_space

lemma mem_nhds_set_iff : t ∈ 𝓝ˢ s ↔ ∀ (x : α), x ∈ s → t ∈ 𝓝 x :=
by simp_rw [nhds_set, filter.mem_Sup, ball_image_iff]

lemma subset_interior_iff_mem_nhds_set : s ⊆ interior t ↔ t ∈ 𝓝ˢ s :=
by simp_rw [mem_nhds_set_iff, subset_interior_iff_nhds]

lemma mem_nhds_set : s ∈ 𝓝ˢ t ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma is_open.mem_nhds_set (hU : is_open t) : t ∈ 𝓝ˢ s ↔ s ⊆ t :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

@[simp] lemma nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x :=
by { ext,
     rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff] }

lemma mem_nhds_set_interior : s ∈ 𝓝ˢ (interior s) :=
subset_interior_iff_mem_nhds_set.mp subset.rfl

lemma mem_nhds_set_empty : s ∈ 𝓝ˢ (∅ : set α) :=
subset_interior_iff_mem_nhds_set.mp $ empty_subset _

lemma nhds_set_empty : 𝓝ˢ (∅ : set α) = ⊥ :=
by { ext, simp [mem_nhds_set_empty] }

lemma nhds_set_univ : 𝓝ˢ (univ : set α) = ⊤ :=
by { ext, rw [← subset_interior_iff_mem_nhds_set, univ_subset_iff, interior_eq_univ, mem_top] }

lemma monotone_nhds_set : monotone (𝓝ˢ : set α → filter α) :=
by { intros s t hst O, simp_rw [← subset_interior_iff_mem_nhds_set], exact subset.trans hst }

lemma union_mem_nhds_set (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) :=
begin
  rw [← subset_interior_iff_mem_nhds_set] at *,
  exact union_subset
    (h₁.trans $ interior_mono $ subset_union_left _ _)
    (h₂.trans $ interior_mono $ subset_union_right _ _)
end
