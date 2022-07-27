/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import topology.basic
/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhds_set s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhds_set`
* `∀ (x : α), x ∈ t → s ∈ 𝓝 x` using `mem_nhds_set_iff_forall`
* `∃ U : set α, is_open U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhds_set_iff_exists`

Furthermore, we have the following results:
* `monotone_nhds_set`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ`is strictly monotone and hence injective:
  `strict_mono_nhds_set`/`injective_nhds_set`. These results are in `topology.separation`.
-/

open set filter
open_locale topological_space

variables {α β : Type*} [topological_space α] [topological_space β]
  {s t s₁ s₂ t₁ t₂ : set α} {x : α}

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set α) : filter α :=
Sup (nhds '' s)

localized "notation `𝓝ˢ` := nhds_set" in topological_space

lemma mem_nhds_set_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ (x : α), x ∈ t → s ∈ 𝓝 x :=
by simp_rw [nhds_set, filter.mem_Sup, ball_image_iff]

lemma subset_interior_iff_mem_nhds_set : s ⊆ interior t ↔ t ∈ 𝓝ˢ s :=
by simp_rw [mem_nhds_set_iff_forall, subset_interior_iff_nhds]

lemma mem_nhds_set_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : set α, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma has_basis_nhds_set (s : set α) : (𝓝ˢ s).has_basis (λ U, is_open U ∧ s ⊆ U) (λ U, U) :=
⟨λ t, by simp [mem_nhds_set_iff_exists, and_assoc]⟩

lemma is_open.mem_nhds_set (hU : is_open s) : s ∈ 𝓝ˢ t ↔ t ⊆ s :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

@[simp] lemma nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x :=
by { ext,
     rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff] }

lemma mem_nhds_set_interior : s ∈ 𝓝ˢ (interior s) :=
subset_interior_iff_mem_nhds_set.mp subset.rfl

lemma mem_nhds_set_empty : s ∈ 𝓝ˢ (∅ : set α) :=
subset_interior_iff_mem_nhds_set.mp $ empty_subset _

@[simp] lemma nhds_set_empty : 𝓝ˢ (∅ : set α) = ⊥ :=
by { ext, simp [mem_nhds_set_empty] }

@[simp] lemma nhds_set_univ : 𝓝ˢ (univ : set α) = ⊤ :=
by { ext, rw [← subset_interior_iff_mem_nhds_set, univ_subset_iff, interior_eq_univ, mem_top] }

lemma monotone_nhds_set : monotone (𝓝ˢ : set α → filter α) :=
λ s t hst, Sup_le_Sup $ image_subset _ hst

@[simp] lemma nhds_set_union (s t : set α) : 𝓝ˢ (s ∪ t) = 𝓝ˢ s ⊔ 𝓝ˢ t :=
by simp only [nhds_set, image_union, Sup_union]

lemma union_mem_nhds_set (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) :=
by { rw nhds_set_union, exact union_mem_sup h₁ h₂ }

/-- Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighborhood of `s`
provided that `f` maps `s` to `t`.  -/
lemma continuous.tendsto_nhds_set {f : α → β} {t : set β} (hf : continuous f)
  (hst : maps_to f s t) : tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
((has_basis_nhds_set s).tendsto_iff (has_basis_nhds_set t)).mpr $ λ U hU,
  ⟨f ⁻¹' U, ⟨hU.1.preimage hf, hst.mono subset.rfl hU.2⟩, λ x, id⟩
