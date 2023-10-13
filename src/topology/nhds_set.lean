/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import topology.basic
/-!
# Neighborhoods of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
open_locale topology filter

variables {α β : Type*} [topological_space α] [topological_space β]
  {s t s₁ s₂ t₁ t₂ : set α} {x : α}

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set α) : filter α :=
Sup (nhds '' s)

localized "notation (name := nhds_set) `𝓝ˢ` := nhds_set" in topology

lemma nhds_set_diagonal (α) [topological_space (α × α)] : 𝓝ˢ (diagonal α) = ⨆ x, 𝓝 (x, x) :=
by { rw [nhds_set, ← range_diag, ← range_comp], refl }

lemma mem_nhds_set_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ (x : α), x ∈ t → s ∈ 𝓝 x :=
by simp_rw [nhds_set, filter.mem_Sup, ball_image_iff]

lemma bUnion_mem_nhds_set {t : α → set α} (h : ∀ x ∈ s, t x ∈ 𝓝 x) : (⋃ x ∈ s, t x) ∈ 𝓝ˢ s :=
mem_nhds_set_iff_forall.2 $ λ x hx, mem_of_superset (h x hx) (subset_Union₂ x hx)

lemma subset_interior_iff_mem_nhds_set : s ⊆ interior t ↔ t ∈ 𝓝ˢ s :=
by simp_rw [mem_nhds_set_iff_forall, subset_interior_iff_nhds]

lemma mem_nhds_set_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : set α, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma has_basis_nhds_set (s : set α) : (𝓝ˢ s).has_basis (λ U, is_open U ∧ s ⊆ U) (λ U, U) :=
⟨λ t, by simp [mem_nhds_set_iff_exists, and_assoc]⟩

lemma is_open.mem_nhds_set (hU : is_open s) : s ∈ 𝓝ˢ t ↔ t ⊆ s :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_is_open.mpr hU]

lemma principal_le_nhds_set : 𝓟 s ≤ 𝓝ˢ s :=
λ s hs, (subset_interior_iff_mem_nhds_set.mpr hs).trans interior_subset

@[simp] lemma nhds_set_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ is_open s :=
by rw [← principal_le_nhds_set.le_iff_eq, le_principal_iff, mem_nhds_set_iff_forall,
  is_open_iff_mem_nhds]

alias nhds_set_eq_principal_iff ↔ _ is_open.nhds_set_eq

@[simp] lemma nhds_set_interior : 𝓝ˢ (interior s) = 𝓟 (interior s) :=
is_open_interior.nhds_set_eq

@[simp] lemma nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x :=
by { ext,
     rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff] }

lemma mem_nhds_set_interior : s ∈ 𝓝ˢ (interior s) :=
subset_interior_iff_mem_nhds_set.mp subset.rfl

@[simp] lemma nhds_set_empty : 𝓝ˢ (∅ : set α) = ⊥ :=
by rw [is_open_empty.nhds_set_eq, principal_empty]

lemma mem_nhds_set_empty : s ∈ 𝓝ˢ (∅ : set α) := by simp

@[simp] lemma nhds_set_univ : 𝓝ˢ (univ : set α) = ⊤ :=
by rw [is_open_univ.nhds_set_eq, principal_univ]

@[mono] lemma nhds_set_mono (h : s ⊆ t) : 𝓝ˢ s ≤ 𝓝ˢ t :=  Sup_le_Sup $ image_subset _ h

lemma monotone_nhds_set : monotone (𝓝ˢ : set α → filter α) := λ s t, nhds_set_mono

lemma nhds_le_nhds_set (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s := le_Sup $ mem_image_of_mem _ h

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
