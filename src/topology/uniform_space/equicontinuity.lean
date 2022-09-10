/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence_topology

/-!
# Equicontinuity

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

section

open uniform_space filter
open_locale uniformity topological_space

variables {ι X Y Z α β γ 𝓕 : Type*} [topological_space X] [topological_space Y]
  [topological_space Z] [uniform_space α] [uniform_space β] [uniform_space γ]

def equicontinuous_at (F : ι → X → α) (x₀ : X) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

protected abbreviation set.equicontinuous_at [has_coe_to_fun 𝓕 (λ _, X → α)]
  (H : set 𝓕) (x₀ : X) : Prop :=
equicontinuous_at (coe_fn ∘ (coe : H → 𝓕)) x₀

def equicontinuous (F : ι → X → α) : Prop :=
∀ x₀, equicontinuous_at F x₀

protected abbreviation set.equicontinuous [has_coe_to_fun 𝓕 (λ _, X → α)]
  (H : set 𝓕) : Prop :=
equicontinuous (coe_fn ∘ (coe : H → 𝓕))

def uniform_equicontinuous (F : ι → β → α) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

protected abbreviation set.uniform_equicontinuous [has_coe_to_fun 𝓕 (λ _, β → α)]
  (H : set 𝓕) : Prop :=
uniform_equicontinuous (coe_fn ∘ (coe : H → 𝓕))

lemma uniform_equicontinuous.equicontinuous {F : ι → β → α} (h : uniform_equicontinuous F) :
  equicontinuous F :=
λ x₀ U hU, mem_of_superset (ball_mem_nhds x₀ (h U hU)) (λ x hx i, hx i)

lemma equicontinuous_at.continuous_at {F : ι → X → α} {x₀ : X} (h : equicontinuous_at F x₀)
  (i : ι) : continuous_at (F i) x₀ :=
begin
  intros U hU,
  rw uniform_space.mem_nhds_iff at hU,
  rcases hU with ⟨V, hV₁, hV₂⟩,
  exact mem_map.mpr (mem_of_superset (h V hV₁) (λ x hx, hV₂ (hx i)))
end

protected lemma set.equicontinuous_at.continuous_at_of_mem [has_coe_to_fun 𝓕 (λ _, X → α)]
  {H : set 𝓕} {x₀ : X} (h : H.equicontinuous_at x₀) {f : 𝓕} (hf : f ∈ H) :
  continuous_at f x₀ :=
h.continuous_at ⟨f, hf⟩

lemma equicontinuous.continuous {F : ι → X → α} (h : equicontinuous F) (i : ι) :
  continuous (F i) :=
continuous_iff_continuous_at.mpr (λ x, (h x).continuous_at i)

protected lemma set.equicontinuous.continuous_of_mem [has_coe_to_fun 𝓕 (λ _, X → α)]
  {H : set 𝓕} (h : H.equicontinuous) {f : 𝓕} (hf : f ∈ H) :
  continuous f :=
h.continuous ⟨f, hf⟩

lemma uniform_equicontinuous.uniform_continuous {F : ι → β → α} (h : uniform_equicontinuous F)
  (i : ι) : uniform_continuous (F i) :=
λ U hU, mem_map.mpr (mem_of_superset (h U hU) $ λ xy hxy, (hxy i))

protected lemma set.uniform_equicontinuous.uniform_continuous_of_mem
  [has_coe_to_fun 𝓕 (λ _, β → α)] {H : set 𝓕} (h : H.uniform_equicontinuous) {f : 𝓕} (hf : f ∈ H) :
  uniform_continuous f :=
h.uniform_continuous ⟨f, hf⟩

section

local attribute [-instance] Pi.topological_space
local attribute [-instance] Pi.uniform_space
local attribute [instance] uniform_convergence.topological_space
local attribute [instance] uniform_convergence.uniform_space

lemma equicontinuous_at_iff_continuous_at {F : ι → X → α} {x₀ : X} :
  equicontinuous_at F x₀ ↔ continuous_at (function.swap F) x₀ :=
by rw [continuous_at, (uniform_convergence.has_basis_nhds ι α _).tendsto_right_iff]; refl

lemma equicontinuous_iff_continuous {F : ι → X → α} :
  equicontinuous F ↔ continuous (function.swap F) :=
by simp_rw [equicontinuous, continuous_iff_continuous_at, equicontinuous_at_iff_continuous_at]

lemma uniform_equicontinuous_iff_uniform_continuous {F : ι → β → α} :
  uniform_equicontinuous F ↔ uniform_continuous (function.swap F) :=
by rw [uniform_continuous, (uniform_convergence.has_basis_uniformity ι α).tendsto_right_iff]; refl

lemma filter.has_basis.equicontinuous_at_iff_left {κ : Type*} {p : κ → Prop} {s : κ → set X}
  {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).has_basis p s) : equicontinuous_at F x₀ ↔
  ∀ U ∈ 𝓤 α, ∃ k (_ : p k), ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      hX.tendsto_iff (uniform_convergence.has_basis_nhds ι α _)],
  refl
end

lemma filter.has_basis.equicontinuous_at_iff_right {κ : Type*} {p : κ → Prop} {s : κ → set (α × α)}
  {F : ι → X → α} {x₀ : X} (hα : (𝓤 α).has_basis p s) : equicontinuous_at F x₀ ↔
  ∀ k, p k → ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ s k :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      (uniform_convergence.has_basis_nhds_of_basis ι α _ hα).tendsto_right_iff],
  refl
end

lemma filter.has_basis.equicontinuous_at_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop} {s₁ : κ₁ → set X}
  {p₂ : κ₂ → Prop} {s₂ : κ₂ → set (α × α)} {F : ι → X → α} {x₀ : X}
  (hX : (𝓝 x₀).has_basis p₁ s₁) (hα : (𝓤 α).has_basis p₂ s₂) : equicontinuous_at F x₀ ↔
  ∀ k₂, p₂ k₂ → ∃ k₁ (_ : p₁ k₁), ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      hX.tendsto_iff (uniform_convergence.has_basis_nhds_of_basis ι α _ hα)],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
  {s₁ : κ₁ → set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → set (α × α)} {F : ι → β → α}
  (hβ : (𝓤 β).has_basis p₁ s₁) (hα : (𝓤 α).has_basis p₂ s₂) : uniform_equicontinuous F ↔
  ∀ k₂, p₂ k₂ → ∃ k₁ (_ : p₁ k₁), ∀ (xy : β × β), xy ∈ s₁ k₁ → ∀ i, (F i xy.1, F i xy.2) ∈ s₂ k₂ :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      hβ.tendsto_iff (uniform_convergence.has_basis_uniformity_of_basis ι α hα)],
  refl
end

end

end
