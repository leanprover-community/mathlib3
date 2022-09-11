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

open uniform_space filter set
open_locale uniformity topological_space

variables {ι κ X Y Z α β γ : Type*} [topological_space X] [topological_space Y]
  [topological_space Z] [uniform_space α] [uniform_space β] [uniform_space γ]

def equicontinuous_at (F : ι → X → α) (x₀ : X) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

protected abbreviation set.equicontinuous_at (H : set $ X → α) (x₀ : X) : Prop :=
equicontinuous_at (coe : H → X → α) x₀

def equicontinuous (F : ι → X → α) : Prop :=
∀ x₀, equicontinuous_at F x₀

protected abbreviation set.equicontinuous (H : set $ X → α) : Prop :=
equicontinuous (coe : H → X → α)

def uniform_equicontinuous (F : ι → β → α) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

protected abbreviation set.uniform_equicontinuous (H : set $ β → α) : Prop :=
uniform_equicontinuous (coe : H → β → α)

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

protected lemma set.equicontinuous_at.continuous_at_of_mem {H : set $ X → α} {x₀ : X}
  (h : H.equicontinuous_at x₀) {f : X → α} (hf : f ∈ H) : continuous_at f x₀ :=
h.continuous_at ⟨f, hf⟩

lemma equicontinuous.continuous {F : ι → X → α} (h : equicontinuous F) (i : ι) :
  continuous (F i) :=
continuous_iff_continuous_at.mpr (λ x, (h x).continuous_at i)

protected lemma set.equicontinuous.continuous_of_mem {H : set $ X → α} (h : H.equicontinuous)
  {f : X → α} (hf : f ∈ H) : continuous f :=
h.continuous ⟨f, hf⟩

lemma uniform_equicontinuous.uniform_continuous {F : ι → β → α} (h : uniform_equicontinuous F)
  (i : ι) : uniform_continuous (F i) :=
λ U hU, mem_map.mpr (mem_of_superset (h U hU) $ λ xy hxy, (hxy i))

protected lemma set.uniform_equicontinuous.uniform_continuous_of_mem {H : set $ β → α}
  (h : H.uniform_equicontinuous) {f : β → α} (hf : f ∈ H) : uniform_continuous f :=
h.uniform_continuous ⟨f, hf⟩

lemma equicontinuous_at.comp {F : ι → X → α} {x₀ : X} (h : equicontinuous_at F x₀) (u : κ → ι) :
  equicontinuous_at (F ∘ u) x₀ :=
λ U hU, (h U hU).mono (λ x H k, H (u k))

protected lemma set.equicontinuous_at.mono {H H' : set $ X → α} {x₀ : X}
  (h : H.equicontinuous_at x₀) (hH : H' ⊆ H) : H'.equicontinuous_at x₀ :=
h.comp (inclusion hH)

lemma equicontinuous.comp {F : ι → X → α} (h : equicontinuous F) (u : κ → ι) :
  equicontinuous (F ∘ u) :=
λ x, (h x).comp u

protected lemma set.equicontinuous.mono {H H' : set $ X → α}
  (h : H.equicontinuous) (hH : H' ⊆ H) : H'.equicontinuous :=
h.comp (inclusion hH)

lemma uniform_equicontinuous.comp {F : ι → β → α} (h : uniform_equicontinuous F) (u : κ → ι) :
  uniform_equicontinuous (F ∘ u) :=
λ U hU, (h U hU).mono (λ x H k, H (u k))

protected lemma set.uniform_equicontinuous.mono {H H' : set $ β → α}
  (h : H.uniform_equicontinuous) (hH : H' ⊆ H) : H'.uniform_equicontinuous :=
h.comp (inclusion hH)

lemma equicontinuous_at_iff_range {F : ι → X → α} {x₀ : X} :
  equicontinuous_at F x₀ ↔ equicontinuous_at (coe : range F → X → α) x₀ :=
⟨λ h, by rw ← comp_range_splitting F; exact h.comp _, λ h, h.comp (range_factorization F)⟩

lemma equicontinuous_iff_range {F : ι → X → α} :
  equicontinuous F ↔ equicontinuous (coe : range F → X → α) :=
forall_congr (λ x₀, equicontinuous_at_iff_range)

lemma uniform_equicontinuous_at_iff_range {F : ι → β → α} :
  uniform_equicontinuous F ↔ uniform_equicontinuous (coe : range F → β → α) :=
⟨λ h, by rw ← comp_range_splitting F; exact h.comp _, λ h, h.comp (range_factorization F)⟩

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

lemma filter.has_basis.uniform_equicontinuous_iff_left {κ : Type*} {p : κ → Prop}
  {s : κ → set (β × β)} {F : ι → β → α} (hβ : (𝓤 β).has_basis p s) : uniform_equicontinuous F ↔
  ∀ U ∈ 𝓤 α, ∃ k (_ : p k), ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      hβ.tendsto_iff (uniform_convergence.has_basis_uniformity ι α)],
  simp_rw [prod.forall],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff_right {κ : Type*} {p : κ → Prop}
  {s : κ → set (α × α)} {F : ι → β → α} (hα : (𝓤 α).has_basis p s) : uniform_equicontinuous F ↔
  ∀ k, p k → ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ s k :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      (uniform_convergence.has_basis_uniformity_of_basis ι α hα).tendsto_right_iff],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
  {s₁ : κ₁ → set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → set (α × α)} {F : ι → β → α}
  (hβ : (𝓤 β).has_basis p₁ s₁) (hα : (𝓤 α).has_basis p₂ s₂) : uniform_equicontinuous F ↔
  ∀ k₂, p₂ k₂ → ∃ k₁ (_ : p₁ k₁), ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      hβ.tendsto_iff (uniform_convergence.has_basis_uniformity_of_basis ι α hα)],
  simp_rw [prod.forall],
  refl
end

lemma uniform_inducing.equicontinuous_at_iff {F : ι → X → α} {x₀ : X} {u : α → β}
  (hu : uniform_inducing u) :
  equicontinuous_at F x₀ ↔ equicontinuous_at (((∘) u) ∘ F) x₀ :=
begin
  have := (uniform_convergence.postcomp_uniform_inducing hu).inducing,
  rw [equicontinuous_at_iff_continuous_at, equicontinuous_at_iff_continuous_at,
      this.continuous_at_iff]
end

lemma uniform_inducing.equicontinuous_iff {F : ι → X → α} {u : α → β}
  (hu : uniform_inducing u) :
  equicontinuous F ↔ equicontinuous (((∘) u) ∘ F) :=
begin
  congrm (∀ x, (_ : Prop)),
  rw hu.equicontinuous_at_iff
end

lemma uniform_inducing.uniform_equicontinuous_iff {F : ι → β → α} {u : α → γ}
  (hu : uniform_inducing u) :
  uniform_equicontinuous F ↔ uniform_equicontinuous (((∘) u) ∘ F) :=
begin
  have := uniform_convergence.postcomp_uniform_inducing hu,
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_equicontinuous_iff_uniform_continuous,
      this.uniform_continuous_iff]
end

lemma equicontinuous.closure {A : set $ X → α} (hA : A.equicontinuous) :
  (closure A).equicontinuous :=
begin
  intros x U hU,
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩,
  filter_upwards [hA x V hV],
  rintros y hy ⟨f, hf⟩,
  rcases uniform_space.mem_closure_iff_ball.mp hf
    ((uniform_convergence.has_basis_uniformity X α).mem_of_mem hV) with ⟨g, hgf, hg⟩,
  exact hVU (prod_mk_mem_comp_rel (prod_mk_mem_comp_rel (hgf x) (hy ⟨g, hg⟩)) $
    hVsymm.mk_mem_comm.mp (hgf y))
end

lemma continuous.equicontinuous_closure {A : set Y} {u : Y → X → α}
  (hA : equicontinuous (u ∘ coe : A → X → α)) (hu : continuous u) :
  equicontinuous (u ∘ coe : (closure A) → X → α) :=
begin
  rw [equicontinuous_iff_range, range_comp, subtype.range_coe] at *,
  exact set.equicontinuous.mono hA.closure (image_closure_subset_closure_image hu)
end

end

end
