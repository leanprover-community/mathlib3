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

variables {ι X Y Z α β γ : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  [uniform_space α] [uniform_space β] [uniform_space γ]

def equicontinuous_at (F : ι → X → α) (x₀ : X) : Prop :=
∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ i, (F i x₀, F i x) ∈ U

protected abbreviation set.equicontinuous_at (H : set $ X → α) (x₀ : X) : Prop :=
equicontinuous_at (coe : H → X → α) x₀

def equicontinuous (F : ι → X → α) : Prop :=
∀ x₀, equicontinuous_at F x₀

protected abbreviation set.equicontinuous (H : set $ X → α) : Prop :=
equicontinuous (coe : H → X → α)

def uniform_equicontinuous (F : ι → β → α) : Prop :=
∀ U ∈ 𝓤 α, ∃ V ∈ 𝓤 β, ∀ (xy : β × β) (_ : xy ∈ V), ∀ i, (F i xy.1, F i xy.2) ∈ U

protected abbreviation set.uniform_equicontinuous (H : set $ β → α) : Prop :=
uniform_equicontinuous (coe : H → β → α)

lemma uniform_equicontinuous.equicontinuous {F : ι → β → α} (h : uniform_equicontinuous F) :
  equicontinuous F :=
begin
  intros x₀ U hU,
  rcases h U hU with ⟨W, hW₁, hW₂⟩,
  exact ⟨ball x₀ W, ball_mem_nhds x₀ hW₁, λ x hx i, hW₂ (x₀, x) hx _⟩
end

lemma equicontinuous_at.continuous_at {F : ι → X → α} {x₀ : X} (h : equicontinuous_at F x₀)
  (i : ι) : continuous_at (F i) x₀ :=
begin
  intros U hU,
  rw uniform_space.mem_nhds_iff at hU,
  rcases hU with ⟨V, hV₁, hV₂⟩,
  rcases h V hV₁ with ⟨W, hW₁, hW₂⟩,
  exact mem_map.mpr (mem_of_superset hW₁ $ λ x hx, hV₂ $ hW₂ _ hx _)
end

protected lemma set.equicontinuous_at.continuous_at_of_mem {H : set $ X → α} {x₀ : X}
  (h : H.equicontinuous_at x₀) {f : X → α} (hf : f ∈ H) :
  continuous_at f x₀ :=
h.continuous_at ⟨f, hf⟩

lemma equicontinuous.continuous {F : ι → X → α} (h : equicontinuous F) (i : ι) :
  continuous (F i) :=
continuous_iff_continuous_at.mpr (λ x, (h x).continuous_at i)

protected lemma set.equicontinuous.continuous_of_mem {H : set $ X → α}
  (h : H.equicontinuous) {f : X → α} (hf : f ∈ H) :
  continuous f :=
h.continuous ⟨f, hf⟩

lemma uniform_equicontinuous.uniform_continuous {F : ι → β → α} (h : uniform_equicontinuous F)
  (i : ι) : uniform_continuous (F i) :=
begin
  intros U hU,
  rcases h U hU with ⟨V, hV₁, hV₂⟩,
  exact mem_map.mpr (mem_of_superset hV₁ $ λ xy hxy, hV₂ _ hxy _)
end

protected lemma set.uniform_equicontinuous.uniform_continuous_of_mem {H : set $ β → α}
  (h : H.uniform_equicontinuous) {f : β → α} (hf : f ∈ H) :
  uniform_continuous f :=
h.uniform_continuous ⟨f, hf⟩

end
