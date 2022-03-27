/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence

/-!
# TODO
-/
noncomputable theory
open_locale topological_space classical uniformity filter

open set filter

namespace uniform_convergence

variables (α : Type*) {β γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def gen (V : set (β × β)) : set ((α → β) × (α → β)) :=
  {uv : (α → β) × (α → β) | ∀ x, (uv.1 x, uv.2 x) ∈ V}

protected lemma is_basis_gen : is_basis (λ V : set (β × β), V ∈ 𝓤 β) (uniform_convergence.gen α) :=
⟨⟨univ, univ_mem⟩, λ U V hU hV, ⟨U ∩ V, inter_mem hU hV, λ uv huv,
  ⟨λ x, (huv x).left, λ x, (huv x).right⟩⟩⟩

protected def uniformity_basis : filter_basis ((α → β) × (α → β)) :=
(uniform_convergence.is_basis_gen α).filter_basis

protected def uniform_core : uniform_space.core (α → β) :=
uniform_space.core.mk_of_basis (uniform_convergence.uniformity_basis α)
  (λ U ⟨V, hV, hVU⟩ f, hVU ▸ λ x, refl_mem_uniformity hV)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ ⟨uniform_convergence.gen α (prod.swap ⁻¹' V),
    ⟨prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩, λ uv huv x, huv x⟩)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV in
    ⟨uniform_convergence.gen α W, ⟨W, hW, rfl⟩, λ uv ⟨w, huw, hwv⟩ x, hWV
      ⟨w x, by exact ⟨huw x, hwv x⟩⟩⟩)

protected def uniform_space : uniform_space (α → β) :=
uniform_space.of_core (uniform_convergence.uniform_core α)

end uniform_convergence

namespace uniform_convergence_on

variables {α : Type*} {β γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def restrict (S : set α) (f : α → β) : S → β :=
f ∘ coe

variables {α}

def uniform_space : uniform_space (α → β) :=
⨅ (S : set α) (hS : S ∈ 𝔖), uniform_space.comap (λ f, f ∘ coe) (uniform_convergence.uniform_space S)

end uniform_convergence_on
