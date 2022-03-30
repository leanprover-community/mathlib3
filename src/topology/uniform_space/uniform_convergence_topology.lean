/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence
import topology.uniform_space.pi

/-!
# TODO
-/
noncomputable theory
open_locale topological_space classical uniformity filter

local attribute [-instance] Pi.uniform_space

open set filter

namespace uniform_convergence

variables (α β : Type*) {γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def gen (V : set (β × β)) : set ((α → β) × (α → β)) :=
  {uv : (α → β) × (α → β) | ∀ x, (uv.1 x, uv.2 x) ∈ V}

protected lemma is_basis_gen :
  is_basis (λ V : set (β × β), V ∈ 𝓤 β) (uniform_convergence.gen α β) :=
⟨⟨univ, univ_mem⟩, λ U V hU hV, ⟨U ∩ V, inter_mem hU hV, λ uv huv,
  ⟨λ x, (huv x).left, λ x, (huv x).right⟩⟩⟩

protected def uniformity_basis : filter_basis ((α → β) × (α → β)) :=
(uniform_convergence.is_basis_gen α β).filter_basis

protected def uniform_core : uniform_space.core (α → β) :=
uniform_space.core.mk_of_basis (uniform_convergence.uniformity_basis α β)
  (λ U ⟨V, hV, hVU⟩ f, hVU ▸ λ x, refl_mem_uniformity hV)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ ⟨uniform_convergence.gen α β (prod.swap ⁻¹' V),
    ⟨prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩, λ uv huv x, huv x⟩)
  (λ U ⟨V, hV, hVU⟩, hVU ▸ let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV in
    ⟨uniform_convergence.gen α β W, ⟨W, hW, rfl⟩, λ uv ⟨w, huw, hwv⟩ x, hWV
      ⟨w x, by exact ⟨huw x, hwv x⟩⟩⟩)

protected def uniform_space : uniform_space (α → β) :=
uniform_space.of_core (uniform_convergence.uniform_core α β)

protected lemma has_basis_uniformity :
  (@uniformity (α → β) (uniform_convergence.uniform_space α β)).has_basis (λ V, V ∈ 𝓤 β)
  (uniform_convergence.gen α β) :=
(uniform_convergence.is_basis_gen α β).has_basis

protected def topological_space : topological_space (α → β) :=
(uniform_convergence.uniform_core α β).to_topological_space

variables {α β}

lemma uniform_continuous_eval (x : α) : @uniform_continuous _ _
  (uniform_convergence.uniform_space α β) _ (function.eval x) :=
begin
  change _ ≤ _,
  rw [map_le_iff_le_comap,
      (uniform_convergence.has_basis_uniformity α β).le_basis_iff ((𝓤 _).basis_sets.comap _)],
  exact λ U hU, ⟨U, hU, λ uv huv, huv x⟩
end

protected lemma le_Pi : uniform_convergence.uniform_space α β ≤ Pi.uniform_space (λ _, β) :=
begin
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi],
  intros x,
  exact uniform_continuous_eval x
end

variable {α}

end uniform_convergence

namespace uniform_convergence_on

variables (α β : Type*) {γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def uniform_space : uniform_space (α → β) :=
⨅ (s : set α) (hs : s ∈ 𝔖), uniform_space.comap (λ f, s.restrict f)
  (uniform_convergence.uniform_space s β)

protected lemma uniform_continuous_restrict (h : s ∈ 𝔖) :
  @uniform_continuous _ _ (uniform_convergence_on.uniform_space α β 𝔖)
  (uniform_convergence.uniform_space s β) s.restrict :=
begin
  change _ ≤ _,
  rw [uniform_convergence_on.uniform_space, map_le_iff_le_comap, uniformity, infi_uniformity],
  refine infi_le_of_le s _,
  rw infi_uniformity,
  exact infi_le _ h,
end

protected lemma uniform_space_antitone : antitone (uniform_convergence_on.uniform_space α β) :=
λ 𝔖₁ 𝔖₂ h₁₂, infi_le_infi_of_subset h₁₂

variables {α β}

lemma uniform_continuous_eval_of_mem {x : α} (hxs : x ∈ s) (hs : s ∈ 𝔖) :
  @uniform_continuous _ _ (uniform_convergence_on.uniform_space α β 𝔖) _ (function.eval x) :=
begin
  change _ ≤ _,
  rw [map_le_iff_le_comap, ((𝓤 _).basis_sets.comap _).ge_iff,
      uniform_convergence_on.uniform_space, infi_uniformity'],
  intros U hU,
  refine mem_infi_of_mem s _,
  rw infi_uniformity',
  exact mem_infi_of_mem hs (mem_comap.mpr
    ⟨ uniform_convergence.gen s β U,
      (uniform_convergence.has_basis_uniformity s β).mem_of_mem hU,
      λ uv huv, huv ⟨x, hxs⟩ ⟩)
end

protected lemma le_Pi_of_covering (h : ⋃₀ 𝔖 = univ) :
  uniform_convergence_on.uniform_space α β 𝔖 ≤ Pi.uniform_space (λ _, β) :=
begin
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi],
  intros x,
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ true.intro),
  exact uniform_continuous_eval_of_mem 𝔖 hxs hs
end

end uniform_convergence_on
