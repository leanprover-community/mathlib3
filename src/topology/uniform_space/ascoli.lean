/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.equicontinuity

/-!
# Ascoli Theorem

## Main definitions
## Main statements
## Notation
## Implementation details
## References
## Tags
-/

open set filter uniform_space function
open_locale filter topological_space uniform_convergence uniformity

lemma totally_bounded_pi {ι : Type*} {α : ι → Type*} [Π i, uniform_space (α i)]
  {t : set ι} {s : Π i, set (α i)} (hs : ∀ i ∈ t, totally_bounded (s i)) :
  totally_bounded (t.pi s) :=
sorry

lemma cauchy_of_ne_bot {α : Type*} [uniform_space α] {l : filter α} [hl : l.ne_bot] :
  cauchy l ↔ l ×ᶠ l ≤ 𝓤 α :=
by simp only [cauchy, hl, true_and]

lemma cauchy_pi {ι : Type*} {α : ι → Type*} [Π i, uniform_space (α i)]
  {l : filter (Π i, α i)} : cauchy l ↔ ∀ i, cauchy (map (eval i) l) :=
sorry

variables {ι X α β : Type*} [topological_space X] [uniform_space α] [uniform_space β]
  {F : ι → X → α} {G : ι → β → α}

lemma theorem1 (hF : equicontinuous F) :
  (uniform_on_fun.uniform_space X α {S | is_compact S}).comap F =
  (Pi.uniform_space (λ _, α)).comap F :=
begin
  let 𝔖 : set (set X) := {S | is_compact S},
  have fact₁ : ⋃₀ 𝔖 = univ :=
    sUnion_eq_univ_iff.mpr (λ x, ⟨{x}, is_compact_singleton, rfl⟩),
  have fact₂ : directed_on (⊆) 𝔖 :=
    λ K₁ h₁ K₂ h₂, ⟨K₁ ∪ K₂, h₁.union h₂, subset_union_left _ _, subset_union_right _ _⟩,
  have fact₃ : 𝔖.nonempty := ⟨∅, is_compact_empty⟩,
  refine le_antisymm (uniform_space.comap_mono $ le_iff_uniform_continuous_id.mpr $
    uniform_on_fun.uniform_continuous_to_fun fact₁) _,
  change comap _ (𝓤 _) ≤ comap _ (𝓤 _),
  simp_rw [Pi.uniformity, filter.comap_infi, filter.comap_comap, function.comp],
  refine ((uniform_on_fun.has_basis_uniformity X α 𝔖 fact₃ fact₂).comap
    (prod.map F F)).ge_iff.mpr _,
  rintros ⟨K, U⟩ ⟨hK : is_compact K, hU : U ∈ 𝓤 α⟩,
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩,
  let Ω : X → set X := λ x, {y | ∀ i, (F i x, F i y) ∈ V},
  rcases hK.elim_nhds_subcover Ω (λ x hx, hF x V hV) with ⟨S, hSK, Scover⟩,
  have : (⋂ s ∈ S, {ij : ι × ι | (F ij.1 s, F ij.2 s) ∈ V}) ⊆
    (prod.map F F) ⁻¹' uniform_on_fun.gen 𝔖 K U,
  { rintro ⟨i, j⟩ hij x hx,
    rw mem_Inter₂ at hij,
    rcases mem_Union₂.mp (Scover hx) with ⟨s, hs, hsx⟩,
    exact hVU (prod_mk_mem_comp_rel (prod_mk_mem_comp_rel
      (Vsymm.mk_mem_comm.mp (hsx i)) (hij s hs)) (hsx j)) },
  exact mem_of_superset
    (S.Inter_mem_sets.mpr $ λ x hxS, mem_infi_of_mem x $ preimage_mem_comap hV) this,
end

lemma ascoli₀ {𝔖 : set (set X)} {F : ι → X →ᵤ[𝔖] α} {l : filter ι} [l.ne_bot]
  (h1 : ⋃₀ 𝔖 = set.univ)
  (h2 : ∀ A ∈ 𝔖, is_compact A)
  (h3 : ∀ A ∈ 𝔖, equicontinuous (λ i, set.restrict A (F i)))
  (h4 : ∀ x, cauchy (map (eval x ∘ F) l)) :
  cauchy (map F l) :=
begin
  change ∀ x, cauchy (map (eval x) (map F l)) at h4,
  rw ← cauchy_pi at h4,
  rw [cauchy_of_ne_bot, prod_map_map_eq, map_le_iff_le_comap] at ⊢ h4,
end

lemma ascoli {𝔖 : set (set X)}
  (h1 : ⋃₀ 𝔖 = set.univ)
  (h2 : ∀ A ∈ 𝔖, is_compact A)
  (h3 : ∀ A ∈ 𝔖, equicontinuous (λ i, set.restrict A (F i)))
  (h4 : ∀ x, totally_bounded (range (λ i, F i x))) :
  totally_bounded (range F) :=
begin

end
