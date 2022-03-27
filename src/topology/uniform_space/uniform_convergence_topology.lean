/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence
import topology.bornology.order

/-!
# TODO
-/
noncomputable theory
open_locale topological_space classical uniformity filter

open set filter bornology

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

lemma foo1 (h : s ⊆ s') : @uniform_continuous (s' → β) (s → β)
  (uniform_convergence.uniform_space s' β) (uniform_convergence.uniform_space s β)
  (λ f x, f ⟨x.1, h x.2⟩) :=
((uniform_convergence.has_basis_uniformity s' β).tendsto_iff
  (uniform_convergence.has_basis_uniformity s β)).mpr (λ U hU,
    ⟨U, hU, λ uv huv ⟨x, hx⟩, huv ⟨x, h hx⟩⟩)

lemma bar1 (h : s ⊆ s') {f : α → β} : (s.restrict : (α → β) → (s → β)) =
  (λ (f : s' → β) (x : s), f (⟨x.1, h x.2⟩ : s')) ∘ s'.restrict :=
rfl

lemma foo2 (s s' : set α) : @uniform_continuous ((s → β) × (s' → β)) (s ∪ s' → β)
  (@prod.uniform_space _ _
    (uniform_convergence.uniform_space s β) (uniform_convergence.uniform_space s' β))
  (uniform_convergence.uniform_space (s ∪ s' : set α) β)
    (λ uv x, x.2.by_cases (λ hx, uv.1 ⟨x.1, hx⟩) (λ hx, uv.2 ⟨x.1, hx⟩)) :=
begin
  rw [uniform_continuous, uniformity_prod],
  refine ((((uniform_convergence.has_basis_uniformity s β).comap _).inf
    ((uniform_convergence.has_basis_uniformity s' β).comap _)).tendsto_iff
    ((uniform_convergence.has_basis_uniformity (s ∪ s' : set α) β))).mpr
    (λ U hU, ⟨⟨U, U⟩, ⟨hU, hU⟩, λ u₁v₁u₂v₂ h x, _⟩),
  simp_rw or.by_cases,
  --split_ifs with h₁ h₂,
  sorry
end

lemma bar2 (s s' : set α) : ((s ∪ s' : set α).restrict : (α → β) → ((s ∪ s') → β)) =
  (λ (uv : (s → β) × (s' → β)) x, x.2.by_cases (λ hx, uv.1 ⟨x.1, hx⟩) (λ hx, uv.2 ⟨x.1, hx⟩)) ∘
    (λ f, ⟨λ x, f x.1, λ x, f x.1⟩) :=
begin
  ext f x,
  dsimp [or.by_cases],
  split_ifs with h₁ h₂,
  { refl },
  { refl },
  { exact (x.2.elim h₁ h₂).elim }
end

variable {α}

end uniform_convergence

namespace uniform_convergence_on

variables (α β : Type*) {γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def uniform_space : uniform_space (α → β) :=
⨅ (s : set α) (hs : s ∈ 𝔖), uniform_space.comap (λ f, s.restrict f)
  (uniform_convergence.uniform_space s β)

protected lemma uniform_continuous_restrict {s : set α} (h : s ∈ 𝔖) :
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

variables {α}

lemma uniform_space_eq_uniform_space_generated :
  uniform_convergence_on.uniform_space α β 𝔖 =
  uniform_convergence_on.uniform_space α β {s | @is_bounded _ (bornology.generate 𝔖) s} :=
begin
  rw [uniform_convergence_on.uniform_space, uniform_convergence_on.uniform_space],
  refine le_antisymm (le_infi $ λ s, le_infi $ λ hs, _)
    (infi_le_infi_of_subset $ λ s, is_bounded_generate),
  sorry
  --refine infi_le_infi (λ s, _),
end

def foo (u : uniform_space (α → β)) : bornology α :=
bornology.of_bounded'
  {S | @uniform_continuous _ _ u (uniform_convergence.uniform_space _ _) (restrict S)}
  (@uniform_continuous_of_const _ _ u (uniform_convergence.uniform_space (∅ : set α) _)
    ((∅ : set α).restrict) (λ a b, funext $ λ x, x.2.elim))
  (λ s₁ h₁ s₂ h₂₁, @uniform_continuous.comp _ _ _ u (uniform_convergence.uniform_space s₁ _)
    (uniform_convergence.uniform_space s₂ _) _ _ (uniform_convergence.foo1 α β h₂₁) h₁)
  (λ s₁ h₁ s₂ h₂,
    begin
      letI : uniform_space (s₁ → β) := uniform_convergence.uniform_space s₁ _,
      letI : uniform_space (s₂ → β) := uniform_convergence.uniform_space s₂ _,
      letI : uniform_space ((s₁ ∪ s₂) → β) := uniform_convergence.uniform_space (s₁ ∪ s₂ : set α) _,
      change uniform_continuous ((s₁ ∪ s₂).restrict : (α → β) → ((s₁ ∪ s₂) → β)),
      rw uniform_convergence.bar2 α β s₁ s₂,
      exact (uniform_convergence.foo2 α β s₁ s₂).comp (uniform_continuous.prod_mk h₁ h₂)
    end)
  (λ x, sorry)

lemma uniform_convergence_on_foo : uniform_convergence_on.uniform_space α β 𝔖 =
  uniform_convergence_on.uniform_space α β
    {s | @is_bounded _ (foo β $ uniform_convergence_on.uniform_space α β 𝔖) s} :=
begin
  ext : 1,
  refine le_antisymm _ _,
  sorry,
  sorry
end

lemma uniform_space_eq_uniform_space_generated' :
  uniform_convergence_on.uniform_space α β 𝔖 =
  uniform_convergence_on.uniform_space α β {s | @is_bounded _ (bornology.generate 𝔖) s} :=
begin
  refine le_antisymm _ (infi_le_infi_of_subset $ λ s, is_bounded_generate),
  rw uniform_convergence_on_foo β 𝔖,
  refine uniform_convergence_on.uniform_space_antitone _ _ _,
  change ∀ s, @is_bounded _ _ s → @is_bounded _ _ s,
  rw [← bornology.le_iff],
  refine bornology.generate_minimal (λ s, _),
  rw is_bounded_of_bounded_iff,
  exact uniform_convergence_on.uniform_continuous_restrict α β 𝔖
end

end uniform_convergence_on
