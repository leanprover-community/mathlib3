/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import order.compactly_generated
import topology.sets.closeds

/-!
# Noetherian space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `well_founded ((>) : opens α → opens α → Prop)`
- `well_founded ((<) : closeds α → closeds α → Prop)`
- `∀ s : set α, is_compact s`
- `∀ s : opens α, is_compact s`

The first is chosen as the definition, and the equivalence is shown in
`topological_space.noetherian_space_tfae`.

Many examples of noetherian spaces come from algebraic topology. For example, the underlying space
of a noetherian scheme (e.g., the spectrum of a noetherian ring) is noetherian.

## Main Results
- `noetherian_space.set`: Every subspace of a noetherian space is noetherian.
- `noetherian_space.is_compact`: Every subspace of a noetherian space is compact.
- `noetherian_space_tfae`: Describes the equivalent definitions of noetherian spaces.
- `noetherian_space.range`: The image of a noetherian space under a continuous map is noetherian.
- `noetherian_space.Union`: The finite union of noetherian spaces is noetherian.
- `noetherian_space.discrete`: A noetherian and hausdorff space is discrete.
- `noetherian_space.exists_finset_irreducible` : Every closed subset of a noetherian space is a
  finite union of irreducible closed subsets.
- `noetherian_space.finite_irreducible_components `: The number of irreducible components of a
  noetherian space is finite.

-/

variables (α β : Type*) [topological_space α] [topological_space β]

namespace topological_space

/-- Type class for noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
@[mk_iff]
class noetherian_space : Prop :=
(well_founded : well_founded ((>) : opens α → opens α → Prop))

lemma noetherian_space_iff_opens :
  noetherian_space α ↔ ∀ s : opens α, is_compact (s : set α) :=
begin
  rw [noetherian_space_iff, complete_lattice.well_founded_iff_is_Sup_finite_compact,
    complete_lattice.is_Sup_finite_compact_iff_all_elements_compact],
  exact forall_congr opens.is_compact_element_iff,
end

@[priority 100]
instance noetherian_space.compact_space [h : noetherian_space α] : compact_space α :=
⟨(noetherian_space_iff_opens α).mp h ⊤⟩

variables {α β}

protected lemma noetherian_space.is_compact [noetherian_space α] (s : set α) : is_compact s :=
begin
  refine is_compact_iff_finite_subcover.2 (λ ι U hUo hs, _),
  rcases ((noetherian_space_iff_opens α).mp ‹_›
    ⟨⋃ i, U i, is_open_Union hUo⟩).elim_finite_subcover U hUo set.subset.rfl with ⟨t, ht⟩,
  exact ⟨t, hs.trans ht⟩
end

protected lemma inducing.noetherian_space [noetherian_space α] {i : β → α} (hi : inducing i) :
  noetherian_space β :=
(noetherian_space_iff_opens _).2 $ λ s, hi.is_compact_iff.1 (noetherian_space.is_compact _)

instance noetherian_space.set [h : noetherian_space α] (s : set α) : noetherian_space s :=
inducing_coe.noetherian_space

variable (α)

example (α : Type*) : set α ≃o (set α)ᵒᵈ := by refine order_iso.compl (set α)

lemma noetherian_space_tfae :
  tfae [noetherian_space α,
    well_founded (λ s t : closeds α, s < t),
    ∀ s : set α, is_compact s,
    ∀ s : opens α, is_compact (s : set α)] :=
begin
  tfae_have : 1 ↔ 2,
  { refine (noetherian_space_iff _).trans (surjective.well_founded_iff opens.compl_bijective.2 _),
    exact λ s t, (order_iso.compl (set α)).lt_iff_lt.symm },
  tfae_have : 1 ↔ 4,
  { exact noetherian_space_iff_opens α },
  tfae_have : 1 → 3,
  { exact @noetherian_space.is_compact _ _ },
  tfae_have : 3 → 4,
  { exact λ H s, H s },
  tfae_finish
end

variables {α β}

instance {α} : noetherian_space (cofinite_topology α) :=
begin
  simp only [noetherian_space_iff_opens, is_compact_iff_ultrafilter_le_nhds,
    cofinite_topology.nhds_eq, ultrafilter.le_sup_iff],
  intros s f hs,
  rcases f.le_cofinite_or_eq_pure with hf|⟨a, rfl⟩,
  { rcases filter.nonempty_of_mem (filter.le_principal_iff.1 hs) with ⟨a, ha⟩,
    exact ⟨a, ha, or.inr hf⟩ },
  { exact ⟨a, filter.le_principal_iff.mp hs, or.inl le_rfl⟩ }
end

lemma noetherian_space_of_surjective [noetherian_space α] (f : α → β)
  (hf : continuous f) (hf' : function.surjective f) : noetherian_space β :=
begin
  rw noetherian_space_iff_opens,
  intro s,
  obtain ⟨t, e⟩ := set.image_surjective.mpr hf' s,
  exact e ▸ (noetherian_space.is_compact t).image hf,
end

lemma noetherian_space_iff_of_homeomorph (f : α ≃ₜ β) :
  noetherian_space α ↔ noetherian_space β :=
⟨λ h, @@noetherian_space_of_surjective _ _ h f f.continuous f.surjective,
  λ h, @@noetherian_space_of_surjective _ _ h f.symm f.symm.continuous f.symm.surjective⟩

lemma noetherian_space.range [noetherian_space α] (f : α → β) (hf : continuous f) :
  noetherian_space (set.range f) :=
noetherian_space_of_surjective (set.cod_restrict f _ set.mem_range_self) (by continuity)
  (λ ⟨a, b, h⟩, ⟨b, subtype.ext h⟩)

lemma noetherian_space_set_iff (s : set α) :
  noetherian_space s ↔ ∀ t ⊆ s, is_compact t :=
begin
  rw (noetherian_space_tfae s).out 0 2,
  split,
  { intros H t ht,
    have := embedding_subtype_coe.is_compact_iff_is_compact_image.mp (H (coe ⁻¹' t)),
    simpa [set.inter_eq_left_iff_subset.mpr ht] using this },
  { intros H t,
    refine embedding_subtype_coe.is_compact_iff_is_compact_image.mpr (H (coe '' t) _),
    simp }
end

@[simp] lemma noetherian_univ_iff :
  noetherian_space (set.univ : set α) ↔ noetherian_space α :=
noetherian_space_iff_of_homeomorph (homeomorph.set.univ α)

lemma noetherian_space.Union {ι : Type*} (f : ι → set α) [finite ι]
  [hf : ∀ i, noetherian_space (f i)] :
  noetherian_space (⋃ i, f i) :=
begin
  casesI nonempty_fintype ι,
  simp_rw noetherian_space_set_iff at hf ⊢,
  intros t ht,
  rw [← set.inter_eq_left_iff_subset.mpr ht, set.inter_Union],
  exact is_compact_Union (λ i, hf i _ (set.inter_subset_right _ _))
end

-- This is not an instance since it makes a loop with `t2_space_discrete`.
lemma noetherian_space.discrete [noetherian_space α] [t2_space α] : discrete_topology α :=
⟨eq_bot_iff.mpr (λ U _, is_closed_compl_iff.mp (noetherian_space.is_compact _).is_closed)⟩

local attribute [instance] noetherian_space.discrete

/-- Spaces that are both Noetherian and Hausdorff is finite. -/
lemma noetherian_space.finite [noetherian_space α] [t2_space α] : finite α :=
begin
  letI : fintype α :=
    set.fintype_of_finite_univ (noetherian_space.is_compact set.univ).finite_of_discrete,
  apply_instance
end

@[priority 100]
instance finite.to_noetherian_space [finite α] : noetherian_space α :=
⟨finite.well_founded_of_trans_of_irrefl _⟩

lemma noetherian_space.exists_finset_irreducible [noetherian_space α] (s : closeds α) :
  ∃ S : finset (closeds α), (∀ k : S, is_irreducible (k : set α)) ∧ s = S.sup id :=
begin
  classical,
  have := ((noetherian_space_tfae α).out 0 1).mp infer_instance,
  apply well_founded.induction this s, clear s,
  intros s H,
  by_cases h₁ : is_preirreducible s.1,
  cases h₂ : s.1.eq_empty_or_nonempty,
  { use ∅, refine ⟨λ k, k.2.elim, _⟩, rw finset.sup_empty, ext1, exact h },
  { use {s},
    simp only [coe_coe, finset.sup_singleton, id.def, eq_self_iff_true, and_true],
    rintro ⟨k, hk⟩,
    cases finset.mem_singleton.mp hk,
    exact ⟨h, h₁⟩ },
  { rw is_preirreducible_iff_closed_union_closed at h₁,
    push_neg at h₁,
    obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁,
    obtain ⟨S₁, hS₁, hS₁'⟩ := H (s ⊓ ⟨z₁, hz₁⟩) (inf_lt_left.2 hz₁'),
    obtain ⟨S₂, hS₂, hS₂'⟩ := H (s ⊓ ⟨z₂, hz₂⟩) (inf_lt_left.2 hz₂'),
    refine ⟨S₁ ∪ S₂, λ k, _, _⟩,
    { cases finset.mem_union.mp k.2 with h' h', exacts [hS₁ ⟨k, h'⟩, hS₂ ⟨k, h'⟩] },
    { rwa [finset.sup_union, ← hS₁', ← hS₂', ← inf_sup_left, left_eq_inf] } }
end

lemma noetherian_space.finite_irreducible_components [noetherian_space α] :
  (irreducible_components α).finite :=
begin
  classical,
  obtain ⟨S, hS₁, hS₂⟩ := noetherian_space.exists_finset_irreducible (⊤ : closeds α),
  suffices : irreducible_components α ⊆ coe '' (S : set $ closeds α),
  { exact set.finite.subset ((set.finite.intro infer_instance).image _) this },
  intros K hK,
  obtain ⟨z, hz, hz'⟩ : ∃ (z : set α) (H : z ∈ finset.image coe S), K ⊆ z,
  { convert is_irreducible_iff_sUnion_closed.mp
      hK.1 (S.image coe) _ _,
    { simp only [finset.mem_image, exists_prop, forall_exists_index, and_imp],
      rintro _ z hz rfl,
      exact z.2 },
    { exact (set.subset_univ _).trans ((congr_arg coe hS₂).trans $ by simp).subset } },
  obtain ⟨s, hs, e⟩ := finset.mem_image.mp hz,
  rw ← e at hz',
  refine ⟨s, hs, _⟩,
  symmetry,
  suffices : K ≤ s, { exact this.antisymm (hK.2 (hS₁ ⟨s, hs⟩) this) },
  simpa,
end

end topological_space
