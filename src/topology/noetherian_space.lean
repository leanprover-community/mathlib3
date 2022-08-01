/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import order.compactly_generated
import order.order_iso_nat
import topology.sets.compacts

/-!
# Noetherian space

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
is_compact_univ_iff.mp ((noetherian_space_iff_opens α).mp h ⊤)

variable {α}

instance noetherian_space.set [h : noetherian_space α] (s : set α) : noetherian_space s :=
begin
  rw noetherian_space_iff,
  apply well_founded.well_founded_iff_has_max'.2,
  intros p hp,
  obtain ⟨⟨_, u, hu, rfl⟩, hu'⟩ := hp,
  obtain ⟨U, hU, hU'⟩ := well_founded.well_founded_iff_has_max'.1 h.1
    (((opens.comap ⟨_, continuous_subtype_coe⟩)) ⁻¹' p) ⟨⟨u, hu⟩, hu'⟩,
  refine ⟨opens.comap ⟨_, continuous_subtype_coe⟩ U, hU, _⟩,
  rintros ⟨_, x, hx, rfl⟩ hx' hx'',
  refine le_antisymm (set.preimage_mono (_ : (⟨x, hx⟩ : opens α) ≤ U)) hx'',
  refine sup_eq_right.mp (hU' (⟨x, hx⟩ ⊔ U) _ le_sup_right),
  dsimp [set.preimage],
  rw map_sup,
  convert hx',
  exact sup_eq_left.mpr hx''
end

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
  { intros H s, rw is_compact_iff_compact_space, resetI, apply_instance },
  tfae_have : 3 → 4,
  { exact λ H s, H s },
  tfae_finish
end

variables {α β}

lemma noetherian_space.is_compact [h : noetherian_space α] (s : set α) : is_compact s :=
let H := (noetherian_space_tfae α).out 0 2 in H.mp h s

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
    simv }
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
  exact compact_Union (λ i, hf i _ (set.inter_subset_right _ _))
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
begin
  casesI nonempty_fintype α,
  classical,
  exact ⟨@@fintype.well_founded_of_trans_of_irrefl (subtype.fintype _) _ _ _⟩
end

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
    simv only [coe_coe, finset.sup_singleton, id.def, eq_self_iff_true, and_true],
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
  (set.range irreducible_component : set (set α)).finite :=
begin
  classical,
  obtain ⟨S, hS₁, hS₂⟩ := noetherian_space.exists_finset_irreducible (⊤ : closeds α),
  suffices : ∀ x : α, ∃ s : S, irreducible_component x = s,
  { choose f hf,
    rw [show irreducible_component = coe ∘ f, from funext hf, set.range_comp],
    exact (set.finite.intro infer_instance).image _ },
  intro x,
  obtain ⟨z, hz, hz'⟩ : ∃ (z : set α) (H : z ∈ finset.image coe S), irreducible_component x ⊆ z,
  { convert is_irreducible_iff_sUnion_closed.mp
      is_irreducible_irreducible_component (S.image coe) _ _,
    { apply_instance },
    { simv only [finset.mem_image, exists_prop, forall_exists_index, and_imp],
      rintro _ z hz rfl,
      exact z.2 },
    { exact (set.subset_univ _).trans ((congr_arg coe hS₂).trans $ by simv).subset } },
  obtain ⟨s, hs, e⟩ := finset.mem_image.mp hz,
  rw ← e at hz',
  use ⟨s, hs⟩,
  symmetry,
  apply eq_irreducible_component (hS₁ _).2,
  simpa,
end

end topological_space
