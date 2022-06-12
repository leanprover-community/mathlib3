/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.closure
import logic.relation

/-!
# Transitive neighborhood relation in simplicial complexes
-/

open finset geometry relation

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [decidable_eq E] [module 𝕜 E] {a b m n : ℕ}
  {S S' S₁ S₂ : simplicial_complex 𝕜 E} {s t u : finset E}

def adjacent (s t : finset E) : Prop := s.card = (s ∩ t).card + 1 ∧ t.card = (t ∩ s).card + 1

lemma adjacent.symm : symmetric (adjacent : finset E → finset E → Prop) := λ s t, and.symm

lemma adjacent_comm : adjacent s t ↔ adjacent t s := ⟨λ h, h.symm, λ h, h.symm⟩

lemma adjacent.card_eq (h : adjacent s t) : t.card = s.card := h.2.trans $ by rw [inter_comm, h.1]

def glued (S : simplicial_complex 𝕜 E) : finset E → finset E → Prop :=
refl_trans_gen (λ s t, adjacent s t ∧ s ∈ S.facets ∧ t ∈ S.facets)

@[refl] lemma glued.refl (s : finset E) : S.glued s s := refl_trans_gen.refl
lemma glued.rfl : S.glued s s := glued.refl _

lemma glued.symm : symmetric S.glued :=
refl_trans_gen.symmetric $ λ s t ⟨hst, hs, ht⟩, ⟨hst.symm, ht, hs⟩

lemma glued_comm : S.glued s t ↔ S.glued t s := ⟨λ h, h.symm, λ h, h.symm⟩

lemma glued.transitive : transitive S.glued := transitive_refl_trans_gen

@[trans] lemma glued.trans (hst : S.glued s t) : S.glued t u → S.glued s u := glued.transitive hst

instance : is_equiv (finset E) S.glued :=
{ refl := reflexive_refl_trans_gen,
  trans := transitive_refl_trans_gen,
  symm := glued.symm }

lemma glued.mem_faces (hst : S.glued s t) (hs : s ∈ S.faces) : t ∈ S.faces :=
begin
  cases refl_trans_gen.cases_tail hst,
  { rw h,
    exact hs },
  { obtain ⟨W, _, _, _, ht⟩ := h,
    exact ht.1 }
end

lemma glued.mem_facets (hst : S.glued s t) (hs : s ∈ S.facets) : t ∈ S.facets :=
begin
  cases refl_trans_gen.cases_tail hst,
  { rw h,
    exact hs },
  { obtain ⟨W, _, _, _, ht⟩ := h,
    exact ht }
end

lemma glued.card_eq (ht : S.glued s t) : t.card = s.card :=
refl_trans_gen.trans_induction_on ht (λ _, rfl) (λ s t h, h.1.card_eq)
  (λ s t u _ _ hts hut, hut.trans hts)

lemma set_of_glued_subset (hs : s ∈ S.faces) :  set_of (S.glued s) ⊆ S.faces :=
λ t ht, ht.mem_faces hs

lemma set_of_glued_antichain : is_antichain (⊆) {t | S.glued s t} :=
λ t ht u hu h htu, h $ eq_of_subset_of_card_le htu $ le_of_eq $ by rw [ht.card_eq, hu.card_eq]

def pure_decomp (S : simplicial_complex 𝕜 E) : set (simplicial_complex 𝕜 E) :=
(λ s, S.closure {t | S.glued s t}) '' S.facets

lemma le_of_mem_pure_decomp (hS : S' ∈ S.pure_decomp) : S' ≤ S :=
by { obtain ⟨_, _, rfl⟩ := hS, exact closure_le }

lemma card_le_of_mem_element_pure_decomp (ht : t ∈ (S.closure {t | S.glued s t}).faces) :
  t.card ≤ s.card :=
by { obtain ⟨ht, u, hu, htu⟩ := ht, rw ←hu.card_eq, exact finset.card_le_of_subset htu }

lemma facet_pure_decomp_self (hs : s ∈ S.faces) : s ∈ (S.closure {t | S.glued s t}).facets :=
⟨⟨hs, ⟨s, glued.rfl, subset.rfl⟩⟩, (λ t ht hst, finset.eq_of_subset_of_card_le hst
  (card_le_of_mem_element_pure_decomp ht))⟩

lemma mem_pure_decomp_facets_iff (hs : s ∈ S.faces) :
  t ∈ (S.closure {t | S.glued s t}).facets ↔ S.glued s t :=
by rw [facets_closure_eq (set_of_glued_subset hs) set_of_glued_antichain, set.mem_set_of]

lemma pure_decomp_facet_iff (hS : S' ∈ S.pure_decomp) :
  s ∈ S'.facets ↔ s ∈ S.faces ∧ S' = S.closure {t | S.glued s t} :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain ⟨t, ht, rfl⟩ := hS,
    use closure_le (facets_subset hs),
    rw mem_pure_decomp_facets_iff ht.1 at hs,
    rw ←curry_eq_of_symmetric_transitive glued.symm glued.transitive hs },
  { rintro ⟨hs, rfl⟩,
    exact ⟨faces_subset_closure ⟨hs, glued.rfl⟩, (λ t ht hst,
      finset.eq_of_subset_of_card_le hst (card_le_of_mem_element_pure_decomp ht))⟩ }
end

lemma pure_decomp_cover_facets (hs : s ∈ S.facets) :
  ∃ S' : simplicial_complex 𝕜 E, S' ∈ S.pure_decomp ∧ s ∈ S'.facets :=
⟨S.closure {t | S.glued s t}, set.mem_image_of_mem _ hs, faces_subset_closure ⟨hs.1, glued.rfl⟩,
  λ t ht, hs.2 $ closure_le ht⟩

lemma pure_decomp_disjoint_facets (hS₁ : S₁ ∈ S.pure_decomp) (hS₂ : S₂ ∈ S.pure_decomp)
  (hs : s ∈ S.facets) (hs₁ : s ∈ S₁.facets) (hs₂ : s ∈ S₂.facets) :
  S₁ = S₂ :=
begin
  obtain ⟨t₁, ht₁, rfl⟩ := hS₁,
  obtain ⟨t₂, ht₂, rfl⟩ := hS₂,
  simp at ⊢ hs₁ hs₂,
  rw mem_pure_decomp_facets_iff ht₁.1 at hs₁,
  rw mem_pure_decomp_facets_iff ht₂.1 at hs₂,
  rw ←curry_eq_of_symmetric_transitive glued.symm glued.transitive (hs₁.trans hs₂.symm),
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [decidable_eq E] [module 𝕜 E] {a b m n : ℕ}
  {S S' S₁ S₂ : simplicial_complex 𝕜 E} {s t u : finset E}

lemma pure_decomp_cover [finite_dimensional 𝕜 E] (hs : s ∈ S.faces) :
  ∃ S' : simplicial_complex 𝕜 E, S' ∈ S.pure_decomp ∧ s ∈ S'.faces :=
let ⟨t, ht, hst⟩ := subfacet hs in (pure_decomp_cover_facets ht).imp $ λ S',
  and.imp_right $ λ htS', S'.down_closed htS'.1 hst $ S.nonempty hs

lemma pure_decomp_facets_subset (hS : S' ∈ S.pure_decomp) (hs : s ∈ S'.facets) : s ∈ S.facets :=
by { obtain ⟨t, ht, rfl⟩ := hS, exact ((mem_pure_decomp_facets_iff ht.1).1 hs).mem_facets ht }

--lemma pure_decomp_facets_partition :

lemma pure_of_mem_pure_decomp (hS : S' ∈ S.pure_decomp) : ∃ n, S'.pure n :=
begin
  obtain ⟨t, ht, rfl⟩ := hS,
  refine ⟨t.card, λ s hs, ((mem_pure_decomp_facets_iff ht.1).1 ⟨hs, sorry⟩).card_eq.trans_le
    le_self_add, sorry⟩,
end

lemma pure_of_pure_decomp_singleton (hS : S.pure_decomp = {S}) : ∃ n, S.pure n :=
begin
  refine pure_of_mem_pure_decomp (_ : S ∈ S.pure_decomp),
  rw hS,
  exact set.mem_singleton _,
end

lemma pure_decomp_space_subset_space :
  (⋃ (S' ∈ S.pure_decomp), (S' : simplicial_complex 𝕜 E).space) ⊆ S.space :=
set.Union₂_subset $ λ S' hS' x hx, let ⟨s, hs, hxs⟩ := mem_space_iff.1 hx in
  mem_space_iff.2 ⟨s, le_of_mem_pure_decomp hS' hs, hxs⟩

lemma pure_decomp_space_eq_space [finite_dimensional 𝕜 E] :
  (⋃ (S' ∈ S.pure_decomp), (S' : simplicial_complex 𝕜 E).space) = S.space :=
begin
  refine pure_decomp_space_subset_space.antisymm (λ x hx, _),
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx,
  obtain ⟨S', hS', hx⟩ := pure_decomp_cover hs,
  exact set.mem_bUnion hS' (mem_space_iff.2 ⟨s, hx, hxs⟩),
end

end linear_ordered_field
end geometry.simplicial_complex
