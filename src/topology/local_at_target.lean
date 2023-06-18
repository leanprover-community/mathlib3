/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.sets.opens

/-!
# Properties of maps that are local at the target.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that the following properties of continuous maps are local at the target :
- `inducing`
- `embedding`
- `open_embedding`
- `closed_embedding`

-/

open topological_space set filter
open_locale topology filter

variables {α β : Type*} [topological_space α] [topological_space β] {f : α → β}
variables {s : set β} {ι : Type*} {U : ι → opens β} (hU : supr U = ⊤)

lemma set.restrict_preimage_inducing (s : set β) (h : inducing f) :
  inducing (s.restrict_preimage f) :=
begin
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @filter.comap_comap _ _ _ _ coe f] at h ⊢,
  intros a,
  rw [← h, ← inducing_coe.nhds_eq_comap],
end

alias set.restrict_preimage_inducing ← inducing.restrict_preimage

lemma set.restrict_preimage_embedding (s : set β) (h : embedding f) :
  embedding (s.restrict_preimage f) :=
⟨h.1.restrict_preimage s, h.2.restrict_preimage s⟩

alias set.restrict_preimage_embedding ← embedding.restrict_preimage

lemma set.restrict_preimage_open_embedding (s : set β) (h : open_embedding f) :
  open_embedding (s.restrict_preimage f) :=
⟨h.1.restrict_preimage s,
  (s.range_restrict_preimage f).symm ▸ continuous_subtype_coe.is_open_preimage _ h.2⟩

alias set.restrict_preimage_open_embedding ← open_embedding.restrict_preimage

lemma set.restrict_preimage_closed_embedding (s : set β) (h : closed_embedding f) :
  closed_embedding (s.restrict_preimage f) :=
⟨h.1.restrict_preimage s,
  (s.range_restrict_preimage f).symm ▸ inducing_coe.is_closed_preimage _ h.2⟩

alias set.restrict_preimage_closed_embedding ← closed_embedding.restrict_preimage

lemma set.restrict_preimage_is_closed_map (s : set β) (H : is_closed_map f)  :
  is_closed_map (s.restrict_preimage f) :=
begin
  rintros t ⟨u, hu, e⟩,
  refine ⟨⟨_, (H _ (is_open.is_closed_compl hu)).1, _⟩⟩,
  rw ← (congr_arg has_compl.compl e).trans (compl_compl t),
  simp only [set.preimage_compl, compl_inj_iff],
  ext ⟨x, hx⟩,
  suffices : (∃ y, y ∉ u ∧ f y = x) ↔ ∃ y, f y ∈ s ∧ y ∉ u ∧ f y = x,
  { simpa [set.restrict_preimage, ← subtype.coe_inj] },
  exact ⟨λ ⟨a, b, c⟩, ⟨a, c.symm ▸ hx, b, c⟩, λ ⟨a, _, b, c⟩, ⟨a, b, c⟩⟩
end

include hU

lemma is_open_iff_inter_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (s ∩ U i) :=
begin
  split,
  { exact λ H i, H.inter (U i).2 },
  { intro H,
    have : (⋃ i, (U i : set β)) = set.univ := by { convert (congr_arg coe hU), simp },
    rw [← s.inter_univ, ← this, set.inter_Union],
    exact is_open_Union H }
end

lemma is_open_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (coe ⁻¹' s : set (U i)) :=
begin
  simp_rw [(U _).2.open_embedding_subtype_coe.open_iff_image_open,
    set.image_preimage_eq_inter_range, subtype.range_coe],
  apply is_open_iff_inter_of_supr_eq_top,
  assumption
end

lemma is_closed_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_closed s ↔ ∀ i, is_closed (coe ⁻¹' s : set (U i)) :=
by simpa using is_open_iff_coe_preimage_of_supr_eq_top hU sᶜ

lemma is_closed_map_iff_is_closed_map_of_supr_eq_top :
  is_closed_map f ↔ ∀ i, is_closed_map ((U i).1.restrict_preimage f) :=
begin
  refine ⟨λ h i, set.restrict_preimage_is_closed_map _ h, _⟩,
  rintros H s hs,
  rw is_closed_iff_coe_preimage_of_supr_eq_top hU,
  intro i,
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩,
  ext ⟨x, hx⟩,
  suffices : (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, f y ∈ U i ∧ y ∈ s ∧ f y = x,
  { simpa [set.restrict_preimage, ← subtype.coe_inj] },
  exact ⟨λ ⟨a, b, c⟩, ⟨a, c.symm ▸ hx, b, c⟩, λ ⟨a, _, b, c⟩, ⟨a, b, c⟩⟩
end

lemma inducing_iff_inducing_of_supr_eq_top (h : continuous f) :
  inducing f ↔ ∀ i, inducing ((U i).1.restrict_preimage f) :=
begin
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @filter.comap_comap _ _ _ _ coe f],
  split,
  { intros H i x, rw [← H, ← inducing_coe.nhds_eq_comap] },
  { intros H x,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp (show f x ∈ supr U, by { rw hU, triv }),
    erw ← open_embedding.map_nhds_eq (h.1 _ (U i).2).open_embedding_subtype_coe ⟨x, hi⟩,
    rw [(H i) ⟨x, hi⟩, filter.subtype_coe_map_comap, function.comp_apply, subtype.coe_mk,
      inf_eq_left, filter.le_principal_iff],
    exact filter.preimage_mem_comap ((U i).2.mem_nhds hi) }
end

lemma embedding_iff_embedding_of_supr_eq_top (h : continuous f) :
  embedding f ↔ ∀ i, embedding ((U i).1.restrict_preimage f) :=
begin
  simp_rw embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply inducing_iff_inducing_of_supr_eq_top; assumption },
  { apply set.injective_iff_injective_of_Union_eq_univ, convert (congr_arg coe hU), simp }
end

lemma open_embedding_iff_open_embedding_of_supr_eq_top (h : continuous f) :
  open_embedding f ↔ ∀ i, open_embedding ((U i).1.restrict_preimage f) :=
begin
  simp_rw open_embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply embedding_iff_embedding_of_supr_eq_top; assumption },
  { simp_rw set.range_restrict_preimage, apply is_open_iff_coe_preimage_of_supr_eq_top hU }
end

lemma closed_embedding_iff_closed_embedding_of_supr_eq_top (h : continuous f) :
  closed_embedding f ↔ ∀ i, closed_embedding ((U i).1.restrict_preimage f) :=
begin
  simp_rw closed_embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply embedding_iff_embedding_of_supr_eq_top; assumption },
  { simp_rw set.range_restrict_preimage, apply is_closed_iff_coe_preimage_of_supr_eq_top hU }
end
