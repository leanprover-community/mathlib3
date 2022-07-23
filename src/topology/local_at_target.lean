/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.sets.opens

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `inducing`
- `embedding`
- `open_embedding`
- `closed_embedding`

-/

lemma set.maps_to.coe_restrict {α β : Type*} {f : α → β} {s : set α} {t : set β}
(h : set.maps_to f s t) :
  coe ∘ h.restrict f s t = s.restrict f := rfl

open topological_space set filter
open_locale topological_space filter

variables {α β : Type*} [topological_space α] [topological_space β] {f : α → β}
variables {s : set β} {ι : Type*} (U : ι → opens β) (hU : supr U = ⊤)

/-- The restriction of a continuous map onto the preimage of a set. -/
@[simps]
def continuous_map.restrict_preimage (f : C(α, β)) (s : set β) : C(f ⁻¹' s, s) :=
⟨s.restrict_preimage f, continuous_iff_continuous_at.mpr $ λ x, f.2.continuous_at.restrict_preimage⟩

include hU

lemma open_iff_inter_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (s ∩ U i) :=
begin
  split,
  { exact λ H i, H.inter (U i).2 },
  { intro H,
    have : (⋃ i, (U i : set β)) = set.univ := by { convert (congr_arg coe hU), simp },
    rw [← s.inter_univ, ← this, set.inter_Union],
    exact is_open_Union H }
end

lemma open_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (coe ⁻¹' s : set (U i)) :=
begin
  simp_rw [(U _).2.open_embedding_subtype_coe.open_iff_image_open,
    set.image_preimage_eq_inter_range, subtype.range_coe],
  apply open_iff_inter_of_supr_eq_top,
  assumption
end

lemma closed_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_closed s ↔ ∀ i, is_closed (coe ⁻¹' s : set (U i)) :=
by simpa using open_iff_coe_preimage_of_supr_eq_top _ hU sᶜ


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

attribute [mk_iff] open_embedding closed_embedding

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
  { simp_rw set.range_restrict_preimage, apply open_iff_coe_preimage_of_supr_eq_top U hU }
end

lemma closed_embedding_iff_closed_embedding_of_supr_eq_top (h : continuous f) :
  closed_embedding f ↔ ∀ i, closed_embedding ((U i).1.restrict_preimage f) :=
begin
  simp_rw closed_embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply embedding_iff_embedding_of_supr_eq_top; assumption },
  { simp_rw set.range_restrict_preimage, apply closed_iff_coe_preimage_of_supr_eq_top U hU }
end
