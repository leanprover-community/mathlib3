/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.maps
import topology.sets.opens
import topology.metric_space.basic

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `inducing`
- `embedding`
- `open_embedding`
- `closed_embedding`

-/

open topological_space

variables {α β : Type*} [topological_space α] [topological_space β] (f : α → β) (h : continuous f)
variables {s : set β} {ι : Type*} (U : ι → opens β) (hU : supr U = ⊤)

lemma continuous_at.restrict_preimage (s : set β) (x : f ⁻¹' s)
  (h : continuous_at f x) : continuous_at (s.restrict_preimage f) x :=
begin
  intros U hU,
  obtain ⟨_, e, ⟨V, hV, rfl⟩, hx⟩ := mem_nhds_iff.mp hU,
  have := h (is_open.mem_nhds hV hx),
  rw [filter.mem_map, mem_nhds_iff] at this ⊢,
  obtain ⟨W, e', hW, hx'⟩ := this,
  use coe ⁻¹' W,
  refine ⟨_, continuous_subtype_coe.1 _ hW, hx'⟩,
  intros y hy,
  apply e,
  exact e' hy
end

/-- The restriction of a continuous map onto the preimage of a set. -/
@[simps]
def continuous_map.restrict_preimage {α β : Type*} [topological_space α] [topological_space β]
  (f : C(α, β)) (s : set β) : C(f ⁻¹' s, s) :=
⟨s.restrict_preimage f, by { rw continuous_iff_continuous_at, intro x,
  apply continuous_at.restrict_preimage f s, exact f.2.continuous_at }⟩

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
begin
  let t := sᶜ, have : s = tᶜ := by simp[t], clear_value t, subst this,
  simpa using open_iff_coe_preimage_of_supr_eq_top _ hU t,
end

include h

lemma inducing_iff_inducing_of_supr_eq_top :
  inducing f ↔ ∀ i, inducing ((U i).1.restrict_preimage f) :=
begin
  split,
  { intros H i, constructor, ext U, split,
    { rintro ⟨V, hV, rfl⟩,
      obtain ⟨s, hs, rfl⟩ := H.is_open_iff.mp hV,
      exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩ },
    { rintro ⟨_, ⟨V, hV, rfl⟩, rfl⟩,
      exact ⟨_, H.is_open_iff.mpr ⟨_, hV, rfl⟩, rfl⟩ } },
  { intros H, constructor,
    rw induced_iff_nhds_eq,
    intro x,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp (show f x ∈ supr U, by { rw hU, triv }),
    erw ← open_embedding.map_nhds_eq (h.1 _ (U i).2).open_embedding_subtype_coe ⟨x, hi⟩,
    rw (induced_iff_nhds_eq _).mp (H i).1 ⟨x, hi⟩,
    erw (induced_iff_nhds_eq (coe : (U i).1 → β)).mp embedding_subtype_coe.to_inducing.1 ⟨_, hi⟩,
    rw [filter.comap_comap, (show coe ∘ (U i).val.restrict_preimage f = f ∘ coe, from rfl),
      subtype.coe_mk, ← filter.comap_comap, filter.subtype_coe_map_comap, inf_eq_left],
    intros S hS,
    rw filter.mem_comap,
    exact ⟨U i, (U i).2.mem_nhds hi, hS⟩ }
end

attribute [mk_iff] open_embedding closed_embedding

lemma embedding_iff_embedding_of_supr_eq_top (h : continuous f) :
  embedding f ↔ ∀ i, embedding ((U i).1.restrict_preimage f) :=
begin
  simp_rw embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply inducing_iff_inducing_of_supr_eq_top; assumption },
  { apply injective_iff_injective_of_Union_eq_univ, convert (congr_arg coe hU), simp }
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
