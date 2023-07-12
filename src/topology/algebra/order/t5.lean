/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.order.basic
import data.set.intervals.ord_connected_component

/-!
# Linear order is a completely normal Hausdorff topological space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a linear order with order topology is a completely normal Hausdorff
topological space.
-/

open filter set function order_dual
open_locale topology filter interval

variables {X : Type*} [linear_order X] [topological_space X] [order_topology X]
  {a b c : X} {s t : set X}

namespace set

@[simp] lemma ord_connected_component_mem_nhds :
  ord_connected_component s a ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
begin
  refine ⟨λ h, mem_of_superset h ord_connected_component_subset, λ h, _⟩,
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩,
  exact mem_of_superset ha' (subset_ord_connected_component ha hs)
end

lemma compl_section_ord_separating_set_mem_nhds_within_Ici (hd : disjoint s (closure t))
  (ha : a ∈ s) :
  (ord_connected_section $ ord_separating_set s t)ᶜ ∈ 𝓝[≥] a :=
begin
  have hmem : tᶜ ∈ 𝓝[≥] a,
  { refine mem_nhds_within_of_mem_nhds _,
    rw [← mem_interior_iff_mem_nhds, interior_compl],
    exact disjoint_left.1 hd ha },
  rcases exists_Icc_mem_subset_of_mem_nhds_within_Ici hmem with ⟨b, hab, hmem', hsub⟩,
  by_cases H : disjoint (Icc a b) (ord_connected_section $ ord_separating_set s t),
  { exact mem_of_superset hmem' (disjoint_left.1 H) },
  { simp only [set.disjoint_left, not_forall, not_not] at H,
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩,
    have hsub' : Icc a b ⊆ ord_connected_component tᶜ a,
      from subset_ord_connected_component (left_mem_Icc.2 hab) hsub,
    replace hac : a < c := hac.lt_of_ne (ne.symm $ ne_of_mem_of_not_mem hc $ disjoint_left.1
      (disjoint_left_ord_separating_set.mono_right ord_connected_section_subset) ha),
    refine mem_of_superset (Ico_mem_nhds_within_Ici (left_mem_Ico.2 hac)) (λ x hx hx', _),
    refine hx.2.ne (eq_of_mem_ord_connected_section_of_uIcc_subset hx' hc _),
    refine subset_inter (subset_Union₂_of_subset a ha _) _,
    { exact ord_connected.uIcc_subset infer_instance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩) },
    { rcases mem_Union₂.1 (ord_connected_section_subset hx').2 with ⟨y, hyt, hxy⟩,
      refine subset_Union₂_of_subset y hyt (ord_connected.uIcc_subset infer_instance hxy _),
      refine subset_ord_connected_component left_mem_uIcc hxy _,
      suffices : c < y,
      { rw [uIcc_of_ge (hx.2.trans this).le],
        exact ⟨hx.2.le, this.le⟩ },
      refine lt_of_not_le (λ hyc, _),
      have hya : y < a, from not_le.1 (λ hay, hsub ⟨hay, hyc.trans hcb⟩ hyt),
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha } }
end

lemma compl_section_ord_separating_set_mem_nhds_within_Iic (hd : disjoint s (closure t))
  (ha : a ∈ s) : (ord_connected_section $ ord_separating_set s t)ᶜ ∈ 𝓝[≤] a :=
have hd' : disjoint (of_dual ⁻¹' s) (closure $ of_dual ⁻¹' t) := hd,
have ha' : to_dual a ∈ of_dual ⁻¹' s := ha,
by simpa only [dual_ord_separating_set, dual_ord_connected_section]
  using compl_section_ord_separating_set_mem_nhds_within_Ici hd' ha'

lemma compl_section_ord_separating_set_mem_nhds (hd : disjoint s (closure t)) (ha : a ∈ s) :
  (ord_connected_section $ ord_separating_set s t)ᶜ ∈ 𝓝 a :=
begin
  rw [← nhds_left_sup_nhds_right, mem_sup],
  exact ⟨compl_section_ord_separating_set_mem_nhds_within_Iic hd ha,
    compl_section_ord_separating_set_mem_nhds_within_Ici hd ha⟩
end

lemma ord_t5_nhd_mem_nhds_set (hd : disjoint s (closure t)) : ord_t5_nhd s t ∈ 𝓝ˢ s :=
bUnion_mem_nhds_set $ λ x hx, ord_connected_component_mem_nhds.2 $
  inter_mem (by { rw [← mem_interior_iff_mem_nhds, interior_compl], exact disjoint_left.1 hd hx })
    (compl_section_ord_separating_set_mem_nhds hd hx)

end set

open set

/-- A linear order with order topology is a completely normal Hausdorff topological space. -/
@[priority 100] instance order_topology.t5_space : t5_space X :=
⟨λ s t h₁ h₂, filter.disjoint_iff.2 ⟨ord_t5_nhd s t, ord_t5_nhd_mem_nhds_set h₂, ord_t5_nhd t s,
  ord_t5_nhd_mem_nhds_set h₁.symm, disjoint_ord_t5_nhd⟩⟩
