import topology.algebra.order.basic

/-!
-/

open filter set function order_dual
open_locale topological_space filter interval

variables {X : Type*} [linear_order X] {a b c : X} {s t : set X}

@[simp] lemma ord_connected_component_mem_nhds [topological_space X] [order_topology X] :
  ord_connected_component s a ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
begin
  refine ⟨λ h, mem_of_superset h ord_connected_component_subset, λ h, _⟩,
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩,
  exact mem_of_superset ha' (subset_ord_connected_component ha hs)
end

namespace order_normal

def sep_set (s t : set X) : set X :=
(⋃ x ∈ s, ord_connected_component tᶜ x) ∩ (⋃ x ∈ t, ord_connected_component sᶜ x)

lemma sep_set_comm (s t : set X) : sep_set s t = sep_set t s := inter_comm _ _

lemma disjoint_left_sep_set : disjoint s (sep_set s t) :=
disjoint.inter_right' _ $ disjoint_Union₂_right.2 $ λ x hx, disjoint_compl_right.mono_right $
  ord_connected_component_subset

lemma disjoint_right_sep_set : disjoint t (sep_set s t) :=
sep_set_comm t s ▸ disjoint_left_sep_set

lemma dual_sep_set : sep_set (of_dual ⁻¹' s) (of_dual ⁻¹' t) = of_dual ⁻¹' (sep_set s t) :=
by simp only [sep_set, mem_preimage, ← to_dual.surjective.Union_comp, of_dual_to_dual,
  dual_ord_connected_component, ← preimage_compl, preimage_inter, preimage_Union]

variables [topological_space X] [order_topology X]

lemma compl_section_sep_set_mem_nhds_within_Ici (hd : disjoint s (closure t)) (ha : a ∈ s) :
  (ord_connected_section $ sep_set s t)ᶜ ∈ 𝓝[≥] a :=
begin
  have hmem : tᶜ ∈ 𝓝[≥] a,
  { refine mem_nhds_within_of_mem_nhds _,
    rw [← mem_interior_iff_mem_nhds, interior_compl],
    exact disjoint_left.1 hd ha },
  rcases exists_Icc_mem_subset_of_mem_nhds_within_Ici hmem with ⟨b, hab, hmem', hsub⟩,
  by_cases H : disjoint (Icc a b) (ord_connected_section $ sep_set s t),
  { exact mem_of_superset hmem' (disjoint_left.1 H) },
  { simp only [set.disjoint_left, not_forall, not_not] at H,
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩,
    have hsub' : Icc a b ⊆ ord_connected_component tᶜ a,
      from subset_ord_connected_component (left_mem_Icc.2 hab) hsub,
    replace hac : a < c := hac.lt_of_ne (ne.symm $ ne_of_mem_of_not_mem hc $
      disjoint_left.1 (disjoint_left_sep_set.mono_right ord_connected_section_subset) ha),
    refine mem_of_superset (Ico_mem_nhds_within_Ici (left_mem_Ico.2 hac)) (λ x hx hx', _),
    refine hx.2.ne (eq_of_mem_ord_connected_section_of_interval_subset hx' hc _),
    refine subset_inter (subset_Union₂_of_subset a ha _) _,
    { exact ord_connected.interval_subset infer_instance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩) },
    { rcases mem_Union₂.1 (ord_connected_section_subset hx').2 with ⟨y, hyt, hxy⟩,
      refine subset_Union₂_of_subset y hyt (ord_connected.interval_subset infer_instance hxy _),
      refine subset_ord_connected_component left_mem_interval hxy _,
      suffices : c < y,
      { rw [interval_of_ge (hx.2.trans this).le],
        exact ⟨hx.2.le, this.le⟩ },
      refine lt_of_not_le (λ hyc, _),
      have hya : y < a, from not_le.1 (λ hay, hsub ⟨hay, hyc.trans hcb⟩ hyt),
      exact hxy (Icc_subset_interval ⟨hya.le, hx.1⟩) ha } }
end

lemma compl_section_sep_set_mem_nhds_within_Iic (hd : disjoint s (closure t)) (ha : a ∈ s) :
  (ord_connected_section $ sep_set s t)ᶜ ∈ 𝓝[≤] a :=
have hd' : disjoint (of_dual ⁻¹' s) (closure $ of_dual ⁻¹' t) := hd,
have ha' : to_dual a ∈ of_dual ⁻¹' s := ha,
by simpa only [dual_sep_set, dual_ord_connected_section]
  using compl_section_sep_set_mem_nhds_within_Ici hd' ha'

lemma compl_section_sep_set_mem_nhds (hd : disjoint s (closure t)) (ha : a ∈ s) :
  (ord_connected_section $ sep_set s t)ᶜ ∈ 𝓝 a :=
begin
  rw [← nhds_left_sup_nhds_right, mem_sup],
  exact ⟨compl_section_sep_set_mem_nhds_within_Iic hd ha,
    compl_section_sep_set_mem_nhds_within_Ici hd ha⟩
end

def nhd (s t : set X) : set X :=
⋃ x ∈ s, ord_connected_component (tᶜ ∩ (ord_connected_section $ sep_set s t)ᶜ) x

lemma nhd_mem_nhds_set (hd : disjoint s (closure t)) : nhd s t ∈ 𝓝ˢ s :=
bUnion_mem_nhds_set $ λ x hx, ord_connected_component_mem_nhds.2 $
  inter_mem (by { rw [← mem_interior_iff_mem_nhds, interior_compl], exact disjoint_left.1 hd hx })
    (compl_section_sep_set_mem_nhds hd hx)

lemma disjoint_nhd : disjoint (nhd s t) (nhd t s) :=
begin
  rintro x ⟨hx₁, hx₂⟩,
  rcases mem_Union₂.1 hx₁ with ⟨a, has, ha⟩, clear hx₁,
  rcases mem_Union₂.1 hx₂ with ⟨b, hbt, hb⟩, clear hx₂,
  rw [mem_ord_connected_component, subset_inter_iff] at ha hb,
  wlog hab : a ≤ b := le_total a b using [a b s t, b a t s] tactic.skip,
  rotate, from λ h₁ h₂ h₃ h₄, this h₂ h₁ h₄ h₃,
  cases ha with ha ha', cases hb with hb hb',
  have hsub : [a, b] ⊆ (sep_set s t).ord_connected_sectionᶜ,
  { rw [sep_set_comm, interval_swap] at hb',
    calc [a, b] ⊆ [a, x] ∪ [x, b] : interval_subset_interval_union_interval
    ... ⊆ (sep_set s t).ord_connected_sectionᶜ : union_subset ha' hb' },
  clear ha' hb',
  cases le_total x a with hxa hax,
  { exact hb (Icc_subset_interval' ⟨hxa, hab⟩) has },
  cases le_total b x with hbx hxb,
  { exact ha (Icc_subset_interval ⟨hab, hbx⟩) hbt },
  have : x ∈ sep_set s t,
  { exact ⟨mem_Union₂.2 ⟨a, has, ha⟩, mem_Union₂.2 ⟨b, hbt, hb⟩⟩ },
  lift x to sep_set s t using this,
  suffices : ord_connected_component (sep_set s t) x ⊆ [a, b],
    from hsub (this $ ord_connected_proj_mem_ord_connected_component _ _) (mem_range_self _),
  rintros y (hy : [↑x, y] ⊆ sep_set s t),
  rw [interval_of_le hab, mem_Icc, ← not_lt, ← not_lt],
  refine ⟨λ hya, _, λ hyb, _⟩,
  { exact disjoint_left.1 disjoint_left_sep_set has (hy $ Icc_subset_interval' ⟨hya.le, hax⟩) },
  { exact disjoint_left.1 disjoint_right_sep_set hbt (hy $ Icc_subset_interval ⟨hxb, hyb.le⟩) }
end

lemma t5 (h₁ : disjoint (closure s) t) (h₂ : disjoint s (closure t)) :
  disjoint (𝓝ˢ s) (𝓝ˢ t) :=
filter.disjoint_iff.2
  ⟨nhd s t, nhd_mem_nhds_set h₂, nhd t s, nhd_mem_nhds_set h₁.symm, disjoint_nhd⟩

end order_normal

instance order_topology.t5_space [topological_space X] [order_topology X] : t5_space X :=
⟨λ s t, order_normal.t5⟩
