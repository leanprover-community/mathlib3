/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.bases
import order.filter.countable_Inter
import tactic.tfae

/-!
-/

open filter set topological_space
open_locale filter topological_space

variables {ι X Y : Type*} [topological_space X] [topological_space Y] {s t : set X}

def is_lindelof (s : set X) : Prop :=
∀ ⦃U : set (set X)⦄, (∀ u ∈ U, is_open u) → (s ⊆ ⋃₀ U) → ∃ V ⊆ U, countable V ∧ s ⊆ ⋃₀ V

lemma is_lindelof.countable_open_subcover (h : is_lindelof s) {U : ι → set X}
  (hU : ∀ i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
  ∃ I : set ι, countable I ∧ s ⊆ ⋃ i ∈ I, U i :=
begin
  rcases @h (range U) (forall_range_iff.2 hU) hsU with ⟨V, hVU, hVc, hsV⟩,
  haveI := hVc.to_encodable,
  choose i hi using λ v : V, @hVU v v.2,
  refine ⟨range i, countable_range _, _⟩,
  simpa only [bUnion_range, hi, ← sUnion_eq_Union]
end

lemma is_lindelof.countable_open_subcover₂ (h : is_lindelof s) {t : set ι} (U : Π i ∈ t, set X)
  (hU : ∀ i ∈ t, is_open (U i ‹_›)) (hsU : s ⊆ ⋃ i ∈ t, U i ‹i ∈ t›) :
  ∃ I ⊆ t, countable I ∧ s ⊆ ⋃ i ∈ I, U i (‹I ⊆ t› ‹i ∈ I›) :=
begin
  rw bUnion_eq_Union at hsU,
  rcases h.countable_open_subcover (λ i : t, hU i i.2) hsU with ⟨I, hIc, hsI⟩,
  refine ⟨coe '' I, subtype.coe_image_subset _ _, hIc.image _, _⟩,
  simpa [Union_coe_set] using hsI
end

lemma is_lindelof_of_exists_cluster_pt
  (h : ∀ (f : filter X) [ne_bot f] [countable_Inter_filter f], s ∈ f → ∃ a ∈ s, cluster_pt a f) :
  is_lindelof s :=
begin
  intros U hUo hsU,
  set p : set X → Prop := λ u, ∃ I ⊆ U, countable I ∧ s \ u ⊆ ⋃₀ I,
  have hp : ∀ S : set (set X), countable S → (∀ u ∈ S, p u) → p (⋂₀ S),
  { intros S hSc hS,
    choose! I hIU hIc hI using hS,
    refine ⟨⋃ u ∈ S, I u, Union₂_subset hIU, hSc.bUnion hIc, _⟩,
    simp only [bUnion_Union, sInter_eq_bInter, diff_Inter, sUnion_Union],
    exact Union₂_mono hI },
  have hp_mono : ∀ u v, p u → u ⊆ v → p v,
  { rintro u v ⟨I, hIU, hIc, hsub⟩ huv,
    exact ⟨I, hIU, hIc, (diff_subset_diff_right huv).trans hsub⟩ },
  set f : filter X := filter.of_countable_Inter {u | p u} hp hp_mono,
  have hf : ∀ {u}, u ∈ f ↔ p u := λ _, iff.rfl,
  suffices : ¬ne_bot f,
  { simp_rw [ne_bot_iff, not_not, ← empty_mem_iff_bot, hf, p, diff_empty] at this,
    exact this },
  introI hfne,
  have : s ∈ f,
  { refine ⟨∅, empty_subset _, countable_empty, _⟩,
    rw diff_self, exact empty_subset _ },
  rcases h _ this with ⟨x, hxs, hxf⟩,
  rcases hsU hxs with ⟨t, htU, hxt⟩,
  have : s \ t ∈ f,
  { refine ⟨{t}, singleton_subset_iff.2 htU, countable_singleton t, _⟩,
    rw [sdiff_sdiff_right_self, sUnion_singleton],
    exact inter_subset_right _ _ },
  rcases cluster_pt_iff.1 hxf ((hUo t htU).mem_nhds hxt) this with ⟨y, hy, -, hy'⟩,
  exact hy' hy
end

/-- A list of properties of a set that are equivalent to `is_lindelof`. Use one of
`is_lindelof_iff_*` or `is_lindelof.*` lemmas instead. -/
lemma is_lindelof_tfae (s : set X) :
  tfae [is_lindelof s,
    ∀ t : X → set X, (∀ x ∈ s, t x ∈ 𝓝 x) → ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, t x,
    ∀ t : X → set X, (∀ x ∈ s, t x ∈ 𝓝[s] x) → ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, t x,
    ∀ U : X → set X, (∀ x, is_open (U x)) → (∀ x, x ∈ U x) →
      ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, U x,
    ∀ T : set (set X), (∀ x ∈ s, ∃ t ∈ T, t ∈ 𝓝 x) → ∃ I ⊆ T, countable I ∧ s ⊆ ⋃₀ I,
    ∀ T : set (set X), (∀ x ∈ s, ∃ t ∈ T, t ∈ 𝓝[s] x) → ∃ I ⊆ T, countable I ∧ s ⊆ ⋃₀ I,
    ∀ ⦃f⦄ [ne_bot f] [countable_Inter_filter f], s ∈ f → ∃ a ∈ s, cluster_pt a f] :=
begin
  tfae_have : 1 → 3,
  { intros H t ht,
    simp only [mem_nhds_within] at ht,
    choose u huo hxu hut using ht,
    rcases H.countable_open_subcover₂ _ huo (λ x hx, mem_Union₂.2 ⟨x, hx, hxu x hx⟩)
      with ⟨I, hIs, hIc, hsI⟩,
    replace hsI := subset_inter hsI subset.rfl, rw Union₂_inter at hsI,
    exact ⟨I, hIs, hIc, hsI.trans $ Union₂_mono $ λ x hx, hut x _⟩ },
  tfae_have : 3 → 2, from λ H t ht, H t (λ x hx, mem_nhds_within_of_mem_nhds (ht x hx)),
  tfae_have : 2 → 4,
    from λ H U hUo hU, H U (λ x hx, (hUo x).mem_nhds (hU x)),
  tfae_have : 4 → 6,
  { intros H T hT,
    simp only [(nhds_within_basis_open _ _).mem_iff] at hT,
    replace hT : ∀ x ∈ s, ∃ (u : {u : set X // x ∈ u ∧ is_open u}) (t ∈ T), ↑u ∩ s ⊆ t,
      by simpa only [subtype.exists', @exists_swap {t // t ∈ T}] using hT,
    haveI : ∀ x, nonempty {u : set X // x ∈ u ∧ is_open u} := λ x, ⟨⟨univ, trivial, is_open_univ⟩⟩,
    choose! u t htT ht using hT,
    rcases H (λ x, u x) (λ x, (u x).2.2) (λ x, (u x).2.1) with ⟨I, hIs, hIc, hsI⟩,
    refine ⟨t '' I, image_subset_iff.2 (λ x hx, htT _ $ hIs hx), hIc.image _, λ x hx, _⟩,
    rcases mem_Union₂.1 (hsI hx) with ⟨i, hi, hxi⟩,
    exact ⟨t i, mem_image_of_mem t hi, ht i (hIs hi) ⟨hxi, hx⟩⟩ },
  tfae_have : 6 → 5,
  { intros H T hT,
    exact H T (λ x hx, (hT x hx).imp $ λ t ht, ⟨ht.fst, mem_nhds_within_of_mem_nhds ht.snd⟩) },
  tfae_have : 5 → 1,
  { refine λ H U hUo hsU, H U (λ x hx, _),
    rcases hsU hx with ⟨t, ht, hxt⟩,
    exact ⟨t, ht, (hUo _ ht).mem_nhds hxt⟩ },
  tfae_have : 7 → 1, from is_lindelof_of_exists_cluster_pt,
  tfae_have : 2 → 7,
  { introsI H f hne hfI hsf,
    simp only [cluster_pt_iff, ← not_disjoint_iff_nonempty_inter],
    by_contra h, push_neg at h,
    choose! t ht V hV hd using h,
    rcases H t ht with ⟨I, hIs, hIc, hsI⟩,
    have : (⋃ x ∈ I, t x) ∩ (⋂ x ∈ I, V x) ∈ f,
      from inter_mem (mem_of_superset hsf hsI)
        ((countable_bInter_mem hIc).2 $ λ x hx, hV _ (hIs hx)),
    rcases filter.nonempty_of_mem this with ⟨x, hxt, hxV⟩,
    rw mem_Inter₂ at hxV, rw mem_Union₂ at hxt, rcases hxt with ⟨i, hi, hxi⟩,
    exact @hd i (hIs hi) x ⟨hxi, hxV _ hi⟩},
  tfae_finish
end

lemma is_lindelof_iff_countable_cover_nhds : is_lindelof s ↔
  ∀ {t : X → set X}, (∀ x ∈ s, t x ∈ 𝓝 x) → ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, t x :=
(is_lindelof_tfae s).out 0 1

alias is_lindelof_iff_countable_cover_nhds ↔ is_lindelof.countable_cover_nhds _

lemma is_lindelof_iff_countable_cover_nhds_within : is_lindelof s ↔
  ∀ {t : X → set X}, (∀ x ∈ s, t x ∈ 𝓝[s] x) → ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, t x :=
(is_lindelof_tfae s).out 0 2

alias is_lindelof_iff_countable_cover_nhds_within ↔ is_lindelof.countable_cover_nhds_within _

lemma is_lindelof_iff_countable_cover_open_nhds : is_lindelof s ↔
  ∀ {u : X → set X}, (∀ x, is_open (u x)) → (∀ x, x ∈ u x) →
    ∃ I ⊆ s, countable I ∧ s ⊆ ⋃ x ∈ I, u x :=
(is_lindelof_tfae s).out 0 3

alias is_lindelof_iff_countable_cover_open_nhds ↔ is_lindelof.countable_cover_open_nhds _

lemma is_lindelof_iff_countable_sUnion_nhds : is_lindelof s ↔
  ∀ {T : set (set X)}, (∀ x ∈ s, ∃ t ∈ T, t ∈ 𝓝 x) → ∃ I ⊆ T, countable I ∧ s ⊆ ⋃₀ I :=
(is_lindelof_tfae s).out 0 4

alias is_lindelof_iff_countable_sUnion_nhds ↔ is_lindelof.countable_sUnion_nhds _

lemma is_lindelof_iff_countable_sUnion_nhds_within : is_lindelof s ↔
  ∀ {T : set (set X)}, (∀ x ∈ s, ∃ t ∈ T, t ∈ 𝓝[s] x) → ∃ I ⊆ T, countable I ∧ s ⊆ ⋃₀ I :=
(is_lindelof_tfae s).out 0 5

alias is_lindelof_iff_countable_sUnion_nhds_within ↔ is_lindelof.countable_sUnion_nhds_within _

lemma is_lindelof_iff_exists_cluster_pt : is_lindelof s ↔
  ∀ (f : filter X) [ne_bot f] [countable_Inter_filter f], s ∈ f → ∃ a ∈ s, cluster_pt a f :=
(is_lindelof_tfae s).out 0 6

lemma is_lindelof.exists_cluster_pt {f : filter X} [ne_bot f] [countable_Inter_filter f]
  (hs : is_lindelof s) (hsf : s ∈ f) : ∃ a ∈ s, cluster_pt a f :=
is_lindelof_iff_exists_cluster_pt.mp hs f hsf

lemma is_lindelof_Union [encodable ι] {s : ι → set X} (h : ∀ i, is_lindelof (s i)) :
  is_lindelof (⋃ i, s i) :=
begin
  intros U hUo hsU,
  choose V hVU hVc hsV using λ i, (h i) hUo (Union_subset_iff.1 hsU i),
  refine ⟨⋃ i, V i, Union_subset hVU, countable_Union hVc, _⟩,
  simpa only [sUnion_Union] using Union_mono hsV
end

lemma is_lindelof_bUnion {I : set ι} (hI : countable I) {s : Π i ∈ I, set X}
  (hs : ∀ i ∈ I, is_lindelof (s i ‹i ∈ I›)) : is_lindelof (⋃ i ∈ I, s i ‹i ∈ I›) :=
begin
  haveI := hI.to_encodable,
  simp only [set_coe.forall', bUnion_eq_Union] at hs ⊢,
  exact is_lindelof_Union hs
end

protected lemma set.countable.is_lindelof (hs : countable s) : is_lindelof s :=
is_lindelof_iff_countable_cover_nhds.mpr $ λ t ht,
  ⟨s, subset.rfl, hs, λ x hx, mem_Union₂.2 ⟨x, hx, mem_of_mem_nhds (ht x hx)⟩⟩

protected lemma set.finite.is_lindelof (hs : finite s) : is_lindelof s :=
hs.countable.is_lindelof

protected lemma set.subsingleton.is_lindelof (hs : s.subsingleton) : is_lindelof s :=
hs.finite.is_lindelof

@[simp] lemma is_lindelof_empty : is_lindelof (∅ : set X) :=
countable_empty.is_lindelof

@[simp] lemma is_lindelof_singleton (x : X) : is_lindelof ({x} : set X) :=
(countable_singleton x).is_lindelof

lemma is_lindelof.inter_closed (hs : is_lindelof s) (ht : is_closed t) :
  is_lindelof (s ∩ t) :=
begin
  apply is_lindelof_of_exists_cluster_pt, introsI f h₁ h₂ hstf,
  rw inter_mem_iff at hstf,
  obtain ⟨a, hsa, ha⟩ : ∃ a ∈ s, cluster_pt a f, from hs.exists_cluster_pt hstf.1,
  have : a ∈ t :=
    (ht.mem_of_nhds_within_ne_bot $ ha.mono $ le_principal_iff.2 hstf.2),
  exact ⟨a, ⟨hsa, this⟩, ha⟩
end

lemma is_closed.inter_lindelof (hs : is_closed s) (ht : is_lindelof t) : is_lindelof (s ∩ t) :=
inter_comm t s ▸ ht.inter_closed hs

lemma is_lindelof.subset (hs : is_lindelof s) (hts : t ⊆ s) (ht : is_closed t) : is_lindelof t :=
by simpa only [inter_eq_self_of_subset_right hts] using hs.inter_closed ht

lemma is_lindelof.image_of_continuous_on (hs : is_lindelof s) {f : X → Y} (hf : continuous_on f s) :
  is_lindelof (f '' s) :=
begin
  refine is_lindelof_iff_countable_cover_nhds_within.mpr (λ t ht, _),
  have : ∀ x ∈ s, f ⁻¹' (t (f x)) ∈ 𝓝[s] x,
    from λ x hx, (hf x hx).tendsto_nhds_within_image (ht (f x) (mem_image_of_mem f hx)),
  rcases hs.countable_cover_nhds_within this with ⟨I, hIs, hIc, hI⟩,
  refine ⟨f '' I, image_subset _ hIs, hIc.image f, _⟩,
  simpa
end

lemma is_lindelof.image (hs : is_lindelof s) {f : X → Y} (hf : continuous f) :
  is_lindelof (f '' s) :=
hs.image_of_continuous_on hf.continuous_on

lemma inducing.is_lindelof_image {e : X → Y} (he : inducing e) :
  is_lindelof (e '' s) ↔ is_lindelof s :=
begin
  refine ⟨λ h, _, λ h, h.image he.continuous⟩,
  refine is_lindelof_iff_countable_cover_open_nhds.mpr (λ u huo hxu, _),
  replace huo := λ x, he.is_open_iff.1 (huo x), -- `simp only ... at huo` fails
  choose v hvo hv using huo, obtain rfl : (λ x, e ⁻¹' (v x)) = u := funext hv,
  have : e '' s ⊆ ⋃ x ∈ s, v x,
    from image_subset_iff.2 (λ x hx, mem_Union₂.2 ⟨x, hx, hxu x⟩),
  simpa using h.countable_open_subcover₂ _ (λ x _, hvo x) this
end

lemma embedding.is_lindelof_image {e : X → Y} (he : embedding e) :
  is_lindelof (e '' s) ↔ is_lindelof s :=
he.to_inducing.is_lindelof_image

class lindelof_space (X : Type*) [topological_space X] : Prop :=
(is_lindelof_univ : is_lindelof (univ : set X))

export lindelof_space (is_lindelof_univ)

lemma is_lindelof_univ_iff : is_lindelof (univ : set X) ↔ lindelof_space X := ⟨λ h, ⟨h⟩, λ h, h.1⟩

protected lemma is_closed.is_lindelof [lindelof_space X] {s : set X} (hs : is_closed s) :
  is_lindelof s :=
is_lindelof_univ.subset (subset_univ s) hs

lemma is_lindelof_iff_lindelof_space : is_lindelof s ↔ lindelof_space s :=
by rw [← is_lindelof_univ_iff, ← embedding_subtype_coe.is_lindelof_image, image_univ,
  subtype.range_coe]

alias is_lindelof_iff_lindelof_space ↔ is_lindelof.to_subtype _

@[protect_proj]
class strongly_lindelof_space (X : Type*) [topological_space X] : Prop :=
(is_lindelof : ∀ s : set X, is_lindelof s)

protected lemma set.is_lindelof [strongly_lindelof_space X] (s : set X) : is_lindelof s :=
strongly_lindelof_space.is_lindelof s

instance second_countable_topology.to_strongly_lindelof_space
  [second_countable_topology X] : strongly_lindelof_space X :=
begin
  refine ⟨λ s U hUo hU, _⟩,
  rcases is_open_sUnion_countable U hUo with ⟨S, hSc, hSU, hS⟩,
  exact ⟨S, hSU, hSc, hS.symm ▸ hU⟩
end
