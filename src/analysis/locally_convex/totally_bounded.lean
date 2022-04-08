/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.bounded
import topology.algebra.uniform_group
import analysis.locally_convex.balanced_core_hull
/-!
blablabla
-/
variables {𝕜 E ι : Type*}

open_locale topological_space pointwise filter

section absorbs
variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E] --[has_scalar 𝕜 E]


lemma absorbs_union_finset {s : set E} {t : finset ι} {f : ι → set E} :
  absorbs 𝕜 s (⋃ (i : ι) (hy : i ∈ t), f i) ↔ ∀ i ∈ t, absorbs 𝕜 s (f i) :=
begin
  classical,
  induction t using finset.induction_on with i t ht hi,
  { simp only [finset.not_mem_empty, set.Union_false, set.Union_empty, absorbs_empty,
    forall_false_left, implies_true_iff] },
  rw [finset.set_bUnion_insert, absorbs_union, hi],
  split; intro h,
  { refine λ i' hi', or.elim (finset.mem_insert.mp hi') _ (λ hi'', h.2 i' hi''),
    exact (λ hi'', by { rw hi'', exact h.1 }), },
  exact ⟨h i (finset.mem_insert_self i t), λ i' hi', h i' (finset.mem_insert_of_mem hi')⟩,
end

lemma absorbs_union_finite {s : set E} {t : set ι} {f : ι → set E} (hi : t.finite) :
  absorbs 𝕜 s (⋃ (i : ι) (hy : i ∈ t), f i) ↔ ∀ i ∈ t, absorbs 𝕜 s (f i) :=
begin
  lift t to finset ι using hi,
  simp only [finset.mem_coe],
  exact absorbs_union_finset,
end

lemma absorbs_add {s1 s2 t1 t2 : set E} (h1 : absorbs 𝕜 s1 t1) (h2 : absorbs 𝕜 s2 t2) :
  absorbs 𝕜 (s1 + s2) (t1 + t2) :=
begin
  rcases h1 with ⟨r1, hr1, h1⟩,
  rcases h2 with ⟨r2, hr2, h2⟩,
  refine ⟨max r1 r2, lt_max_of_lt_left hr1, λ a ha, _⟩,
  rw smul_add,
  exact set.add_subset_add (h1 a (le_of_max_le_left ha)) (h2 a (le_of_max_le_right ha)),
end

end absorbs

namespace bornology

section bornology

variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [uniform_space E] [uniform_add_group E] [has_continuous_smul 𝕜 E]
variables [regular_space E]

lemma absorbent.absorbs_finite {s : set E} (hs : absorbent 𝕜 s) {v : set E} (hv : v.finite) :
  absorbs 𝕜 s v :=
begin
  rw ←set.bUnion_of_singleton v,
  refine (absorbs_union_finite hv).mpr (λ i hi, absorbent.absorbs hs),
end


lemma totally_bounded.is_vonN_bounded {s : set E} (hs : totally_bounded s) : is_vonN_bounded 𝕜 s :=
begin
  rw totally_bounded_iff_subset_finite_Union_nhds_zero at hs,
  intros U hU,
  have h : filter.tendsto (λ (x : E × E), x.fst + x.snd) (𝓝 (0,0)) (𝓝 ((0 : E) + (0 : E))) :=
  continuous_iff_continuous_at.mp has_continuous_add.continuous_add (0,0),
  rw add_zero at h,
  have h' := filter.has_basis.prod (nhds_basis_closed_balanced 𝕜 E)
    (nhds_basis_closed_balanced 𝕜 E),
  simp_rw [←nhds_prod_eq, id.def] at h',
  rcases filter.tendsto.basis_left h h' U hU with ⟨x, hx, h''⟩,
  simp at h'',
  specialize hs x.snd hx.2.1,
  rcases hs with ⟨t, ht, hs⟩,
  have hx1 : absorbent 𝕜 x.fst := absorbent_nhds_zero hx.1.1,
  refine absorbs.mono_right _ hs,
  rw absorbs_union_finite ht,
  intros y hy,
  have hxfstsnd : x.fst + x.snd ⊆ U :=
  begin
    intros z hz,
    rw set.mem_add at hz,
    rcases hz with ⟨z1, z2, hz1, hz2, hz⟩,
    have hz' : (z1,z2) ∈ x.fst ×ˢ x.snd :=
    by { rw [set.prod_mk_mem_set_prod_eq], exact ⟨hz1, hz2⟩ },
    specialize h'' hz',
    simp only [hz] at h'',
    exact h'',
  end,
  refine absorbs.mono_left _ hxfstsnd,
  rw ←set.singleton_vadd,
  rw vadd_eq_add,
  refine absorbs_add (absorbent.absorbs hx1) _,
  exact hx.2.2.2.absorbs_self,
end

end bornology

end bornology
