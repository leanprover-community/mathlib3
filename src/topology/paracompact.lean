/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
import topology.subset_properties
import topology.separation

/-!
A formal roadmap for basic properties of paracompact spaces.

It contains the statements that compact spaces and metric spaces are paracompact,
and that paracompact t2 spaces are normal, as well as partially formalised proofs.

Any contributor should feel welcome to contribute complete proofs. When this happens,
we should also consider preserving the current file as an exemplar of a formal roadmap.
-/

open set filter
open_locale filter topological_space

/-- A topological space is called paracompact, if every open covering of this space admits
a locally finite refinement. -/
class paracompact_space (X : Type*) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ (S : set (set X)) (ho : ∀ s ∈ S, is_open s) (hc : ⋃₀ S = univ),
  ∃ (T : set (set X)) (ho : ∀ t ∈ T, is_open t) (hc : ⋃₀ T = univ),
    locally_finite (coe : T → set X) ∧ ∀ t ∈ T, ∃ s ∈ S, t ⊆ s)

variables {ι X : Type*} [topological_space X]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
 one indexed on the same type with each open set contained in the corresponding original one. -/
lemma paracompact_space.precise_refinement [paracompact_space X] (u : ι → set X)
  (uo : ∀ a, is_open (u a)) (uc : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, (∀ a, is_open (v a)) ∧ (⋃ i, v i) = univ ∧ locally_finite v ∧ (∀ a, v a ⊆ u a) :=
begin
  have := paracompact_space.locally_finite_refinement (range u) (forall_range_iff.2 uo) uc,
  simp_rw [exists_range_iff, exists_prop, sUnion_eq_univ_iff, set_coe.forall'] at this,
  choose T hTo hTX hTf f hf, choose t htT ht using hTX, choose U hxU hUf using hTf,
  refine ⟨λ i, ⋃ t ∈ f ⁻¹' {i}, ↑t, _, _, _, _⟩,
  { exact λ a, is_open_Union (λ t, is_open_Union $ λ ha, hTo t) },
  { simp only [eq_univ_iff_forall, mem_Union],
    exact λ x, ⟨f ⟨t x, htT x⟩, ⟨t x, htT x⟩, rfl, ht x⟩ },
  { refine λ x, ⟨U x, hxU x, ((hUf x).image f).subset _⟩,
    simp only [subset_def, mem_Union, mem_set_of_eq, set.nonempty, mem_inter_eq],
    rintro i ⟨y, ⟨t, rfl : f t = i, hyt⟩, hyU⟩,
    exact mem_image_of_mem _ ⟨y, hyt, hyU⟩ },
  { simp only [subset_def, mem_Union],
    rintro i x ⟨t, rfl : f t = i, hxt⟩,
    exact hf _ hxt }
end

instance paracompact_of_compact [compact_space X] : paracompact_space X :=
begin
  refine ⟨λ S hSo hSu, _⟩,
  rw sUnion_eq_bUnion at hSu,
  rcases compact_univ.elim_finite_subcover_image hSo hSu.ge with ⟨T, hTS, hTf, hTu⟩,
  rw ← sUnion_eq_bUnion at hTu,
  haveI := hTf.fintype,
  exact ⟨T, λ t ht, hSo t (hTS ht), univ_subset_iff.1 hTu, locally_finite_of_fintype _,
    λ t ht, ⟨t, hTS ht, subset.refl t⟩⟩
end

instance paracompact_of_locally_compact_sigma_compact [locally_compact_space X]
  [sigma_compact_space X] [t2_space X] : paracompact_space X :=
begin
  refine ⟨λ S hSo hSc, _⟩,
  set K := compact_covering X,
  have : ∀ n, ∃ T ⊆ S, finite T ∧ K (n + 2) \ interior (K (n + 1)) ⊆
    ⋃ t ∈ T, (t ∩ interior (K (n + 3)) \ K n),
  { intro n,
    apply (compact_diff (is_compact_compact_covering X (n + 2))
      is_open_interior).elim_finite_subcover_image,
    { exact λ s hs, is_open_diff (is_open_inter (hSo s hs) is_open_interior)
        (is_compact_compact_covering X n).is_closed },
    { simp_rw [← Union_diff, ← Union_inter, ← sUnion_eq_bUnion],
      rw [hSc, univ_inter], -- `simp_rw` fails to rewrite this
      exact diff_subset_diff (compact_covering_sub_ _ } }
end

lemma normal_of_paracompact_t2 {X : Type u} [topological_space X] [t2_space X]
  [paracompact_space X] : normal_space X :=
todo
/-
Similar to the proof of `generalized_tube_lemma`, but different enough not to merge them.
Lemma: if `s : set X` is closed and can be separated from any point by open sets,
then `s` can also be separated from any closed set by open sets. Apply twice.

See
* Bourbaki, General Topology, Chapter IX, §4.4
* https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal
-/

lemma paracompact_of_metric {X : Type u} [metric_space X] : paracompact_space X :=
todo
/-
See Mary Ellen Rudin, A new proof that metric spaces are paracompact.
https://www.ams.org/journals/proc/1969-020-02/S0002-9939-1969-0236876-3/S0002-9939-1969-0236876-3.pdf
-/
