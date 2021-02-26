/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
import topology.subset_properties
import topology.separation
import data.option.basic

/-!
# Paracompact topological spaces

In this file we define a `paracompact_space` and provide two instances: 

- a compact space is paracompact;
- a locally compact sigma compact Hausdorff space is paracompact.

We also prove that every paracompact Hausdorff space is normal. This statement is not an instance
to avoid loops in the instance graph.

## TODO

Define partition of unity

## Tags

compact space, paracompact space
-/

open set filter function
open_locale filter topological_space

universes u v

/-- A topological space is called paracompact, if every open covering of this space admits
a locally finite refinement. -/
class paracompact_space (X : Type u) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ (S : set (set X)) (ho : ∀ s ∈ S, is_open s) (hc : ⋃₀ S = univ),
  ∃ (α : Type u) (t : α → set X) (ho : ∀ a, is_open (t a)) (hc : (⋃ a, t a) = univ),
    locally_finite t ∧ ∀ a, ∃ s ∈ S, t a ⊆ s)

variables {ι X : Type*} [topological_space X]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
lemma paracompact_space.precise_refinement [paracompact_space X] (u : ι → set X)
  (uo : ∀ a, is_open (u a)) (uc : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, (∀ a, is_open (v a)) ∧ (⋃ i, v i) = univ ∧ locally_finite v ∧ (∀ a, v a ⊆ u a) :=
begin
  have := paracompact_space.locally_finite_refinement (range u) (forall_range_iff.2 uo) uc,
  simp_rw [exists_range_iff, exists_prop, Union_eq_univ_iff] at this,
  choose α t hto hXt htf ind hind, choose t_inv ht_inv using hXt, choose U hxU hU using htf,
  refine ⟨λ i, ⋃ (a : α) (ha : ind a = i), t a, _, _, _, _⟩,
  { exact λ a, is_open_Union (λ a, is_open_Union $ λ ha, hto a) },
  { simp only [eq_univ_iff_forall, mem_Union],
    exact λ x, ⟨ind (t_inv x), _, rfl, ht_inv _⟩ },
  { refine λ x, ⟨U x, hxU x, ((hU x).image ind).subset _⟩,
    simp only [subset_def, mem_Union, mem_set_of_eq, set.nonempty, mem_inter_eq],
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩,
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩ },
  { simp only [subset_def, mem_Union],
    rintro i x ⟨a, rfl, hxa⟩,
    exact hind _ hxa }
end

/-- A compact space is paracompact. -/
@[priority 100] -- See note [lower instance priority]
instance paracompact_of_compact [compact_space X] : paracompact_space X :=
begin
  refine ⟨λ S hSo hSu, _⟩,
  rw sUnion_eq_Union at hSu,
  rcases compact_univ.elim_finite_subcover _ (λ s : S, hSo s.1 s.2)  hSu.ge with ⟨T, hT⟩,
  simp only [subset_def, mem_Union, mem_univ, forall_prop_of_true] at hT, choose s hsT hs using hT,
  refine ⟨(T : set S), λ t, t.1.1, λ t, hSo _ t.1.2,
    univ_subset_iff.1 $ λ x hx, mem_Union.2 ⟨⟨s x, hsT x⟩, hs x⟩, locally_finite_of_fintype _,
    λ t, ⟨t.1.1, t.1.2, subset.refl _⟩⟩
end

/-- A locally compact sigma compact Hausdorff topological space is paracompact.
The formalization is based on
[these handouts](http://math.stanford.edu/~conrad/diffgeomPage/handouts/paracompact.pdf)
by Brian Conrad. -/
@[priority 100] -- See note [lower instance priority]
instance paracompact_of_locally_compact_sigma_compact [locally_compact_space X]
  [sigma_compact_space X] [t2_space X] : paracompact_space X :=
begin
  classical,
  refine ⟨λ S hSo hSc, _⟩,
  -- For technical reasons we prepend two empty sets to the sequence `compact_exhaustion X`
  set K' : compact_exhaustion X := compact_exhaustion.choice X,
  set K : compact_exhaustion X := K'.shiftr.shiftr,
  -- Now we restate properties of `compact_covering X` for `K`
  have hKcov : ∀ x, x ∈ K (K'.find x + 2) \ K (K'.find x + 1),
    by simpa only [K'.find_shiftr] using K'.shiftr.mem_diff_shiftr_find,
  -- Next we choose a finite covering `T n` of each `K (n + 2) \ interior (K (n + 1))`
  have : ∀ n, ∃ T ⊆ S, finite T ∧ K (n + 2) \ interior (K (n + 1)) ⊆ ⋃₀ T,
  { intro n,
    simp only [sUnion_eq_bUnion],
    apply (compact_diff (K'.is_compact n) is_open_interior).elim_finite_subcover_image,
    { exact λ s hs, hSo s hs },
    { rw [← sUnion_eq_bUnion, hSc],
      exact subset_univ _ } },
  choose T hTS hTf hTK, haveI := λ n, (hTf n).fintype,
  -- Finally, we take the set of all `t \ K n`, `t ∈ T n`
  refine ⟨Σ n, T n, λ a, a.2 \ K a.1, _, _, _, _⟩,
  { rintro ⟨n, t⟩,
    exact is_open_diff (hSo _ (hTS n t.2)) (K.is_closed _) },
  { refine Union_eq_univ_iff.2 (λ x, _),
    have hn := hKcov x,
    rcases hTK _ (diff_subset_diff_right interior_subset hn) with ⟨t, ht, hxt⟩,
    exact ⟨⟨_, t, ht⟩, hxt, λ hx, hn.2 (K.subset_succ _ hx)⟩ },
  { intro x,
    refine ⟨interior (K (K'.find x + 3)),
      mem_nhds_sets is_open_interior (K.subset_interior_succ _ (hKcov x).1), _⟩,
    have : (⋃ k ≤ K'.find x + 2, (range $ sigma.mk k) : set (Σ n, T n)).finite,
      from (finite_le_nat _).bUnion (λ k hk, finite_range _),
    apply this.subset, rintro ⟨k, t, ht⟩,
    simp only [mem_Union, mem_set_of_eq, mem_image_eq, subtype.coe_mk],
    rintro ⟨x, ⟨hxt, hxk⟩, hxn⟩,
    refine ⟨k, _, ⟨t, ht⟩, rfl⟩,
    contrapose! hxk with hnk,
    exact K.subset hnk (interior_subset hxn) },
  { rintro ⟨n, t, ht⟩,
    exact ⟨t, hTS n ht, diff_subset _ _⟩ }
end

/- A paracompact Hausdorff space is normal. Formalizatio is based on the proof at
[ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
lemma normal_of_paracompact_t2 [t2_space X] [paracompact_space X] : normal_space X :=
begin
  /- It suffices to lear how to go from points to a set o one side. Then we can apply
  this procedure to one set, the to the other set. -/
  suffices : ∀ (s t : set X), is_closed s → is_closed t →
    (∀ x ∈ s, ∃ u v, is_open u ∧ is_open v ∧ x ∈ u ∧ t ⊆ v ∧ disjoint u v) →
    ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v,
  { refine ⟨λ s t hs ht hst, _⟩,
    refine this s t hs ht (λ x hx, _),
    rcases this t {x} ht is_closed_singleton (λ y hyt, _) with ⟨v, u, hv, hu, htv, hxu, huv⟩,
    { exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩ },
    { have : x ≠ y, by { rintro rfl, exact hst ⟨hx, hyt⟩ },
      rcases t2_separation this with ⟨v, u, hv, hu, hxv, hyu, hd⟩,
      exact ⟨u, v, hu, hv, hyu, singleton_subset_iff.2 hxv, disjoint.symm hd.le⟩ } },
  /- Proof of the lemma -/
  intros s t hs ht H, choose u v hu hv hxu htv huv using set_coe.forall'.1 H,
  rcases paracompact_space.precise_refinement (λ o, option.elim o sᶜ u)
    (option.forall.2 ⟨is_open_compl_iff.2 hs, hu⟩) _
    with ⟨u', hu'o, hcov', hu'fin, hsub⟩,
  { suffices : ∀ y : t, ∃ v' : set X, is_open v' ∧ ↑y ∈ v' ∧ disjoint (⋃ x, u' (some x)) v',
    { choose v' hv'o hyv' hd,
      refine ⟨⋃ x, u' (some x), ⋃ y, v' y, is_open_Union (λ x, hu'o _), is_open_Union hv'o,
        λ x hx, mem_Union.2 _, λ y hy, mem_Union.2 _, _⟩,
      { rcases Union_eq_univ_iff.1 hcov' x with ⟨(_|x'), hx'⟩,
        { exact (hsub none hx' hx).elim },
        { exact ⟨x', hx'⟩ } },
      { exact ⟨⟨y, hy⟩, hyv' _⟩ },
    { simp only [disjoint_left, mem_Union, not_exists],
      rintro x ⟨x', hx'⟩ y hy,
      exact hd y ⟨mem_Union.2 ⟨x', hx'⟩, hy⟩ }  },
    { intro y,
      rcases hu'fin y with ⟨v', hyv', hv'⟩,
      simp only [finite_option, mem_set_of_eq] at hv',
      refine ⟨interior v' ∩ ⋂ (x : s) (hx : (u' (some x) ∩ v').nonempty), v x, _, _, _⟩,
      { exact is_open_inter is_open_interior (is_open_bInter hv' $ λ _ _, hv _) },
      { exact ⟨mem_interior_iff_mem_nhds.2 hyv', mem_bInter $ λ x hx, htv x y.2⟩ },
      { simp only [disjoint_left, mem_Union, mem_inter_eq, mem_Inter],
        rintro x ⟨x', hx'⟩ ⟨hxv', hxv⟩,
        exact huv x' ⟨hsub (some x') hx', hxv _ ⟨_, hx', interior_subset hxv'⟩⟩ } } },
  { refine Union_eq_univ_iff.2 (λ x, _),
    by_cases hx : x ∈ s,
    { exact ⟨some ⟨x, hx⟩, hxu _⟩ },
    { exact ⟨none, hx⟩ } }
end

