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

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locally_compact_sigma_compact`. Moreover, we can choose a locally finite refinement
  with sets in a given collection of filter bases of `𝓝 x, `x : X`, see
  `refinement_of_locally_compact_sigma_compact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `emetric_space` is a paracompact space, see instance `emetric_space.paracompact_space` in
  `topology/metric_space/emetric_space`.

## TODO

* Define partition of unity.

* Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/

open set filter function
open_locale filter topological_space

universes u v

/-- A topological space is called paracompact, if every open covering of this space admits a locally
finite refinement. We use the same universe for all types in the definition to avoid creating a
class like `paracompact_space.{u v}`. Due to lemma `precise_refinement` below, every open covering
`s : α → set X` indexed on `α : Type v` has a *precise* locally finite refinement, i.e., a locally
finite refinement `t : α → set X` indexed on the same type such that each `∀ i, t i ⊆ s i`. -/
class paracompact_space (X : Type u) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ (α : Type u) (s : α → set X) (ho : ∀ a, is_open (s a)) (hc : (⋃ a, s a) = univ),
  ∃ (β : Type u) (t : β → set X) (ho : ∀ b, is_open (t b)) (hc : (⋃ b, t b) = univ),
    locally_finite t ∧ ∀ b, ∃ a, t b ⊆ s a)

variables {ι : Type u} {X : Type v} [topological_space X]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
lemma precise_refinement [paracompact_space X] (u : ι → set X) (uo : ∀ a, is_open (u a))
  (uc : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, (∀ a, is_open (v a)) ∧ (⋃ i, v i) = univ ∧ locally_finite v ∧ (∀ a, v a ⊆ u a) :=
begin
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := paracompact_space.locally_finite_refinement (range u) coe
    (set_coe.forall.2 $ forall_range_iff.2 uo) (by rwa [← sUnion_range, subtype.range_coe]),
  simp only [set_coe.exists, subtype.coe_mk, exists_range_iff', Union_eq_univ_iff,
    exists_prop] at this,
  choose α t hto hXt htf ind hind, choose t_inv ht_inv using hXt, choose U hxU hU using htf,
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
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

/-- In a paracompact space, every open covering of a closed set admits a locally finite refinement
indexed by the same type. -/
lemma precise_refinement_set [paracompact_space X] {s : set X} (hs : is_closed s)
  (u : ι → set X) (uo : ∀ i, is_open (u i)) (us : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, (∀ i, is_open (v i)) ∧ (s ⊆ ⋃ i, v i) ∧ locally_finite v ∧ (∀ i, v i ⊆ u i) :=
begin
  rcases precise_refinement (λ i, option.elim i sᶜ u)
    (option.forall.2 ⟨is_open_compl_iff.2 hs, uo⟩) _ with ⟨v, vo, vc, vf, vu⟩,
  refine ⟨v ∘ some, λ i, vo _, _, vf.comp_injective (option.some_injective _), λ i, vu _⟩,
  { simp only [Union_option, ← compl_subset_iff_union] at vc,
    exact subset.trans (subset_compl_comm.1 $ vu option.none) vc },
  { simpa only [Union_option, option.elim, ← compl_subset_iff_union, compl_compl] }
end

/-- A compact space is paracompact. -/
@[priority 100] -- See note [lower instance priority]
instance paracompact_of_compact [compact_space X] : paracompact_space X :=
begin
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine ⟨λ ι s ho hu, _⟩,
  rcases compact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩,
  have := hT, simp only [subset_def, mem_Union] at this,
  choose i hiT hi using λ x, this x (mem_univ x),
  refine ⟨(T : set ι), λ t, s t, λ t, ho _, _, locally_finite_of_fintype _, λ t, ⟨t, subset.rfl⟩⟩,
  rwa [Union_subtype, finset.set_bUnion_coe, ← univ_subset_iff],
end

/-- Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose that for each
`x : X` we are given

* `s x : set X`, a neighborhood of `x`;
* `(p x : ι x → Prop, B x : ι x → set X)`, a basis of the filter `𝓝 x`.

Then there exists a locally finite covering `λ i, B (c i) (r i)` such that
`B (c i) (r i) ⊆ s (c i)`.

The notation is inspired by the case `B x r = metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. In the latter case this lemma implies that `X` is a paracompact space.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

In the most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis
  [locally_compact_space X] [sigma_compact_space X] [t2_space X]
  {ι : X → Type u} {p : Π x, ι x → Prop} {B : Π x, ι x → set X}
  (hB : ∀ x, (𝓝 x).has_basis (p x) (B x)) (s : X → set X) (hs : ∀ x, s x ∈ 𝓝 x) :
  ∃ (α : Type v) (c : α → X) (r : Π a, ι (c a)), (∀ a, p (c a) (r a)) ∧
    (⋃ a, B (c a) (r a)) = univ ∧ locally_finite (λ a, B (c a) (r a)) ∧
    ∀ a, B (c a) (r a) ⊆ s (c a) :=
begin
  classical,
  haveI : ∀ x, nonempty (ι x) := λ x, (hB x).nonempty,
  -- For technical reasons we prepend two empty sets to the sequence `compact_exhaustion.choice X`
  set K' : compact_exhaustion X := compact_exhaustion.choice X,
  set K : compact_exhaustion X := K'.shiftr.shiftr,
  set Kdiff := λ n, K (n + 1) \ interior (K n),
  -- Now we restate some properties of `compact_exhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1),
  { intro x,
    simpa only [K'.find_shiftr]
      using diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x) },
  have Kdiffc : ∀ n, is_compact (Kdiff n), from λ n, compact_diff (K.is_compact _) is_open_interior,
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) = K (n + 2) \ interior (K (n + 1))` such that
  -- `B (c n i) (r n i) ⊆ interior (K (n + 3)) \ K n`
  have : ∀ n (x ∈ Kdiff (n + 1)), (K n)ᶜ ∈ 𝓝 x,
    from λ n x hx, mem_nhds_sets (K.is_closed n) (λ hx', hx.2 $ K.subset_interior_succ _ hx'),
  choose! r hrp hr using (λ n x hx, (hB x).mem_iff.1 (inter_mem_sets (hs x) (this n x hx))),
  have hxr : ∀ n (x ∈ Kdiff (n + 1)), B x (r n x) ∈ 𝓝 x,
    from λ n x hx, (hB x).mem_of_mem (hrp _ _ hx),
  choose T hTK hT using λ n, (Kdiffc (n + 1)).elim_nhds_subcover _ (hxr n),
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, ↥(T n : set X), λ a, a.2, λ a, r a.1 a.2, _, _, _, _⟩,
  { rintro ⟨n, x, hx⟩, exact hrp _ _ (hTK _ _ hx) },
  { refine Union_eq_univ_iff.2 (λ x, _),
    obtain ⟨c, hcT, hcx⟩ : ∃ c ∈ T (K'.find x), x ∈ B c (r (K'.find x) c) :=
      mem_bUnion_iff.1 (hT _ (hKcov x)),
    exact ⟨⟨_,  c, hcT⟩, hcx⟩ },
  { intro x,
    refine ⟨interior (K (K'.find x + 3)),
      mem_nhds_sets is_open_interior (K.subset_interior_succ _ (hKcov x).1), _⟩,
    have : (⋃ k ≤ K'.find x + 2, (range $ sigma.mk k) : set (Σ n, ↥(T n : set X))).finite,
      from (finite_le_nat _).bUnion (λ k hk, finite_range _),
    apply this.subset, rintro ⟨k, c, hc⟩,
    simp only [mem_Union, mem_set_of_eq, mem_image_eq, subtype.coe_mk],
    rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩,
    refine ⟨k, _, ⟨c, hc⟩, rfl⟩,
    have := (mem_compl_iff _ _).1 (hr k c (hTK _ _ hc) hxB).2,
    contrapose! this with hnk,
    exact K.subset hnk (interior_subset hxK) },
  { rintro ⟨n, x, hx⟩,
    exact subset.trans (hr n x $ hTK _ _ hx) (inter_subset_left _ _) }
end

/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a more precise statement. -/
@[priority 100] -- See note [lower instance priority]
instance paracompact_of_locally_compact_sigma_compact [locally_compact_space X]
  [sigma_compact_space X] [t2_space X] : paracompact_space X :=
begin
  refine ⟨λ α s ho hc, _⟩,
  choose i hi using Union_eq_univ_iff.1 hc,
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis nhds_basis_opens
    (s ∘ i) (λ x, mem_nhds_sets (ho _ ) (hi _)) with ⟨β, c, t, hto, htc, htf, hsub⟩,
  exact ⟨β, t, λ x, (hto x).2, htc, htf, λ b, ⟨i $ c b, hsub _⟩⟩
end

/- Dieudonné‘s theorem: a paracompact Hausdorff space is normal. Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
lemma normal_of_paracompact_t2 [t2_space X] [paracompact_space X] : normal_space X :=
begin
  /- It suffices to learn how to go from points to a set on one side. Then we can apply
  this procedure to one set, then to the other set. -/
  suffices : ∀ (s t : set X), is_closed s → is_closed t →
    (∀ x ∈ s, ∃ u v, is_open u ∧ is_open v ∧ x ∈ u ∧ t ⊆ v ∧ disjoint u v) →
    ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v,
  { refine ⟨λ s t hs ht hst, this s t hs ht (λ x hx, _)⟩,
    rcases this t {x} ht is_closed_singleton (λ y hyt, _) with ⟨v, u, hv, hu, htv, hxu, huv⟩,
    { exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩ },
    { have : x ≠ y, by { rintro rfl, exact hst ⟨hx, hyt⟩ },
      rcases t2_separation this with ⟨v, u, hv, hu, hxv, hyu, hd⟩,
      exact ⟨u, v, hu, hv, hyu, singleton_subset_iff.2 hxv, disjoint.symm hd.le⟩ } },
  /- Proof of the lemma: for each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`.
  The sets `u x` form an open covering of `s`. We choose a locally finite refinement
  `u' : s → set X`, then `⋃ i, u' i` and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods
  of `s` and `t`.  -/
  intros s t hs ht H, choose u v hu hv hxu htv huv using set_coe.forall'.1 H,
  rcases precise_refinement_set hs u hu (λ x hx, mem_Union.2 ⟨⟨x, hx⟩, hxu _⟩)
    with ⟨u', hu'o, hcov', hu'fin, hsub⟩,
  refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, is_open_Union hu'o, is_closed_closure, hcov',
    _, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩,
  rw [hu'fin.closure_Union, compl_Union, subset_Inter_iff],
  refine λ i x hxt hxu, absurd (htv i hxt) (closure_minimal _ (is_closed_compl_iff.2 $ hv _) hxu),
  exact λ y hyu hyv, huv i ⟨hsub _ hyu, hyv⟩,
end
