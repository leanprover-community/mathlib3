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
  `paracompact_of_locally_compact_sigma_compact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x, `x : X`, see
  `refinement_of_locally_compact_sigma_compact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `emetric_space` is a paracompact space, see instance `emetric_space.paracompact_space` in
  `topology/metric_space/emetric_space`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

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
class paracompact_space (X : Type v) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ (α : Type v) (s : α → set X) (ho : ∀ a, is_open (s a)) (hc : (⋃ a, s a) = univ),
  ∃ (β : Type v) (t : β → set X) (ho : ∀ b, is_open (t b)) (hc : (⋃ b, t b) = univ),
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
  rwa [Union_coe_set, finset.set_bUnion_coe, ← univ_subset_iff],
end

/-- Let `X` be a locally compact sigma compact Hausdorff topological space, let `s` be a closed set
in `X`. Suppose that for each `x ∈ s` the sets `B x : ι x → set X` with the predicate
`p x : ι x → Prop` form a basis of the filter `𝓝 x`. Then there exists a locally finite covering
`λ i, B (c i) (r i)` of `s` such that all “centers” `c i` belong to `s` and each `r i` satisfies
`p (c i)`.

The notation is inspired by the case `B x r = metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `filter.has_basis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locally_compact_sigma_compact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a version of this lemma
dealing with a covering of the whole space.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis_set
  [locally_compact_space X] [sigma_compact_space X] [t2_space X]
  {ι : X → Type u} {p : Π x, ι x → Prop} {B : Π x, ι x → set X} {s : set X}
  (hs : is_closed s) (hB : ∀ x ∈ s, (𝓝 x).has_basis (p x) (B x)) :
  ∃ (α : Type v) (c : α → X) (r : Π a, ι (c a)), (∀ a, c a ∈ s ∧ p (c a) (r a)) ∧
    (s ⊆ ⋃ a, B (c a) (r a)) ∧ locally_finite (λ a, B (c a) (r a)) :=
begin
  classical,
  -- For technical reasons we prepend two empty sets to the sequence `compact_exhaustion.choice X`
  set K' : compact_exhaustion X := compact_exhaustion.choice X,
  set K : compact_exhaustion X := K'.shiftr.shiftr,
  set Kdiff := λ n, K (n + 1) \ interior (K n),
  -- Now we restate some properties of `compact_exhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1),
  { intro x,
    simpa only [K'.find_shiftr]
      using diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x) },
  have Kdiffc : ∀ n, is_compact (Kdiff n ∩ s),
    from λ n, ((K.is_compact _).diff is_open_interior).inter_right hs,
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : ∀ n (x : Kdiff (n + 1) ∩ s), (K n)ᶜ ∈ 𝓝 (x : X),
    from λ n x, is_open.mem_nhds (K.is_closed n).is_open_compl
      (λ hx', x.2.1.2 $ K.subset_interior_succ _ hx'),
  haveI : ∀ n (x : Kdiff n ∩ s), nonempty (ι x) := λ n x, (hB x x.2.2).nonempty,
  choose! r hrp hr using (λ n (x : Kdiff (n + 1) ∩ s), (hB x x.2.2).mem_iff.1 (this n x)),
  have hxr : ∀ n x (hx : x ∈ Kdiff (n + 1) ∩ s), B x (r n ⟨x, hx⟩) ∈ 𝓝 x,
    from λ n x hx, (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩),
  choose T hT using λ n, (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n),
  set T' : Π n, set ↥(Kdiff (n + 1) ∩ s) := λ n, T n,
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, λ a, a.2, λ a, r a.1 a.2, _, _, _⟩,
  { rintro ⟨n, x, hx⟩, exact ⟨x.2.2, hrp _ _⟩ },
  { refine (λ x hx, mem_Union.2 _),
    rcases mem_bUnion_iff.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩,
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩ },
  { intro x,
    refine ⟨interior (K (K'.find x + 3)),
      is_open.mem_nhds is_open_interior (K.subset_interior_succ _ (hKcov x).1), _⟩,
    have : (⋃ k ≤ K'.find x + 2, (range $ sigma.mk k) : set (Σ n, T' n)).finite,
      from (finite_le_nat _).bUnion (λ k hk, finite_range _),
    apply this.subset, rintro ⟨k, c, hc⟩,
    simp only [mem_Union, mem_set_of_eq, mem_image_eq, subtype.coe_mk],
    rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩,
    refine ⟨k, _, ⟨c, hc⟩, rfl⟩,
    have := (mem_compl_iff _ _).1 (hr k c hxB),
    contrapose! this with hnk,
    exact K.subset hnk (interior_subset hxK) },
end

/-- Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose that for each
`x` the sets `B x : ι x → set X` with the predicate `p x : ι x → Prop` form a basis of the filter
`𝓝 x`. Then there exists a locally finite covering `λ i, B (c i) (r i)` of `X` such that each `r i`
satisfies `p (c i)`

The notation is inspired by the case `B x r = metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `filter.has_basis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locally_compact_sigma_compact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set` for a version of this lemma
dealing with a covering of a closed set.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis
  [locally_compact_space X] [sigma_compact_space X] [t2_space X]
  {ι : X → Type u} {p : Π x, ι x → Prop} {B : Π x, ι x → set X}
  (hB : ∀ x, (𝓝 x).has_basis (p x) (B x)) :
  ∃ (α : Type v) (c : α → X) (r : Π a, ι (c a)), (∀ a, p (c a) (r a)) ∧
    (⋃ a, B (c a) (r a)) = univ ∧ locally_finite (λ a, B (c a) (r a)) :=
let ⟨α, c, r, hp, hU, hfin⟩ := refinement_of_locally_compact_sigma_compact_of_nhds_basis_set
  is_closed_univ (λ x _, hB x)
in ⟨α, c, r, λ a, (hp a).2, univ_subset_iff.1 hU, hfin⟩

/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a more precise statement. -/
@[priority 100] -- See note [lower instance priority]
instance paracompact_of_locally_compact_sigma_compact [locally_compact_space X]
  [sigma_compact_space X] [t2_space X] : paracompact_space X :=
begin
  refine ⟨λ α s ho hc, _⟩,
  choose i hi using Union_eq_univ_iff.1 hc,
  have : ∀ x : X, (𝓝 x).has_basis (λ t : set X, (x ∈ t ∧ is_open t) ∧ t ⊆ s (i x)) id,
    from λ x : X, (nhds_basis_opens x).restrict_subset (is_open.mem_nhds (ho (i x)) (hi x)),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis this
    with ⟨β, c, t, hto, htc, htf⟩,
  exact ⟨β, t, λ x, (hto x).1.2, htc, htf, λ b, ⟨i $ c b, (hto b).2⟩⟩
end

/- Dieudonné‘s theorem: a paracompact Hausdorff space is normal. Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
lemma normal_of_paracompact_t2 [t2_space X] [paracompact_space X] : normal_space X :=
begin
  /- First we show how to go from points to a set on one side. -/
  have : ∀ (s t : set X), is_closed s → is_closed t →
    (∀ x ∈ s, ∃ u v, is_open u ∧ is_open v ∧ x ∈ u ∧ t ⊆ v ∧ disjoint u v) →
    ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v,
  { /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
    open covering of `s`. We choose a locally finite refinement `u' : s → set X`, then `⋃ i, u' i`
    and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    intros s t hs ht H, choose u v hu hv hxu htv huv using set_coe.forall'.1 H,
    rcases precise_refinement_set hs u hu (λ x hx, mem_Union.2 ⟨⟨x, hx⟩, hxu _⟩)
      with ⟨u', hu'o, hcov', hu'fin, hsub⟩,
    refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, is_open_Union hu'o, is_closed_closure.is_open_compl,
      hcov', _, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩,
    rw [hu'fin.closure_Union, compl_Union, subset_Inter_iff],
    refine λ i x hxt hxu, absurd (htv i hxt) (closure_minimal _ (is_closed_compl_iff.2 $ hv _) hxu),
    exact λ y hyu hyv, huv i ⟨hsub _ hyu, hyv⟩ },
  /- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`. -/
  refine ⟨λ s t hs ht hst, this s t hs ht (λ x hx, _)⟩,
  rcases this t {x} ht is_closed_singleton (λ y hyt, _) with ⟨v, u, hv, hu, htv, hxu, huv⟩,
  { exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩ },
  { have : x ≠ y, by { rintro rfl, exact hst ⟨hx, hyt⟩ },
    rcases t2_separation this with ⟨v, u, hv, hu, hxv, hyu, hd⟩,
    exact ⟨u, v, hu, hv, hyu, singleton_subset_iff.2 hxv, disjoint.symm hd.le⟩ }
end
