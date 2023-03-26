/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import data.set.bool_indicator
import order.succ_pred.relation
import topology.subset_properties
import tactic.congrm

/-!
# Connected subsets of topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `is_connected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connected_component` is the connected component of an element in the space.
* `is_totally_disconnected`: all of its connected components are singletons.
* `is_totally_separated`: any two points can be separated by two disjoint opens that cover the set.

For each of these definitions, we also have a class stating that the whole space
satisfies that property:
`connected_space`, `totally_disconnected_space`, `totally_separated_space`.

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

open set function topological_space relation
open_locale classical topology

universes u v
variables {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*} [topological_space α]
  {s t u v : set α}

section preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
def is_preconnected (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v → s ⊆ u ∪ v →
  (s ∩ u).nonempty → (s ∩ v).nonempty → (s ∩ (u ∩ v)).nonempty

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def is_connected (s : set α) : Prop :=
s.nonempty ∧ is_preconnected s

lemma is_connected.nonempty {s : set α} (h : is_connected s) :
  s.nonempty := h.1

lemma is_connected.is_preconnected {s : set α} (h : is_connected s) :
  is_preconnected s := h.2

theorem is_preirreducible.is_preconnected {s : set α} (H : is_preirreducible s) :
  is_preconnected s :=
λ _ _ hu hv _, H _ _ hu hv

theorem is_irreducible.is_connected {s : set α} (H : is_irreducible s) : is_connected s :=
⟨H.nonempty, H.is_preirreducible.is_preconnected⟩

theorem is_preconnected_empty : is_preconnected (∅ : set α) :=
is_preirreducible_empty.is_preconnected

theorem is_connected_singleton {x} : is_connected ({x} : set α) :=
is_irreducible_singleton.is_connected

theorem is_preconnected_singleton {x} : is_preconnected ({x} : set α) :=
is_connected_singleton.is_preconnected

theorem set.subsingleton.is_preconnected {s : set α} (hs : s.subsingleton) :
  is_preconnected s :=
hs.induction_on is_preconnected_empty (λ x, is_preconnected_singleton)

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall {s : set α} (x : α)
  (H : ∀ y ∈ s, ∃ t ⊆ s, x ∈ t ∧ y ∈ t ∧ is_preconnected t) :
  is_preconnected s :=
begin
  rintros u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩,
  have xs : x ∈ s, by { rcases H y ys with ⟨t, ts, xt, yt, ht⟩, exact ts xt },
  wlog xu : x ∈ u,
  { rw inter_comm u v, rw union_comm at hs,
    exact this x H v u hv hu hs y ys yv z zs zu xs ((hs xs).resolve_right xu), },
  rcases H y ys with ⟨t, ts, xt, yt, ht⟩,
  have := ht u v hu hv(subset.trans ts hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩,
  exact this.imp (λ z hz, ⟨ts hz.1, hz.2⟩)
end

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall_pair {s : set α}
  (H : ∀ x y ∈ s, ∃ t ⊆ s, x ∈ t ∧ y ∈ t ∧ is_preconnected t) :
  is_preconnected s :=
begin
  rcases eq_empty_or_nonempty s with (rfl|⟨x, hx⟩),
  exacts [is_preconnected_empty, is_preconnected_of_forall x $ λ y, H x hx y],
end

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem is_preconnected_sUnion (x : α) (c : set (set α)) (H1 : ∀ s ∈ c, x ∈ s)
  (H2 : ∀ s ∈ c, is_preconnected s) : is_preconnected (⋃₀ c) :=
begin
  apply is_preconnected_of_forall x,
  rintros y ⟨s, sc, ys⟩,
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩
end

theorem is_preconnected_Union {ι : Sort*} {s : ι → set α} (h₁ : (⋂ i, s i).nonempty)
  (h₂ : ∀ i, is_preconnected (s i)) :
  is_preconnected (⋃ i, s i) :=
exists.elim h₁ $ λ f hf, is_preconnected_sUnion f _ hf (forall_range_iff.2 h₂)

theorem is_preconnected.union (x : α) {s t : set α} (H1 : x ∈ s) (H2 : x ∈ t)
  (H3 : is_preconnected s) (H4 : is_preconnected t) : is_preconnected (s ∪ t) :=
sUnion_pair s t ▸ is_preconnected_sUnion x {s, t}
  (by rintro r (rfl | rfl | h); assumption)
  (by rintro r (rfl | rfl | h); assumption)

theorem is_preconnected.union' {s t : set α} (H : (s ∩ t).nonempty)
  (hs : is_preconnected s) (ht : is_preconnected t) : is_preconnected (s ∪ t) :=
by { rcases H with ⟨x, hxs, hxt⟩, exact hs.union x hxs hxt ht }

theorem is_connected.union {s t : set α} (H : (s ∩ t).nonempty)
  (Hs : is_connected s) (Ht : is_connected t) : is_connected (s ∪ t) :=
begin
  rcases H with ⟨x, hx⟩,
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, _⟩,
  exact is_preconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Hs.is_preconnected Ht.is_preconnected
end

/-- The directed sUnion of a set S of preconnected subsets is preconnected. -/
theorem is_preconnected.sUnion_directed {S : set (set α)}
  (K : directed_on (⊆) S)
  (H : ∀ s ∈ S, is_preconnected s) : is_preconnected (⋃₀ S) :=
begin
  rintros u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩,
  obtain ⟨r, hrS, hsr, htr⟩ : ∃ r ∈ S, s ⊆ r ∧ t ⊆ r := K s hsS t htS,
  have Hnuv : (r ∩ (u ∩ v)).nonempty,
  from H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv)
    ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩,
  have Kruv : r ∩ (u ∩ v) ⊆ ⋃₀ S ∩ (u ∩ v),
  from inter_subset_inter_left _ (subset_sUnion_of_mem hrS),
  exact Hnuv.mono Kruv
end

/-- The bUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem is_preconnected.bUnion_of_refl_trans_gen {ι : Type*} {t : set ι} {s : ι → set α}
  (H : ∀ i ∈ t, is_preconnected (s i))
  (K : ∀ i j ∈ t, refl_trans_gen (λ i j : ι, (s i ∩ s j).nonempty ∧ i ∈ t) i j) :
  is_preconnected (⋃ n ∈ t, s n) :=
begin
  let R := λ i j : ι, (s i ∩ s j).nonempty ∧ i ∈ t,
  have P : ∀ (i j ∈ t), refl_trans_gen R i j →
    ∃ (p ⊆ t), i ∈ p ∧ j ∈ p ∧ is_preconnected (⋃ j ∈ p, s j),
  { intros i hi j hj h,
    induction h,
    case refl
    { refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, _⟩,
      rw [bUnion_singleton],
      exact H i hi },
    case tail : j k hij hjk ih
    { obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2,
      refine ⟨insert k p, insert_subset.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip, mem_insert k p, _⟩,
      rw [bUnion_insert],
      refine (H k hj).union' _ hp,
      refine hjk.1.mono _,
      rw [inter_comm],
      refine inter_subset_inter subset.rfl (subset_bUnion_of_mem hjp) } },
  refine is_preconnected_of_forall_pair _,
  intros x hx y hy,
  obtain ⟨i: ι, hi : i ∈ t, hxi : x ∈ s i⟩ := mem_Union₂.1 hx,
  obtain ⟨j: ι, hj : j ∈ t, hyj : y ∈ s j⟩ := mem_Union₂.1 hy,
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj),
  exact ⟨⋃ j ∈ p, s j, bUnion_subset_bUnion_left hpt, mem_bUnion hip hxi, mem_bUnion hjp hyj, hp⟩
end

/-- The bUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem is_connected.bUnion_of_refl_trans_gen {ι : Type*} {t : set ι} {s : ι → set α}
  (ht : t.nonempty)
  (H : ∀ i ∈ t, is_connected (s i))
  (K : ∀ i j ∈ t, refl_trans_gen (λ i j : ι, (s i ∩ s j).nonempty ∧ i ∈ t) i j) :
  is_connected (⋃ n ∈ t, s n) :=
⟨nonempty_bUnion.2 $ ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
  is_preconnected.bUnion_of_refl_trans_gen (λ i hi, (H i hi).is_preconnected) K⟩

/-- Preconnectedness of the Union of a family of preconnected sets
indexed by the vertices of a preconnected graph,
where two vertices are joined when the corresponding sets intersect. -/
theorem is_preconnected.Union_of_refl_trans_gen {ι : Type*} {s : ι → set α}
  (H : ∀ i, is_preconnected (s i))
  (K : ∀ i j, refl_trans_gen (λ i j : ι, (s i ∩ s j).nonempty) i j) :
  is_preconnected (⋃ n, s n) :=
by { rw [← bUnion_univ], exact is_preconnected.bUnion_of_refl_trans_gen (λ i _, H i)
  (λ i _ j _, by simpa [mem_univ] using K i j) }

theorem is_connected.Union_of_refl_trans_gen {ι : Type*} [nonempty ι] {s : ι → set α}
  (H : ∀ i, is_connected (s i))
  (K : ∀ i j, refl_trans_gen (λ i j : ι, (s i ∩ s j).nonempty) i j) :
  is_connected (⋃ n, s n) :=
⟨nonempty_Union.2 $ nonempty.elim ‹_› $ λ i : ι, ⟨i, (H _).nonempty⟩,
  is_preconnected.Union_of_refl_trans_gen (λ i, (H i).is_preconnected) K⟩

section succ_order
open order

variables [linear_order β] [succ_order β] [is_succ_archimedean β]

/-- The Union of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is preconnected. -/
theorem is_preconnected.Union_of_chain {s : β → set α}
  (H : ∀ n, is_preconnected (s n))
  (K : ∀ n, (s n ∩ s (succ n)).nonempty) :
  is_preconnected (⋃ n, s n) :=
is_preconnected.Union_of_refl_trans_gen H $
  λ i j, refl_trans_gen_of_succ _ (λ i _, K i) $ λ i _, by { rw inter_comm, exact K i }

/-- The Union of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is connected. -/
theorem is_connected.Union_of_chain [nonempty β] {s : β → set α}
  (H : ∀ n, is_connected (s n))
  (K : ∀ n, (s n ∩ s (succ n)).nonempty) :
  is_connected (⋃ n, s n) :=
is_connected.Union_of_refl_trans_gen H $
  λ i j, refl_trans_gen_of_succ _ (λ i _, K i) $ λ i _, by { rw inter_comm, exact K i }

/-- The Union of preconnected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem is_preconnected.bUnion_of_chain
  {s : β → set α} {t : set β} (ht : ord_connected t)
  (H : ∀ n ∈ t, is_preconnected (s n))
  (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).nonempty) :
  is_preconnected (⋃ n ∈ t, s n) :=
begin
  have h1 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → k ∈ t :=
    λ i j k hi hj hk, ht.out hi hj (Ico_subset_Icc_self hk),
  have h2 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → succ k ∈ t := λ i j k hi hj hk,
    ht.out hi hj ⟨hk.1.trans $ le_succ k, succ_le_of_lt hk.2⟩,
  have h3 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → (s k ∩ s (succ k)).nonempty :=
    λ i j k hi hj hk, K _ (h1 hi hj hk) (h2 hi hj hk),
  refine is_preconnected.bUnion_of_refl_trans_gen H (λ i hi j hj, _),
  exact refl_trans_gen_of_succ _ (λ k hk, ⟨h3 hi hj hk, h1 hi hj hk⟩)
    (λ k hk, ⟨by { rw [inter_comm], exact h3 hj hi hk }, h2 hj hi hk⟩),
end

/-- The Union of connected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem is_connected.bUnion_of_chain
  {s : β → set α} {t : set β} (hnt : t.nonempty) (ht : ord_connected t)
  (H : ∀ n ∈ t, is_connected (s n))
  (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).nonempty) :
  is_connected (⋃ n ∈ t, s n) :=
⟨nonempty_bUnion.2 $ ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
  is_preconnected.bUnion_of_chain ht (λ i hi, (H i hi).is_preconnected) K⟩

end succ_order

/-- Theorem of bark and tree :
if a set is within a (pre)connected set and its closure,
then it is (pre)connected as well. -/
theorem is_preconnected.subset_closure {s : set α} {t : set α}
  (H : is_preconnected s) (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) :
  is_preconnected t :=
λ u v hu hv htuv ⟨y, hyt, hyu⟩ ⟨z, hzt, hzv⟩,
let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu,
    ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv,
    ⟨r, hrs, hruv⟩ := H u v hu hv (subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
  ⟨r, Kst hrs, hruv⟩

theorem is_connected.subset_closure {s : set α} {t : set α}
  (H : is_connected s) (Kst : s ⊆ t) (Ktcs : t ⊆ closure s): is_connected t :=
let hsne := H.left,
    ht := Kst,
    htne := nonempty.mono ht hsne in
    ⟨nonempty.mono Kst H.left, is_preconnected.subset_closure H.right Kst Ktcs ⟩

/-- The closure of a (pre)connected set is (pre)connected as well. -/
theorem is_preconnected.closure {s : set α} (H : is_preconnected s) :
  is_preconnected (closure s) :=
is_preconnected.subset_closure H subset_closure $ subset.refl $ closure s

theorem is_connected.closure {s : set α} (H : is_connected s) :
  is_connected (closure s) :=
is_connected.subset_closure H subset_closure $ subset.refl $ closure s

/-- The image of a (pre)connected set is (pre)connected as well. -/
theorem is_preconnected.image [topological_space β] {s : set α} (H : is_preconnected s)
  (f : α → β) (hf : continuous_on f s) : is_preconnected (f '' s) :=
begin
  -- Unfold/destruct definitions in hypotheses
  rintros u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩,
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩,
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩,
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s ⊆ u' ∪ v',
  { rw [image_subset_iff, preimage_union] at huv,
    replace huv := subset_inter huv (subset.refl _),
    rw [inter_distrib_right, u'_eq, v'_eq, ← inter_distrib_right] at huv,
    exact (subset_inter_iff.1 huv).1 },
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹is_preconnected s›`
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).nonempty,
  { refine H u' v' hu' hv' huv ⟨x, _⟩ ⟨y, _⟩; rw inter_comm,
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩] },
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc,
    inter_comm s, inter_comm s, ← u'_eq, ← v'_eq] at hz,
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩
end

theorem is_connected.image [topological_space β] {s : set α} (H : is_connected s)
  (f : α → β) (hf : continuous_on f s) : is_connected (f '' s) :=
⟨nonempty_image_iff.mpr H.nonempty, H.is_preconnected.image f hf⟩

theorem is_preconnected_closed_iff {s : set α} :
  is_preconnected s ↔ ∀ t t', is_closed t → is_closed t' → s ⊆ t ∪ t' →
    (s ∩ t).nonempty → (s ∩ t').nonempty → (s ∩ (t ∩ t')).nonempty :=
⟨begin
  rintros h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩,
  rw [←not_disjoint_iff_nonempty_inter, ←subset_compl_iff_disjoint_right, compl_inter],
  intros h',
  have xt' : x ∉ t', from (h' xs).resolve_left (absurd xt),
  have yt : y ∉ t, from (h' ys).resolve_right (absurd yt'),
  have := h _ _ ht.is_open_compl ht'.is_open_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩,
  rw ←compl_union at this,
  exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
end,
begin
  rintros h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩,
  rw [←not_disjoint_iff_nonempty_inter, ←subset_compl_iff_disjoint_right, compl_inter],
  intros h',
  have xv : x ∉ v, from (h' xs).elim (absurd xu) id,
  have yu : y ∉ u, from (h' ys).elim id (absurd yv),
  have := h _ _ hu.is_closed_compl hv.is_closed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩,
  rw ←compl_union at this,
  exact this.ne_empty huv.disjoint_compl_right.inter_eq,
end⟩

lemma inducing.is_preconnected_image [topological_space β] {s : set α} {f : α → β}
  (hf : inducing f) : is_preconnected (f '' s) ↔ is_preconnected s :=
begin
  refine ⟨λ h, _, λ h, h.image _ hf.continuous.continuous_on⟩,
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩,
  rcases hf.is_open_iff.1 hu' with ⟨u, hu, rfl⟩,
  rcases hf.is_open_iff.1 hv' with ⟨v, hv, rfl⟩,
  replace huv : f '' s ⊆ u ∪ v, by rwa image_subset_iff,
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩
    with ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩,
  exact ⟨z, hzs, hzuv⟩
end

/- TODO: The following lemmas about connection of preimages hold more generally for strict maps
(the quotient and subspace topologies of the image agree) whose fibers are preconnected. -/

lemma is_preconnected.preimage_of_open_map [topological_space β] {s : set β}
  (hs : is_preconnected s) {f : α → β} (hinj : function.injective f) (hf : is_open_map f)
  (hsf : s ⊆ range f) :
  is_preconnected (f ⁻¹' s) :=
λ u v hu hv hsuv hsu hsv,
begin
  obtain ⟨b, hbs, hbu, hbv⟩ := hs (f '' u) (f '' v) (hf u hu) (hf v hv) _ _ _,
  obtain ⟨a, rfl⟩ := hsf hbs,
  rw hinj.mem_set_image at hbu hbv,
  exact ⟨a, hbs, hbu, hbv⟩,
  { have := image_subset f hsuv,
    rwa [set.image_preimage_eq_of_subset hsf, image_union] at this },
  { obtain ⟨x, hx1, hx2⟩ := hsu,
    exact ⟨f x, hx1, x, hx2, rfl⟩ },
  { obtain ⟨y, hy1, hy2⟩ := hsv,
    exact ⟨f y, hy1, y, hy2, rfl⟩ }
end

lemma is_preconnected.preimage_of_closed_map [topological_space β] {s : set β}
  (hs : is_preconnected s) {f : α → β} (hinj : function.injective f) (hf : is_closed_map f)
  (hsf : s ⊆ range f) :
  is_preconnected (f ⁻¹' s) :=
is_preconnected_closed_iff.2 $ λ u v hu hv hsuv hsu hsv,
begin
  obtain ⟨b, hbs, hbu, hbv⟩ :=
    is_preconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) _ _ _,
  obtain ⟨a, rfl⟩ := hsf hbs,
  rw hinj.mem_set_image at hbu hbv,
  exact ⟨a, hbs, hbu, hbv⟩,
  { have := image_subset f hsuv,
    rwa [set.image_preimage_eq_of_subset hsf, image_union] at this },
  { obtain ⟨x, hx1, hx2⟩ := hsu,
    exact ⟨f x, hx1, x, hx2, rfl⟩ },
  { obtain ⟨y, hy1, hy2⟩ := hsv,
    exact ⟨f y, hy1, y, hy2, rfl⟩ }
end

lemma is_connected.preimage_of_open_map [topological_space β] {s : set β} (hs : is_connected s)
  {f : α → β} (hinj : function.injective f) (hf : is_open_map f) (hsf : s ⊆ range f) :
  is_connected (f ⁻¹' s) :=
⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_open_map hinj hf hsf⟩

lemma is_connected.preimage_of_closed_map [topological_space β] {s : set β} (hs : is_connected s)
  {f : α → β} (hinj : function.injective f) (hf : is_closed_map f) (hsf : s ⊆ range f) :
  is_connected (f ⁻¹' s) :=
⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_closed_map hinj hf hsf⟩

lemma is_preconnected.subset_or_subset (hu : is_open u) (hv : is_open v) (huv : disjoint u v)
  (hsuv : s ⊆ u ∪ v) (hs : is_preconnected s) :
  s ⊆ u ∨ s ⊆ v :=
begin
  specialize hs u v hu hv hsuv,
  obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty,
  { exact or.inr ((set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv) },
  { replace hs := mt (hs hsu),
    simp_rw [set.not_nonempty_iff_eq_empty, ←set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs,
    exact or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv) }
end

lemma is_preconnected.subset_left_of_subset_union (hu : is_open u) (hv : is_open v)
  (huv : disjoint u v) (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).nonempty) (hs : is_preconnected s) :
  s ⊆ u :=
disjoint.subset_left_of_subset_union hsuv
begin
  by_contra hsv,
  rw not_disjoint_iff_nonempty_inter at hsv,
  obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv,
  exact set.disjoint_iff.1 huv hx,
end

lemma is_preconnected.subset_right_of_subset_union (hu : is_open u) (hv : is_open v)
  (huv : disjoint u v) (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).nonempty) (hs : is_preconnected s) :
  s ⊆ v :=
hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

/-- If a preconnected set `s` intersects an open set `u`, and limit points of `u` inside `s` are
contained in `u`, then the whole set `s` is contained in `u`. -/
lemma is_preconnected.subset_of_closure_inter_subset (hs : is_preconnected s)
  (hu : is_open u) (h'u : (s ∩ u).nonempty) (h : closure u ∩ s ⊆ u) : s ⊆ u :=
begin
  have A : s ⊆ u ∪ (closure u)ᶜ,
  { assume x hx,
    by_cases xu : x ∈ u,
    { exact or.inl xu },
    { right,
      assume h'x,
      exact xu (h (mem_inter h'x hx)) } },
  apply hs.subset_left_of_subset_union hu is_closed_closure.is_open_compl _ A h'u,
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure),
end

theorem is_preconnected.prod [topological_space β] {s : set α} {t : set β}
  (hs : is_preconnected s) (ht : is_preconnected t) :
  is_preconnected (s ×ˢ t) :=
begin
  apply is_preconnected_of_forall_pair,
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩,
  refine ⟨prod.mk a₁ '' t ∪ flip prod.mk b₂ '' s, _,
    or.inl ⟨b₁, hb₁, rfl⟩, or.inr ⟨a₂, ha₂, rfl⟩, _⟩,
  { rintro _ (⟨y, hy, rfl⟩|⟨x, hx, rfl⟩),
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩] },
  { exact (ht.image _ (continuous.prod.mk _).continuous_on).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (continuous_id.prod_mk continuous_const).continuous_on) }
end

theorem is_connected.prod [topological_space β] {s : set α} {t : set β}
  (hs : is_connected s) (ht : is_connected t) : is_connected (s ×ˢ t) :=
⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

theorem is_preconnected_univ_pi [Π i, topological_space (π i)] {s : Π i, set (π i)}
  (hs : ∀ i, is_preconnected (s i)) :
  is_preconnected (pi univ s) :=
begin
  rintros u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩,
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩,
  induction I using finset.induction_on with i I hi ihI,
  { refine ⟨g, hgs, ⟨_, hgv⟩⟩, simpa using hI },
  { rw [finset.piecewise_insert] at hI,
    have := I.piecewise_mem_set_pi hfs hgs,
    refine (hsuv this).elim ihI (λ h, _),
    set S := update (I.piecewise f g) i '' (s i),
    have hsub : S ⊆ pi univ s,
    { refine image_subset_iff.2 (λ z hz, _),
      rwa update_preimage_univ_pi,
      exact λ j hj, this j trivial },
    have hconn : is_preconnected S,
      from (hs i).image _ (continuous_const.update i continuous_id).continuous_on,
    have hSu : (S ∩ u).nonempty,
      from ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩,
    have hSv : (S ∩ v).nonempty,
      from ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩,
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono _,
    exact inter_subset_inter_left _ hsub }
end

@[simp] theorem is_connected_univ_pi [Π i, topological_space (π i)] {s : Π i, set (π i)} :
  is_connected (pi univ s) ↔ ∀ i, is_connected (s i) :=
begin
  simp only [is_connected, ← univ_pi_nonempty_iff, forall_and_distrib, and.congr_right_iff],
  refine λ hne, ⟨λ hc i, _, is_preconnected_univ_pi⟩,
  rw [← eval_image_univ_pi hne],
  exact hc.image _ (continuous_apply _).continuous_on
end

lemma sigma.is_connected_iff [Π i, topological_space (π i)] {s : set (Σ i, π i)} :
  is_connected s ↔ ∃ i t, is_connected t ∧ s = sigma.mk i '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty,
    have : s ⊆ range (sigma.mk i),
    { have h : range (sigma.mk i) = sigma.fst ⁻¹' {i}, by { ext, simp },
      rw h,
      exact is_preconnected.subset_left_of_subset_union
        (is_open_sigma_fst_preimage _) (is_open_sigma_fst_preimage {x | x ≠ i})
        (set.disjoint_iff.2 $ λ x hx, hx.2 hx.1)
        (λ y hy, by simp [classical.em]) ⟨⟨i, x⟩, hx, rfl⟩ hs.2 },
    exact ⟨i, sigma.mk i ⁻¹' s,
      hs.preimage_of_open_map sigma_mk_injective is_open_map_sigma_mk this,
      (set.image_preimage_eq_of_subset this).symm⟩ },
  { rintro ⟨i, t, ht, rfl⟩,
    exact ht.image _ continuous_sigma_mk.continuous_on }
end

lemma sigma.is_preconnected_iff [hι : nonempty ι] [Π i, topological_space (π i)]
  {s : set (Σ i, π i)} :
  is_preconnected s ↔ ∃ i t, is_preconnected t ∧ s = sigma.mk i '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain rfl | h := s.eq_empty_or_nonempty,
    { exact ⟨classical.choice hι, ∅, is_preconnected_empty, (set.image_empty _).symm⟩ },
    { obtain ⟨a, t, ht, rfl⟩ := sigma.is_connected_iff.1 ⟨h, hs⟩,
      refine ⟨a, t, ht.is_preconnected, rfl⟩ } },
  { rintro ⟨a, t, ht, rfl⟩,
    exact ht.image _ continuous_sigma_mk.continuous_on }
end

lemma sum.is_connected_iff [topological_space β] {s : set (α ⊕ β)} :
  is_connected s ↔
    (∃ t, is_connected t ∧ s = sum.inl '' t) ∨ ∃ t, is_connected t ∧ s = sum.inr '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { let u : set (α ⊕ β) := range sum.inl,
    let v : set (α ⊕ β) := range sum.inr,
    have hu : is_open u, exact is_open_range_inl,
    obtain ⟨x | x, hx⟩ := hs.nonempty,
    { have h : s ⊆ range sum.inl := is_preconnected.subset_left_of_subset_union
        is_open_range_inl is_open_range_inr is_compl_range_inl_range_inr.disjoint
        (by simp) ⟨sum.inl x, hx, x, rfl⟩ hs.2,
      refine or.inl ⟨sum.inl ⁻¹' s, _, _⟩,
      { exact hs.preimage_of_open_map sum.inl_injective open_embedding_inl.is_open_map h },
      { exact (set.image_preimage_eq_of_subset h).symm } },
    { have h : s ⊆ range sum.inr := is_preconnected.subset_right_of_subset_union
        is_open_range_inl is_open_range_inr is_compl_range_inl_range_inr.disjoint
        (by simp) ⟨sum.inr x, hx, x, rfl⟩ hs.2,
      refine or.inr ⟨sum.inr ⁻¹' s, _, _⟩,
      { exact hs.preimage_of_open_map sum.inr_injective open_embedding_inr.is_open_map h },
      { exact (set.image_preimage_eq_of_subset h).symm } } },
  { rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩),
    { exact ht.image _ continuous_inl.continuous_on },
    { exact ht.image _ continuous_inr.continuous_on } }
end

lemma sum.is_preconnected_iff [topological_space β] {s : set (α ⊕ β)} :
  is_preconnected s ↔
    (∃ t, is_preconnected t ∧ s = sum.inl '' t) ∨ ∃ t, is_preconnected t ∧ s = sum.inr '' t :=
begin
  refine ⟨λ hs, _, _⟩,
  { obtain rfl | h := s.eq_empty_or_nonempty,
    { exact or.inl ⟨∅, is_preconnected_empty, (set.image_empty _).symm⟩ },
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := sum.is_connected_iff.1 ⟨h, hs⟩,
    { exact or.inl ⟨t, ht.is_preconnected, rfl⟩ },
    { exact or.inr ⟨t, ht.is_preconnected, rfl⟩ } },
  { rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩),
    { exact ht.image _ continuous_inl.continuous_on },
    { exact ht.image _ continuous_inr.continuous_on } }
end

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def connected_component (x : α) : set α :=
⋃₀ { s : set α | is_preconnected s ∧ x ∈ s }

/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
def connected_component_in (F : set α) (x : α) : set α :=
if h : x ∈ F then coe '' (connected_component (⟨x, h⟩ : F)) else ∅

lemma connected_component_in_eq_image {F : set α} {x : α} (h : x ∈ F) :
  connected_component_in F x = coe '' (connected_component (⟨x, h⟩ : F)) :=
dif_pos h

lemma connected_component_in_eq_empty {F : set α} {x : α} (h : x ∉ F) :
  connected_component_in F x = ∅ :=
dif_neg h

theorem mem_connected_component {x : α} : x ∈ connected_component x :=
mem_sUnion_of_mem (mem_singleton x) ⟨is_connected_singleton.is_preconnected, mem_singleton x⟩

theorem mem_connected_component_in {x : α} {F : set α} (hx : x ∈ F) :
  x ∈ connected_component_in F x :=
by simp [connected_component_in_eq_image hx, mem_connected_component, hx]

theorem connected_component_nonempty {x : α} :
  (connected_component x).nonempty :=
⟨x, mem_connected_component⟩

theorem connected_component_in_nonempty_iff {x : α} {F : set α} :
  (connected_component_in F x).nonempty ↔ x ∈ F :=
by { rw [connected_component_in], split_ifs; simp [connected_component_nonempty, h] }

theorem connected_component_in_subset (F : set α) (x : α) :
  connected_component_in F x ⊆ F :=
by { rw [connected_component_in], split_ifs; simp }

theorem is_preconnected_connected_component {x : α} : is_preconnected (connected_component x) :=
is_preconnected_sUnion x _ (λ _, and.right) (λ _, and.left)

lemma is_preconnected_connected_component_in {x : α} {F : set α} :
  is_preconnected (connected_component_in F x) :=
begin
  rw [connected_component_in], split_ifs,
  { exact embedding_subtype_coe.to_inducing.is_preconnected_image.mpr
      is_preconnected_connected_component },
  { exact is_preconnected_empty },
end

theorem is_connected_connected_component {x : α} : is_connected (connected_component x) :=
⟨⟨x, mem_connected_component⟩, is_preconnected_connected_component⟩

lemma is_connected_connected_component_in_iff {x : α} {F : set α} :
  is_connected (connected_component_in F x) ↔ x ∈ F :=
by simp_rw [← connected_component_in_nonempty_iff, is_connected,
  is_preconnected_connected_component_in, and_true]

theorem is_preconnected.subset_connected_component {x : α} {s : set α}
  (H1 : is_preconnected s) (H2 : x ∈ s) : s ⊆ connected_component x :=
λ z hz, mem_sUnion_of_mem hz ⟨H1, H2⟩

lemma is_preconnected.subset_connected_component_in {x : α} {F : set α} (hs : is_preconnected s)
  (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ connected_component_in F x :=
begin
  have : is_preconnected ((coe : F → α) ⁻¹' s),
  { refine embedding_subtype_coe.to_inducing.is_preconnected_image.mp _,
    rwa [subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF] },
  have h2xs : (⟨x, hsF hxs⟩ : F) ∈ coe ⁻¹' s := by { rw [mem_preimage], exact hxs },
  have := this.subset_connected_component h2xs,
  rw [connected_component_in_eq_image (hsF hxs)],
  refine subset.trans _ (image_subset _ this),
  rw [subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF]
end

theorem is_connected.subset_connected_component {x : α} {s : set α}
  (H1 : is_connected s) (H2 : x ∈ s) : s ⊆ connected_component x :=
H1.2.subset_connected_component H2

lemma is_preconnected.connected_component_in {x : α} {F : set α} (h : is_preconnected F)
  (hx : x ∈ F) : connected_component_in F x = F :=
(connected_component_in_subset F x).antisymm (h.subset_connected_component_in hx subset_rfl)

theorem connected_component_eq {x y : α} (h : y ∈ connected_component x) :
  connected_component x = connected_component y :=
eq_of_subset_of_subset
  (is_connected_connected_component.subset_connected_component h)
  (is_connected_connected_component.subset_connected_component
    (set.mem_of_mem_of_subset mem_connected_component
      (is_connected_connected_component.subset_connected_component h)))

theorem connected_component_eq_iff_mem {x y : α} :
  connected_component x = connected_component y ↔ x ∈ connected_component y :=
⟨λ h, h ▸ mem_connected_component, λ h, (connected_component_eq h).symm⟩

lemma connected_component_in_eq {x y : α} {F : set α} (h : y ∈ connected_component_in F x) :
  connected_component_in F x = connected_component_in F y :=
begin
  have hx : x ∈ F := connected_component_in_nonempty_iff.mp ⟨y, h⟩,
  simp_rw [connected_component_in_eq_image hx] at h ⊢,
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h,
  simp_rw [subtype.coe_mk, connected_component_in_eq_image hy, connected_component_eq h2y]
end

theorem connected_component_in_univ (x : α) :
  connected_component_in univ x = connected_component x :=
subset_antisymm
  (is_preconnected_connected_component_in.subset_connected_component $
    mem_connected_component_in trivial)
  (is_preconnected_connected_component.subset_connected_component_in mem_connected_component $
    subset_univ _)

lemma connected_component_disjoint {x y : α} (h : connected_component x ≠ connected_component y) :
  disjoint (connected_component x) (connected_component y) :=
set.disjoint_left.2 (λ a h1 h2, h
  ((connected_component_eq h1).trans (connected_component_eq h2).symm))

theorem is_closed_connected_component {x : α} :
  is_closed (connected_component x) :=
closure_subset_iff_is_closed.1 $
  is_connected_connected_component.closure.subset_connected_component $
    subset_closure mem_connected_component

lemma continuous.image_connected_component_subset [topological_space β] {f : α → β}
  (h : continuous f) (a : α) : f '' connected_component a ⊆ connected_component (f a) :=
(is_connected_connected_component.image f h.continuous_on).subset_connected_component
  ((mem_image f (connected_component a) (f a)).2 ⟨a, mem_connected_component, rfl⟩)

lemma continuous.maps_to_connected_component [topological_space β] {f : α → β}
  (h : continuous f) (a : α) : maps_to f (connected_component a) (connected_component (f a)) :=
maps_to'.2 $ h.image_connected_component_subset a

theorem irreducible_component_subset_connected_component {x : α} :
  irreducible_component x ⊆ connected_component x :=
is_irreducible_irreducible_component.is_connected.subset_connected_component
  mem_irreducible_component

@[mono]
lemma connected_component_in_mono (x : α) {F G : set α} (h : F ⊆ G) :
  connected_component_in F x ⊆ connected_component_in G x :=
begin
  by_cases hx : x ∈ F,
  { rw [connected_component_in_eq_image hx, connected_component_in_eq_image (h hx),
        ← show (coe : G → α) ∘ inclusion h = coe, by ext ; refl, image_comp],
    exact image_subset coe ((continuous_inclusion h).image_connected_component_subset ⟨x, hx⟩) },
  { rw connected_component_in_eq_empty hx,
    exact set.empty_subset _ },
end

/-- A preconnected space is one where there is no non-trivial open partition. -/
class preconnected_space (α : Type u) [topological_space α] : Prop :=
(is_preconnected_univ : is_preconnected (univ : set α))

export preconnected_space (is_preconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class connected_space (α : Type u) [topological_space α] extends preconnected_space α : Prop :=
(to_nonempty : nonempty α)

attribute [instance, priority 50] connected_space.to_nonempty -- see Note [lower instance priority]

lemma is_connected_univ [connected_space α] : is_connected (univ : set α) :=
⟨univ_nonempty, is_preconnected_univ⟩

lemma is_preconnected_range [topological_space β] [preconnected_space α] {f : α → β}
  (h : continuous f) : is_preconnected (range f) :=
@image_univ _ _ f ▸ is_preconnected_univ.image _ h.continuous_on

lemma is_connected_range [topological_space β] [connected_space α] {f : α → β} (h : continuous f) :
  is_connected (range f) :=
⟨range_nonempty f, is_preconnected_range h⟩

lemma dense_range.preconnected_space [topological_space β] [preconnected_space α] {f : α → β}
  (hf : dense_range f) (hc : continuous f) :
  preconnected_space β :=
⟨hf.closure_eq ▸ (is_preconnected_range hc).closure⟩

lemma connected_space_iff_connected_component :
  connected_space α ↔ ∃ x : α, connected_component x = univ :=
begin
  split,
  { rintro ⟨⟨x⟩⟩,
    exactI ⟨x, eq_univ_of_univ_subset $
      is_preconnected_univ.subset_connected_component (mem_univ x)⟩ },
  { rintros ⟨x, h⟩,
    haveI : preconnected_space α := ⟨by { rw ← h, exact is_preconnected_connected_component }⟩,
    exact ⟨⟨x⟩⟩ }
end

lemma preconnected_space_iff_connected_component :
  preconnected_space α ↔ ∀ x : α, connected_component x = univ :=
begin
  split,
  { intros h x,
    exactI (eq_univ_of_univ_subset $
      is_preconnected_univ.subset_connected_component (mem_univ x)) },
  { intros h,
    casesI is_empty_or_nonempty α with hα hα,
    { exact ⟨by { rw (univ_eq_empty_iff.mpr hα), exact is_preconnected_empty }⟩ },
    { exact ⟨by { rw ← h (classical.choice hα), exact is_preconnected_connected_component }⟩ } }
end

@[simp] lemma preconnected_space.connected_component_eq_univ {X : Type*} [topological_space X]
  [h : preconnected_space X] (x : X) : connected_component x = univ :=
preconnected_space_iff_connected_component.mp h x

instance [topological_space β] [preconnected_space α] [preconnected_space β] :
  preconnected_space (α × β) :=
⟨by { rw ← univ_prod_univ, exact is_preconnected_univ.prod is_preconnected_univ }⟩

instance [topological_space β] [connected_space α] [connected_space β] :
  connected_space (α × β) :=
⟨prod.nonempty⟩

instance [Π i, topological_space (π i)] [∀ i, preconnected_space (π i)] :
  preconnected_space (Π i, π i) :=
⟨by { rw ← pi_univ univ, exact is_preconnected_univ_pi (λ i, is_preconnected_univ) }⟩

instance [Π i, topological_space (π i)] [∀ i, connected_space (π i)] : connected_space (Π i, π i) :=
⟨classical.nonempty_pi.2 $ λ i, by apply_instance⟩

@[priority 100] -- see Note [lower instance priority]
instance preirreducible_space.preconnected_space (α : Type u) [topological_space α]
  [preirreducible_space α] : preconnected_space α :=
⟨(preirreducible_space.is_preirreducible_univ α).is_preconnected⟩

@[priority 100] -- see Note [lower instance priority]
instance irreducible_space.connected_space (α : Type u) [topological_space α]
  [irreducible_space α] : connected_space α :=
{ to_nonempty := irreducible_space.to_nonempty α }

theorem nonempty_inter [preconnected_space α] {s t : set α} :
  is_open s → is_open t → s ∪ t = univ → s.nonempty → t.nonempty → (s ∩ t).nonempty :=
by simpa only [univ_inter, univ_subset_iff] using
  @preconnected_space.is_preconnected_univ α _ _ s t

theorem is_clopen_iff [preconnected_space α] {s : set α} : is_clopen s ↔ s = ∅ ∨ s = univ :=
⟨λ hs, classical.by_contradiction $ λ h,
  have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅, from ⟨mt or.inl h,
    mt (λ h2, or.inr $ (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩,
  let ⟨_, h2, h3⟩ := nonempty_inter hs.1 hs.2.is_open_compl (union_compl_self s)
    (nonempty_iff_ne_empty.2 h1.1) (nonempty_iff_ne_empty.2 h1.2) in
  h3 h2,
by rintro (rfl | rfl); [exact is_clopen_empty, exact is_clopen_univ]⟩

lemma is_clopen.eq_univ [preconnected_space α] {s : set α} (h' : is_clopen s) (h : s.nonempty) :
  s = univ :=
(is_clopen_iff.mp h').resolve_left h.ne_empty

lemma frontier_eq_empty_iff [preconnected_space α] {s : set α} :
  frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
is_clopen_iff_frontier_eq_empty.symm.trans is_clopen_iff

lemma nonempty_frontier_iff [preconnected_space α] {s : set α} :
  (frontier s).nonempty ↔ s.nonempty ∧ s ≠ univ :=
by simp only [nonempty_iff_ne_empty, ne.def, frontier_eq_empty_iff, not_or_distrib]

lemma subtype.preconnected_space {s : set α} (h : is_preconnected s) :
  preconnected_space s :=
{ is_preconnected_univ := by rwa [← embedding_subtype_coe.to_inducing.is_preconnected_image,
    image_univ, subtype.range_coe] }

lemma subtype.connected_space {s : set α} (h : is_connected s) :
  connected_space s :=
{ to_preconnected_space := subtype.preconnected_space h.is_preconnected,
  to_nonempty := h.nonempty.to_subtype }

lemma is_preconnected_iff_preconnected_space {s : set α} :
  is_preconnected s ↔ preconnected_space s :=
⟨subtype.preconnected_space,
 begin
   introI,
   simpa using is_preconnected_univ.image (coe : s → α) continuous_subtype_coe.continuous_on
 end⟩

lemma is_connected_iff_connected_space {s : set α} : is_connected s ↔ connected_space s :=
⟨subtype.connected_space,
 λ h, ⟨nonempty_subtype.mp h.2, is_preconnected_iff_preconnected_space.mpr h.1⟩⟩

/-- A set `s` is preconnected if and only if
for every cover by two open sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
lemma is_preconnected_iff_subset_of_disjoint {s : set α} :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_open u) (hv : is_open v) (hs : s ⊆ u ∪ v) (huv : s ∩ (u ∩ v) = ∅),
  s ⊆ u ∨ s ⊆ v :=
begin
  split; intro h,
  { intros u v hu hv hs huv,
    specialize h u v hu hv hs,
    contrapose! huv,
    rw ←nonempty_iff_ne_empty,
    simp [not_subset] at huv,
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩,
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu,
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv,
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩ },
  { intros u v hu hv hs hsu hsv,
    rw nonempty_iff_ne_empty,
    intro H,
    specialize h u v hu hv hs H,
    contrapose H,
    apply nonempty.ne_empty,
    cases h,
    { rcases hsv with ⟨x, hxs, hxv⟩, exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩ },
    { rcases hsu with ⟨x, hxs, hxu⟩, exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩ } }
end

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
lemma is_connected_iff_sUnion_disjoint_open {s : set α} :
  is_connected s ↔
  ∀ (U : finset (set α)) (H : ∀ (u v : set α), u ∈ U → v ∈ U → (s ∩ (u ∩ v)).nonempty → u = v)
  (hU : ∀ u ∈ U, is_open u) (hs : s ⊆ ⋃₀ ↑U),
  ∃ u ∈ U, s ⊆ u :=
begin
  rw [is_connected, is_preconnected_iff_subset_of_disjoint],
  split; intro h,
  { intro U, apply finset.induction_on U,
    { rcases h.left,
      suffices : s ⊆ ∅ → false, { simpa },
      intro, solve_by_elim },
    { intros u U hu IH hs hU H,
      rw [finset.coe_insert, sUnion_insert] at H,
      cases h.2 u (⋃₀ ↑U) _ _ H _ with hsu hsU,
      { exact ⟨u, finset.mem_insert_self _ _, hsu⟩ },
      { rcases IH _ _ hsU with ⟨v, hvU, hsv⟩,
        { exact ⟨v, finset.mem_insert_of_mem hvU, hsv⟩ },
        { intros, apply hs; solve_by_elim [finset.mem_insert_of_mem] },
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { solve_by_elim [finset.mem_insert_self] },
      { apply is_open_sUnion,
        intros, solve_by_elim [finset.mem_insert_of_mem] },
      { apply eq_empty_of_subset_empty,
        rintro x ⟨hxs, hxu, hxU⟩,
        rw mem_sUnion at hxU,
        rcases hxU with ⟨v, hvU, hxv⟩,
        rcases hs u v (finset.mem_insert_self _ _) (finset.mem_insert_of_mem hvU) _ with rfl,
        { contradiction },
        { exact ⟨x, hxs, hxu, hxv⟩ } } } },
  { split,
    { rw nonempty_iff_ne_empty,
      by_contradiction hs, subst hs,
      simpa using h ∅ _ _ _; simp },
    intros u v hu hv hs hsuv,
    rcases h {u, v} _ _ _ with ⟨t, ht, ht'⟩,
    { rw [finset.mem_insert, finset.mem_singleton] at ht,
      rcases ht with rfl|rfl; tauto },
    { intros t₁ t₂ ht₁ ht₂ hst,
      rw nonempty_iff_ne_empty at hst,
      rw [finset.mem_insert, finset.mem_singleton] at ht₁ ht₂,
      rcases ht₁ with rfl|rfl; rcases ht₂ with rfl|rfl,
      all_goals { refl <|> contradiction <|> skip },
      rw inter_comm t₁ at hst, contradiction },
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption },
    { simpa using hs } }
end

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem is_preconnected.subset_clopen {s t : set α} (hs : is_preconnected s) (ht : is_clopen t)
  (hne : (s ∩ t).nonempty) : s ⊆ t :=
begin
  by_contra h,
  have : (s ∩ tᶜ).nonempty := inter_compl_nonempty_iff.2 h,
  obtain ⟨x, -, hx, hx'⟩ : (s ∩ (t ∩ tᶜ)).nonempty,
    from hs t tᶜ ht.is_open ht.compl.is_open (λ x hx, em _) hne this,
  exact hx' hx
end

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem disjoint_or_subset_of_clopen {s t : set α} (hs : is_preconnected s) (ht : is_clopen t) :
  disjoint s t ∨ s ⊆ t :=
(disjoint_or_nonempty_inter s t).imp_right $ hs.subset_clopen ht

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint_closed :
  is_preconnected s ↔
    ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hs : s ⊆ u ∪ v) (huv : s ∩ (u ∩ v) = ∅),
      s ⊆ u ∨ s ⊆ v :=
begin
  split; intro h,
  { intros u v hu hv hs huv,
    rw is_preconnected_closed_iff at h,
    specialize h u v hu hv hs,
    contrapose! huv,
    rw ←nonempty_iff_ne_empty,
    simp [not_subset] at huv,
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩,
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu,
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv,
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩ },
  { rw is_preconnected_closed_iff,
    intros u v hu hv hs hsu hsv,
    rw nonempty_iff_ne_empty,
    intro H,
    specialize h u v hu hv hs H,
    contrapose H,
    apply nonempty.ne_empty,
    cases h,
    { rcases hsv with ⟨x, hxs, hxv⟩, exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩ },
    { rcases hsu with ⟨x, hxs, hxu⟩, exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩ } }
end

/-- A closed set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_fully_disjoint_closed {s : set α} (hs : is_closed s) :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hss : s ⊆ u ∪ v) (huv : disjoint u v),
  s ⊆ u ∨ s ⊆ v :=
begin
  split,
  { intros h u v hu hv hss huv,
    apply is_preconnected_iff_subset_of_disjoint_closed.1 h u v hu hv hss,
    rw [huv.inter_eq, inter_empty] },
  intro H,
  rw is_preconnected_iff_subset_of_disjoint_closed,
  intros u v hu hv hss huv,
  have H1 := H (u ∩ s) (v ∩ s),
  rw [subset_inter_iff, subset_inter_iff] at H1,
  simp only [subset.refl, and_true] at H1,
  apply H1 (is_closed.inter hu hs) (is_closed.inter hv hs),
  { rw ←inter_distrib_right,
    exact subset_inter hss subset.rfl },
  { rwa [disjoint_iff_inter_eq_empty, ←inter_inter_distrib_right, inter_comm] }
end

lemma is_clopen.connected_component_subset {x} (hs : is_clopen s) (hx : x ∈ s) :
  connected_component x ⊆ s :=
is_preconnected_connected_component.subset_clopen hs ⟨x, mem_connected_component, hx⟩

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
lemma connected_component_subset_Inter_clopen {x : α} :
  connected_component x ⊆ ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z :=
subset_Inter $ λ Z, Z.2.1.connected_component_subset Z.2.2

/-- A clopen set is the union of its connected components. -/
lemma is_clopen.bUnion_connected_component_eq {Z : set α} (h : is_clopen Z) :
  (⋃ x ∈ Z, connected_component x) = Z :=
subset.antisymm (Union₂_subset $ λ x, h.connected_component_subset) $
  λ x hx, mem_Union₂_of_mem hx mem_connected_component

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
lemma preimage_connected_component_connected [topological_space β] {f : α → β}
  (connected_fibers : ∀ t : β, is_connected (f ⁻¹' {t}))
  (hcl : ∀ (T : set β), is_closed T ↔ is_closed (f ⁻¹' T)) (t : β) :
  is_connected (f ⁻¹' connected_component t) :=
begin
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : surjective f := surjective.of_comp (λ t : β, (connected_fibers t).1),

  split,
  { cases hf t with s hs,
    use s,
    rw [mem_preimage, hs],
    exact mem_connected_component },

  have hT : is_closed (f ⁻¹' connected_component t) :=
    (hcl (connected_component t)).1 is_closed_connected_component,

  -- To show it's preconnected we decompose (f ⁻¹' connected_component t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw is_preconnected_iff_subset_of_fully_disjoint_closed hT,
  intros u v hu hv huv uv_disj,

  -- To do this we decompose connected_component t into T₁ and T₂
  -- we will show that connected_component t is a subset of either and hence
  -- (f ⁻¹' connected_component t) is a subset of u or v
  let T₁ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ u},
  let T₂ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ v},

  have fiber_decomp : ∀ t' ∈ connected_component t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v,
  { intros t' ht',
    apply is_preconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv,
    { exact subset.trans (hf.preimage_subset_preimage_iff.2 (singleton_subset_iff.2 ht')) huv },
    rw [uv_disj.inter_eq, inter_empty] },

  have T₁_u : f ⁻¹' T₁ = (f ⁻¹' connected_component t) ∩ u,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      refine Union₂_subset (λ t' ht', subset_inter _ ht'.2),
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff],
      exact ht'.1 },
    rintros a ⟨hat, hau⟩,
    constructor,
    { exact mem_preimage.1 hat },
    dsimp only,
    cases fiber_decomp (f a) (mem_preimage.1 hat),
    { exact h },
    { cases (nonempty_of_mem $ mem_inter hau $ h rfl).not_disjoint uv_disj } },
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = (f ⁻¹' connected_component t) ∩ v,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      refine Union₂_subset (λ t' ht', subset_inter _ ht'.2),
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff],
      exact ht'.1 },
    rintros a ⟨hat, hav⟩,
    constructor,
    { exact mem_preimage.1 hat },
    dsimp only,
    cases fiber_decomp (f a) (mem_preimage.1 hat),
    { cases (nonempty_of_mem (mem_inter (h rfl) hav)).not_disjoint uv_disj },
    { exact h } },

  -- Now we show T₁, T₂ are closed, cover connected_component t and are disjoint.
  have hT₁ : is_closed T₁ := ((hcl T₁).2 (T₁_u.symm ▸ (is_closed.inter hT hu))),
  have hT₂ : is_closed T₂ := ((hcl T₂).2 (T₂_v.symm ▸ (is_closed.inter hT hv))),

  have T_decomp : connected_component t ⊆ T₁ ∪ T₂,
  { intros t' ht',
    rw mem_union t' T₁ T₂,
    cases fiber_decomp t' ht' with htu htv,
    { left, exact ⟨ht', htu⟩ },
    right, exact ⟨ht', htv⟩ },

  have T_disjoint : disjoint T₁ T₂,
  { refine disjoint.of_preimage hf _,
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ←inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty] },

  -- Now we do cases on whether (connected_component t) is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  cases (is_preconnected_iff_subset_of_fully_disjoint_closed is_closed_connected_component).1
    is_preconnected_connected_component T₁ T₂ hT₁ hT₂ T_decomp T_disjoint,
  { left,
    rw subset.antisymm_iff at T₁_u,
    suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₁,
    { exact subset.trans (subset.trans this T₁_u.1) (inter_subset_right _ _) },
    exact preimage_mono h },
  right,
  rw subset.antisymm_iff at T₂_v,
  suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₂,
  { exact subset.trans (subset.trans this T₂_v.1) (inter_subset_right _ _) },
  exact preimage_mono h,
end

lemma quotient_map.preimage_connected_component [topological_space β] {f : α → β}
  (hf : quotient_map f) (h_fibers : ∀ y : β, is_connected (f ⁻¹' {y})) (a : α) :
  f ⁻¹' connected_component (f a) = connected_component a :=
((preimage_connected_component_connected h_fibers
  (λ _, hf.is_closed_preimage.symm) _).subset_connected_component mem_connected_component).antisymm
  (hf.continuous.maps_to_connected_component a)

lemma quotient_map.image_connected_component [topological_space β] {f : α → β}
  (hf : quotient_map f) (h_fibers : ∀ y : β, is_connected (f ⁻¹' {y})) (a : α) :
  f '' connected_component a = connected_component (f a) :=
by rw [← hf.preimage_connected_component h_fibers, image_preimage_eq _ hf.surjective]

end preconnected

section locally_connected_space

/-- A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Note that it is equivalent to each point having a basis of connected
(non necessarily open) sets but in a non-trivial way, so we choose this definition and prove the
equivalence later in `locally_connected_space_iff_connected_basis`. -/
class locally_connected_space (α : Type*) [topological_space α] : Prop :=
(open_connected_basis : ∀ x, (𝓝 x).has_basis (λ s : set α, is_open s ∧ x ∈ s ∧ is_connected s) id)

lemma locally_connected_space_iff_open_connected_basis : locally_connected_space α ↔
  ∀ x, (𝓝 x).has_basis (λ s : set α, is_open s ∧ x ∈ s ∧ is_connected s) id :=
⟨@locally_connected_space.open_connected_basis _ _, locally_connected_space.mk⟩

lemma locally_connected_space_iff_open_connected_subsets :
  locally_connected_space α ↔ ∀ (x : α) (U ∈ 𝓝 x), ∃ V ⊆ U, is_open V ∧ x ∈ V ∧ is_connected V :=
begin
  rw locally_connected_space_iff_open_connected_basis,
  congrm ∀ x, (_ : Prop),
  split,
  { intros h U hU,
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩,
    exact ⟨V, hVU, hV⟩ },
  { exact λ h, ⟨λ U, ⟨λ hU, let ⟨V, hVU, hV⟩ := h U hU in ⟨V, hV, hVU⟩,
                λ ⟨V, ⟨hV, hxV, _⟩, hVU⟩, mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩⟩⟩ }
end

/-- A space with discrete topology is a locally connected space. -/
@[priority 100]
instance discrete_topology.to_locally_connected_space (α) [topological_space α]
  [discrete_topology α] : locally_connected_space α :=
locally_connected_space_iff_open_connected_subsets.2 $ λ x _U hU,
  ⟨{x}, singleton_subset_iff.2 $ mem_of_mem_nhds hU, is_open_discrete _, mem_singleton _,
    is_connected_singleton⟩

lemma connected_component_in_mem_nhds [locally_connected_space α] {F : set α} {x : α}
  (h : F ∈ 𝓝 x) :
  connected_component_in F x ∈ 𝓝 x :=
begin
  rw (locally_connected_space.open_connected_basis x).mem_iff at h,
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩,
  exact mem_nhds_iff.mpr ⟨s, h2s.is_preconnected.subset_connected_component_in hxs hsF, h1s, hxs⟩
end

lemma is_open.connected_component_in [locally_connected_space α] {F : set α} {x : α}
  (hF : is_open F) :
  is_open (connected_component_in F x) :=
begin
  rw [is_open_iff_mem_nhds],
  intros y hy,
  rw [connected_component_in_eq hy],
  exact connected_component_in_mem_nhds (is_open_iff_mem_nhds.mp hF y $
    connected_component_in_subset F x hy)
end

lemma is_open_connected_component [locally_connected_space α] {x : α} :
  is_open (connected_component x) :=
begin
  rw ← connected_component_in_univ,
  exact is_open_univ.connected_component_in
end

lemma is_clopen_connected_component [locally_connected_space α] {x : α} :
  is_clopen (connected_component x) :=
⟨is_open_connected_component, is_closed_connected_component⟩

lemma locally_connected_space_iff_connected_component_in_open :
  locally_connected_space α ↔ ∀ F : set α, is_open F → ∀ x ∈ F,
  is_open (connected_component_in F x) :=
begin
  split,
  { introI h,
    exact λ F hF x _, hF.connected_component_in },
  { intro h,
    rw locally_connected_space_iff_open_connected_subsets,
    refine (λ x U hU, ⟨connected_component_in (interior U) x,
      (connected_component_in_subset _ _).trans interior_subset, h _ is_open_interior x _,
      mem_connected_component_in _, is_connected_connected_component_in_iff.mpr _⟩);
    exact (mem_interior_iff_mem_nhds.mpr hU) }
end

lemma locally_connected_space_iff_connected_subsets :
  locally_connected_space α ↔ ∀ (x : α) (U ∈ 𝓝 x), ∃ V ∈ 𝓝 x, is_preconnected V ∧ V ⊆ U :=
begin
  split,
  { rw locally_connected_space_iff_open_connected_subsets,
    intros h x U hxU,
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩,
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.is_preconnected, hVU⟩ },
  { rw locally_connected_space_iff_connected_component_in_open,
    refine λ h U hU x hxU, is_open_iff_mem_nhds.mpr (λ y hy, _),
    rw connected_component_in_eq hy,
    rcases h y U (hU.mem_nhds $ (connected_component_in_subset _ _) hy) with ⟨V, hVy, hV, hVU⟩,
    exact filter.mem_of_superset hVy
      (hV.subset_connected_component_in (mem_of_mem_nhds hVy) hVU) }
end

lemma locally_connected_space_iff_connected_basis :
  locally_connected_space α ↔
  ∀ x, (𝓝 x).has_basis (λ s : set α, s ∈ 𝓝 x ∧ is_preconnected s) id :=
begin
  rw locally_connected_space_iff_connected_subsets,
  congrm ∀ x, (_ : Prop),
  exact filter.has_basis_self.symm
end

lemma locally_connected_space_of_connected_bases {ι : Type*} (b : α → ι → set α) (p : α → ι → Prop)
  (hbasis : ∀ x, (𝓝 x).has_basis (p x) (b x))
  (hconnected : ∀ x i, p x i → is_preconnected (b x i)) :
  locally_connected_space α :=
begin
  rw locally_connected_space_iff_connected_basis,
  exact λ x, (hbasis x).to_has_basis
    (λ i hi, ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩)
    (λ s hs, ⟨(hbasis x).index s hs.1,
      ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩)
end

end locally_connected_space

section totally_disconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton.-/
def is_totally_disconnected (s : set α) : Prop :=
∀ t, t ⊆ s → is_preconnected t → t.subsingleton

theorem is_totally_disconnected_empty : is_totally_disconnected (∅ : set α) :=
λ _ ht _ _ x_in _ _, (ht x_in).elim

theorem is_totally_disconnected_singleton {x} : is_totally_disconnected ({x} : set α) :=
λ _ ht _, subsingleton_singleton.anti ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
class totally_disconnected_space (α : Type u) [topological_space α] : Prop :=
(is_totally_disconnected_univ : is_totally_disconnected (univ : set α))

lemma is_preconnected.subsingleton [totally_disconnected_space α]
  {s : set α} (h : is_preconnected s) : s.subsingleton :=
totally_disconnected_space.is_totally_disconnected_univ s (subset_univ s) h

instance pi.totally_disconnected_space {α : Type*} {β : α → Type*}
  [t₂ : Πa, topological_space (β a)] [∀a, totally_disconnected_space (β a)] :
  totally_disconnected_space (Π (a : α), β a) :=
⟨λ t h1 h2,
  have this : ∀ a, is_preconnected ((λ x : Π a, β a, x a) '' t),
    from λ a, h2.image (λ x, x a) (continuous_apply a).continuous_on,
  λ x x_in y y_in, funext $ λ a, (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

instance prod.totally_disconnected_space [topological_space β]
  [totally_disconnected_space α] [totally_disconnected_space β] :
  totally_disconnected_space (α × β) :=
⟨λ t h1 h2,
have H1 : is_preconnected (prod.fst '' t), from h2.image prod.fst continuous_fst.continuous_on,
have H2 : is_preconnected (prod.snd '' t), from h2.image prod.snd continuous_snd.continuous_on,
λ x hx y hy, prod.ext
  (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

instance [topological_space β] [totally_disconnected_space α] [totally_disconnected_space β] :
  totally_disconnected_space (α ⊕ β) :=
begin
  refine ⟨λ s _ hs, _⟩,
  obtain (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) := sum.is_preconnected_iff.1 hs,
  { exact ht.subsingleton.image _ },
  { exact ht.subsingleton.image _ }
end

instance [Π i, topological_space (π i)] [∀ i, totally_disconnected_space (π i)] :
  totally_disconnected_space (Σ i, π i) :=
begin
  refine ⟨λ s _ hs, _⟩,
  obtain rfl | h := s.eq_empty_or_nonempty,
  { exact subsingleton_empty },
  { obtain ⟨a, t, ht, rfl⟩ := sigma.is_connected_iff.1 ⟨h, hs⟩,
    exact ht.is_preconnected.subsingleton.image _ }
end

/-- Let `X` be a topological space, and suppose that for all distinct `x,y ∈ X`, there
  is some clopen set `U` such that `x ∈ U` and `y ∉ U`. Then `X` is totally disconnected. -/
lemma is_totally_disconnected_of_clopen_set {X : Type*} [topological_space X]
  (hX : ∀ {x y : X} (h_diff : x ≠ y), ∃ (U : set X) (h_clopen : is_clopen U), x ∈ U ∧ y ∉ U) :
  is_totally_disconnected (set.univ : set X) :=
begin
  rintro S - hS,
  unfold set.subsingleton,
  by_contra' h_contra,
  rcases h_contra with ⟨x, hx, y, hy, hxy⟩,
  obtain ⟨U, h_clopen, hxU, hyU⟩ := hX hxy,
  specialize hS U Uᶜ h_clopen.1 h_clopen.compl.1 (λ a ha, em (a ∈ U)) ⟨x, hx, hxU⟩ ⟨y, hy, hyU⟩,
  rw [inter_compl_self, set.inter_empty] at hS,
  exact set.not_nonempty_empty hS,
end

/-- A space is totally disconnected iff its connected components are subsingletons. -/
lemma totally_disconnected_space_iff_connected_component_subsingleton :
  totally_disconnected_space α ↔ ∀ x : α, (connected_component x).subsingleton :=
begin
  split,
  { intros h x,
    apply h.1,
    { exact subset_univ _ },
    exact is_preconnected_connected_component },
  intro h, constructor,
  intros s s_sub hs,
  rcases eq_empty_or_nonempty s with rfl | ⟨x, x_in⟩,
  { exact subsingleton_empty },
  { exact (h x).anti (hs.subset_connected_component x_in) }
end

/-- A space is totally disconnected iff its connected components are singletons. -/
lemma totally_disconnected_space_iff_connected_component_singleton :
  totally_disconnected_space α ↔ ∀ x : α, connected_component x = {x} :=
begin
  rw totally_disconnected_space_iff_connected_component_subsingleton,
  apply forall_congr (λ x, _),
  rw subsingleton_iff_singleton,
  exact mem_connected_component
end

@[simp] theorem connected_component_eq_singleton [totally_disconnected_space α] (x : α) :
  connected_component x = {x} :=
totally_disconnected_space_iff_connected_component_singleton.1 ‹_› x

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp] lemma continuous.image_connected_component_eq_singleton {β : Type*} [topological_space β]
  [totally_disconnected_space β] {f : α → β} (h : continuous f) (a : α) :
  f '' connected_component a = {f a} :=
(set.subsingleton_iff_singleton $ mem_image_of_mem f mem_connected_component).mp
  (is_preconnected_connected_component.image f h.continuous_on).subsingleton

lemma is_totally_disconnected_of_totally_disconnected_space [totally_disconnected_space α]
  (s : set α) : is_totally_disconnected s :=
λ t hts ht, totally_disconnected_space.is_totally_disconnected_univ _ t.subset_univ ht

lemma is_totally_disconnected_of_image [topological_space β] {f : α → β} (hf : continuous_on f s)
  (hf' : injective f) (h : is_totally_disconnected (f '' s)) : is_totally_disconnected s :=
λ t hts ht x x_in y y_in, hf' $ h _ (image_subset f hts) (ht.image f $ hf.mono hts)
  (mem_image_of_mem f x_in) (mem_image_of_mem f y_in)

lemma embedding.is_totally_disconnected [topological_space β] {f : α → β} (hf : embedding f)
  {s : set α} (h : is_totally_disconnected (f '' s)) : is_totally_disconnected s :=
is_totally_disconnected_of_image hf.continuous.continuous_on hf.inj h

instance subtype.totally_disconnected_space {α : Type*} {p : α → Prop} [topological_space α]
  [totally_disconnected_space α] : totally_disconnected_space (subtype p) :=
⟨embedding_subtype_coe.is_totally_disconnected
  (is_totally_disconnected_of_totally_disconnected_space _)⟩

end totally_disconnected

section totally_separated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def is_totally_separated (s : set α) : Prop :=
∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ u v : set α, is_open u ∧ is_open v ∧
  x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ disjoint u v

theorem is_totally_separated_empty : is_totally_separated (∅ : set α) :=
λ x, false.elim

theorem is_totally_separated_singleton {x} : is_totally_separated ({x} : set α) :=
λ p hp q hq hpq, (hpq $ (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

theorem is_totally_disconnected_of_is_totally_separated {s : set α}
  (H : is_totally_separated s) : is_totally_disconnected s :=
begin
  intros t hts ht x x_in y y_in,
  by_contra h,
  obtain ⟨u : set α, v : set α, hu : is_open u, hv : is_open v,
          hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v, huv⟩ :=
    H x (hts x_in) y (hts y_in) h,
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty _,
  rw [huv.inter_eq, inter_empty],
end

alias is_totally_disconnected_of_is_totally_separated ← is_totally_separated.is_totally_disconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class totally_separated_space (α : Type u) [topological_space α] : Prop :=
(is_totally_separated_univ [] : is_totally_separated (univ : set α))

@[priority 100] -- see Note [lower instance priority]
instance totally_separated_space.totally_disconnected_space (α : Type u) [topological_space α]
  [totally_separated_space α] : totally_disconnected_space α :=
⟨is_totally_disconnected_of_is_totally_separated $
  totally_separated_space.is_totally_separated_univ α⟩

@[priority 100] -- see Note [lower instance priority]
instance totally_separated_space.of_discrete
  (α : Type*) [topological_space α] [discrete_topology α] : totally_separated_space α :=
⟨λ a _ b _ h, ⟨{b}ᶜ, {b}, is_open_discrete _, is_open_discrete _, by simpa⟩⟩

lemma exists_clopen_of_totally_separated {α : Type*} [topological_space α]
  [totally_separated_space α] {x y : α} (hxy : x ≠ y) :
  ∃ (U : set α) (hU : is_clopen U), x ∈ U ∧ y ∈ Uᶜ :=
begin
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    totally_separated_space.is_totally_separated_univ α x (set.mem_univ x) y (set.mem_univ y) hxy,
  have clopen_U := is_clopen_inter_of_disjoint_cover_clopen (is_clopen_univ) f hU hV disj,
  rw univ_inter _ at clopen_U,
  rw [←set.subset_compl_iff_disjoint_right, subset_compl_comm] at disj,
  exact ⟨U, clopen_U, Ux, disj Vy⟩,
end

end totally_separated

section connected_component_setoid

/-- The setoid of connected components of a topological space -/
def connected_component_setoid (α : Type*) [topological_space α] : setoid α :=
⟨λ x y, connected_component x = connected_component y,
  ⟨λ x, by trivial, λ x y h1, h1.symm, λ x y z h1 h2, h1.trans h2⟩⟩

/-- The quotient of a space by its connected components -/
def connected_components (α : Type u) [topological_space α] :=
quotient (connected_component_setoid α)

instance : has_coe_t α (connected_components α) := ⟨quotient.mk'⟩

namespace connected_components

@[simp] lemma coe_eq_coe {x y : α} :
  (x : connected_components α) = y ↔ connected_component x = connected_component y :=
quotient.eq'

lemma coe_ne_coe {x y : α} :
  (x : connected_components α) ≠ y ↔ connected_component x ≠ connected_component y :=
not_congr coe_eq_coe

lemma coe_eq_coe' {x y : α} :
  (x : connected_components α) = y ↔ x ∈ connected_component y :=
coe_eq_coe.trans connected_component_eq_iff_mem

instance [inhabited α] : inhabited (connected_components α) := ⟨↑(default : α)⟩

instance : topological_space (connected_components α) :=
quotient.topological_space

lemma surjective_coe : surjective (coe : α → connected_components α) := surjective_quot_mk _
lemma quotient_map_coe : quotient_map (coe : α → connected_components α) := quotient_map_quot_mk

@[continuity]
lemma continuous_coe : continuous (coe : α → connected_components α) := quotient_map_coe.continuous

@[simp] lemma range_coe : range (coe : α → connected_components α)= univ :=
surjective_coe.range_eq

end connected_components

variables [topological_space β] [totally_disconnected_space β] {f : α → β}

lemma continuous.image_eq_of_connected_component_eq (h : continuous f) (a b : α)
  (hab : connected_component a = connected_component b) : f a = f b :=
singleton_eq_singleton_iff.1 $
  h.image_connected_component_eq_singleton a ▸
  h.image_connected_component_eq_singleton b ▸ hab ▸ rfl

/--
The lift to `connected_components α` of a continuous map from `α` to a totally disconnected space
-/
def continuous.connected_components_lift (h : continuous f) :
  connected_components α → β :=
λ x, quotient.lift_on' x f h.image_eq_of_connected_component_eq

@[continuity] lemma continuous.connected_components_lift_continuous (h : continuous f) :
  continuous h.connected_components_lift :=
h.quotient_lift_on' h.image_eq_of_connected_component_eq

@[simp] lemma continuous.connected_components_lift_apply_coe (h : continuous f) (x : α) :
  h.connected_components_lift x = f x := rfl

@[simp] lemma continuous.connected_components_lift_comp_coe (h : continuous f) :
  h.connected_components_lift ∘ coe = f := rfl

lemma connected_components_lift_unique' {β : Sort*} {g₁ g₂ : connected_components α → β}
  (hg : g₁ ∘ (coe : α → connected_components α) = g₂ ∘ coe) :
  g₁ = g₂ :=
connected_components.surjective_coe.injective_comp_right hg

lemma continuous.connected_components_lift_unique (h : continuous f)
  (g : connected_components α → β) (hg : g ∘ coe = f) : g = h.connected_components_lift :=
connected_components_lift_unique' $ hg.trans h.connected_components_lift_comp_coe.symm

/-- The preimage of a singleton in `connected_components` is the connected component
of an element in the equivalence class. -/
lemma connected_components_preimage_singleton {x : α} :
  coe ⁻¹' ({x} : set (connected_components α)) = connected_component x :=
by { ext y, simp [connected_components.coe_eq_coe'] }

/-- The preimage of the image of a set under the quotient map to `connected_components α`
is the union of the connected components of the elements in it. -/
lemma connected_components_preimage_image (U : set α) :
  coe ⁻¹' (coe '' U : set (connected_components α)) = ⋃ x ∈ U, connected_component x :=
by simp only [connected_components_preimage_singleton, preimage_Union₂, image_eq_Union]

instance connected_components.totally_disconnected_space :
  totally_disconnected_space (connected_components α) :=
begin
  rw totally_disconnected_space_iff_connected_component_singleton,
  refine connected_components.surjective_coe.forall.2 (λ x, _),
  rw [← connected_components.quotient_map_coe.image_connected_component,
    ← connected_components_preimage_singleton,
    image_preimage_eq _ connected_components.surjective_coe],
  refine connected_components.surjective_coe.forall.2 (λ y, _),
  rw connected_components_preimage_singleton,
  exact is_connected_connected_component
end

/-- Functoriality of `connected_components` -/
def continuous.connected_components_map {β : Type*} [topological_space β] {f : α → β}
  (h : continuous f) : connected_components α → connected_components β :=
continuous.connected_components_lift (continuous_quotient_mk.comp h)

lemma continuous.connected_components_map_continuous {β : Type*} [topological_space β] {f : α → β}
  (h : continuous f) : continuous h.connected_components_map :=
continuous.connected_components_lift_continuous (continuous_quotient_mk.comp h)

end connected_component_setoid

/-- A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s` -/
lemma is_preconnected.constant {Y : Type*} [topological_space Y] [discrete_topology Y]
  {s : set α} (hs : is_preconnected s) {f : α → Y} (hf : continuous_on f s)
  {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
(hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- If every map to `bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected -/
lemma is_preconnected_of_forall_constant {s : set α}
  (hs : ∀ f : α → bool, continuous_on f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : is_preconnected s :=
begin
  unfold is_preconnected,
  by_contra',
  rcases this with ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩,
  rw [not_nonempty_iff_eq_empty] at H,
  have hy : y ∉ u,
    from λ y_in_u, eq_empty_iff_forall_not_mem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩,
  have : continuous_on u.bool_indicator s,
  { apply (continuous_on_indicator_iff_clopen _ _).mpr ⟨_, _⟩,
    { exact continuous_subtype_coe.is_open_preimage u u_op },
    { rw preimage_subtype_coe_eq_compl hsuv H,
      exact (continuous_subtype_coe.is_open_preimage v v_op).is_closed_compl } },
  simpa [(u.mem_iff_bool_indicator _).mp x_in_u, (u.not_mem_iff_bool_indicator _).mp hy] using
    hs _ this x x_in_s y y_in_s
end

/-- A `preconnected_space` version of `is_preconnected.constant` -/
lemma preconnected_space.constant {Y : Type*} [topological_space Y] [discrete_topology Y]
  (hp : preconnected_space α) {f : α → Y} (hf : continuous f) {x y : α} : f x = f y :=
is_preconnected.constant hp.is_preconnected_univ (continuous.continuous_on hf) trivial trivial

/-- A `preconnected_space` version of `is_preconnected_of_forall_constant` -/
lemma preconnected_space_of_forall_constant (hs : ∀ f : α → bool, continuous f → ∀ x y, f x = f y) :
  preconnected_space α :=
⟨is_preconnected_of_forall_constant
  (λ f hf x hx y hy, hs f (continuous_iff_continuous_on_univ.mpr hf) x y)⟩

/-- Refinement of `is_preconnected.constant` only assuming the map factors through a
discrete subset of the target. -/
lemma is_preconnected.constant_of_maps_to [topological_space β]
  {S : set α} (hS : is_preconnected S) {T : set β} [discrete_topology T] {f : α → β}
  (hc : continuous_on f S) (hTm : maps_to f S T)
  {x y : α} (hx : x ∈ S) (hy : y ∈ S) : f x = f y :=
begin
  let F : S → T := (λ x:S, ⟨f x.val, hTm x.property⟩),
  suffices : F ⟨x, hx⟩ = F ⟨y, hy⟩,
  { rw ←subtype.coe_inj at this, exact this },
  exact (is_preconnected_iff_preconnected_space.mp hS).constant
    (continuous_induced_rng.mpr $ continuous_on_iff_continuous_restrict.mp hc)
end
