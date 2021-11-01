/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import topology.stone_cech
import data.stream

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. We prove the theorem for a general
semigroup `M` instead of `ℕ+` since it is no harder, although this special case implies the general
case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And a general topological argument shows the existence of an idempotent
ultrafilter (see `exists_idempotent`).

## Main results

- `exists_FS_of_finite_cover`: Hindman's theorem on finite sums.

-/

open filter

instance {M} [has_add M] : has_add (ultrafilter M) := { add := λ U V, (+) <$> U <*> V }

lemma eventually_add {M} [has_add M] (U V : ultrafilter M) (p : M → Prop) :
  (∀ᶠ m in ↑(U + V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m + m') := iff.refl _

instance {M} [add_semigroup M] : add_semigroup (ultrafilter M) :=
{ add_assoc := λ U V W, ultrafilter.coe_inj.mp $ filter.ext' $ λ p,
    by simp only [eventually_add, add_assoc]
  ..ultrafilter.has_add }

lemma left_continuity {M} [add_semigroup M] (V : ultrafilter M) : continuous (+ V) :=
topological_space.is_topological_basis.continuous ultrafilter_basis_is_basis _ $
set.forall_range_iff.mpr $ λ s, ultrafilter_is_open_basic { m : M | ∀ᶠ m' in V, m + m' ∈ s }

lemma exists_idempotent (M : Type*) [add_semigroup M] [nonempty M] [topological_space M]
  [compact_space M] [t2_space M] (left_continuity : ∀ r : M, continuous (+ r)) :
  ∃ m : M, m + m = m :=
begin
  let S : set (set M) := { N : set M | is_closed N ∧ N.nonempty ∧ ∀ m m' ∈ N, m + m' ∈ N },
  suffices : ∃ N ∈ S, ∀ N' ∈ S, N' ⊆ N → N' = N,
  { rcases this with ⟨N, ⟨N_closed, ⟨m, hm⟩, N_add⟩, N_minimal⟩,
    use m,
    have translate_eq : (+ m) '' N = N,
    { apply N_minimal,
      { refine ⟨is_compact.is_closed (is_compact.image (is_closed.is_compact N_closed)
        (left_continuity m)), ⟨_, ⟨m, hm, rfl⟩⟩, _⟩,
        rintros _ _ ⟨m'', hm'', rfl⟩ ⟨m', hm', rfl⟩,
        exact ⟨m'' + m + m', N_add _ _ (N_add _ _ hm'' hm) hm', add_assoc _ _ _⟩, },
      { rintros _ ⟨m', hm', rfl⟩,
        exact N_add _ _ hm' hm, }, },
    have absorbing_eq : N ∩ { m' | m' + m = m} = N,
    { apply N_minimal,
      { refine ⟨N_closed.inter (is_closed.preimage (left_continuity m) (t1_space.t1 m)), _, _⟩,
        { change m ∈ (+ m) '' N, rw translate_eq, exact hm, },
        { rintros m'' m' ⟨mem'', eq'' : _ = m⟩ ⟨mem', eq' : _ = m⟩,
          refine ⟨N_add _ _ mem'' mem', _⟩,
          rw [set.mem_set_of_eq, add_assoc, eq', eq''], }, },
      apply set.inter_subset_left, },
    rw ←absorbing_eq at hm,
    exact hm.2, },
  apply zorn.zorn_superset,
  intros c hcs hc,
  refine ⟨⋂₀ c, ⟨is_closed_sInter $ λ t ht, (hcs ht).1, _, _⟩, _⟩,
  { obtain rfl | hcnemp := c.eq_empty_or_nonempty,
    { simp only [set.univ_nonempty, set.sInter_empty] },
    convert @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ _
      (c.nonempty_coe_sort.mpr hcnemp) (coe : c → set M) _ _ _ _,
    { simp only [subtype.range_coe_subtype, set.set_of_mem_eq] } ,
    { intros a b,
      cases hc.total_of_refl a.2 b.2,
      { exact ⟨a, set.subset.rfl, h⟩, },
      { exact ⟨b, h, set.subset.rfl⟩, }, },
    { intro i, exact (hcs i.property).2.1, },
    { intro i, exact is_closed.is_compact (hcs i.property).1, },
    { intro i, exact (hcs i.property).1, }, },
  { intros m m' hm hm',
    rw set.mem_sInter,
    intros t ht,
    exact (hcs ht).2.2 m m' (set.mem_sInter.mp hm t ht) (set.mem_sInter.mp hm' t ht), },
  { intros s hs, exact set.sInter_subset_of_mem hs, },
end

/-- `FS a m` says that `m : M` is the sum of a finite nonempty subsequence of `a : stream M`. We
define it directly as an inductive prop instead of talking about finite subsequences. -/
inductive FS {M} [add_semigroup M] : stream M → M → Prop
| singleton (a : stream M) : FS a a.head
| tail (a : stream M) (m : M) (h : FS a.tail m) : FS a m
| add (a : stream M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

lemma exists_FS_of_large {M} [add_semigroup M] (U : ultrafilter M) (U_idem : U + U = U)
  (s₀ : set M) (sU : s₀ ∈ U) : ∃ a, ∀ m, FS a m → m ∈ s₀ :=
begin
  have exists_elem : ∀ (s : set M) (hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m + m' ∈ s }).nonempty :=
    λ s hs, ultrafilter.nonempty_of_mem (inter_mem hs $ by { rw ←U_idem at hs, exact hs }),
  let elem : { s // s ∈ U } → M := λ p, set.nonempty.some (exists_elem p.val p.property),
  let succ : { s // s ∈ U } → { s // s ∈ U } := λ p, ⟨p.val ∩ { m | elem p + m ∈ p.val }, _⟩,
  use stream.corec elem succ (subtype.mk s₀ sU),
  { suffices : ∀ (a : stream M) (m : M), FS a m → ∀ p, a = stream.corec elem succ p → m ∈ p.val,
    { intros m hm, exact this _ m hm ⟨s₀, sU⟩ rfl, },
    clear sU s₀,
    intros a m h,
    induction h with b b n h ih b n h ih,
    { rintros p rfl,
      rw [stream.corec_eq, stream.head_cons],
      exact set.inter_subset_left _ _ (set.nonempty.some_mem _), },
    { rintros p rfl,
      refine set.inter_subset_left _ _ (ih (succ p) _),
      rw [stream.corec_eq, stream.tail_cons], },
    { rintros p rfl,
      have := set.inter_subset_right _ _ (ih (succ p) _),
      { simpa only using this },
      rw [stream.corec_eq, stream.tail_cons], }, },
  apply inter_mem p.property,
  convert set.inter_subset_right _ _ (set.nonempty.some_mem $ exists_elem p.val p.property),
end

/-- **Hindman's theorem** -/
theorem exists_FS_of_finite_cover {M} [add_semigroup M] [nonempty M] (s : set (set M))
  (s_finite : s.finite) (s_covers : ⋃₀ s = set.univ) :
  ∃ (c ∈ s) (a : stream M), ∀ m, FS a m → m ∈ c :=
begin
  have : ∃ U : ultrafilter M, U + U = U,
  { apply exists_idempotent, apply left_continuity, },
  obtain ⟨U, U_idem⟩ := this,
  obtain ⟨c, c_s, hc⟩ := (ultrafilter.finite_sUnion_mem_iff s_finite).mp _,
  refine ⟨c, c_s, exists_FS_of_large U U_idem c hc⟩,
  rw s_covers,
  exact univ_mem,
end
