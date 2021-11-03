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

@[to_additive]
instance {M} [has_mul M] : has_mul (ultrafilter M) := { mul := λ U V, (*) <$> U <*> V }

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
lemma eventually_mul {M} [has_mul M] (U V : ultrafilter M) (p : M → Prop) :
  (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') := iff.rfl

@[to_additive]
instance {M} [semigroup M] : semigroup (ultrafilter M) :=
{ mul_assoc := λ U V W, ultrafilter.coe_inj.mp $ filter.ext' $ λ p,
    by simp only [eventually_mul, mul_assoc]
  ..ultrafilter.has_mul }

/- We don't prove `continuous_mul_right`, because in general it is false! -/
@[to_additive]
lemma continuous_mul_left {M} [semigroup M] (V : ultrafilter M) : continuous (* V) :=
topological_space.is_topological_basis.continuous ultrafilter_basis_is_basis _ $
set.forall_range_iff.mpr $ λ s, ultrafilter_is_open_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }

/-- Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
an idempotent, i.e. an `m` such that `m * m = m`. -/
@[to_additive "Any nonempty compact Hausdorff additive semigroup where right-addition is continuous
contains an idempotent, i.e. an `m` such that `m + m = m`"]
lemma exists_idempotent_of_compact_t2_of_continuous_mul_left {M} [nonempty M] [semigroup M]
  [topological_space M] [compact_space M] [t2_space M]
  (continuous_mul_left : ∀ r : M, continuous (* r)) : ∃ m : M, m * m = m :=
begin
/- We apply Zorn's lemma to the poset of nonempty closed subsemigroups of `M`. It will turn out that
any minimal element is `{m}` for an idempotent `m : M`. -/
  let S : set (set M) := { N : set M | is_closed N ∧ N.nonempty ∧ ∀ m m' ∈ N, m * m' ∈ N },
  suffices : ∃ N ∈ S, ∀ N' ∈ S, N' ⊆ N → N' = N,
  { rcases this with ⟨N, ⟨N_closed, ⟨m, hm⟩, N_mul⟩, N_minimal⟩,
    use m,
/- We now have an element `m : M` of a minimal subsemigroup `N`, and want to show `m + m = m`.
We first show that every element of `N` is of the form `m' + m`.-/
    have scaling_eq_self : (* m) '' N = N,
    { apply N_minimal,
      { refine ⟨is_compact.is_closed (is_compact.image (is_closed.is_compact N_closed)
          (continuous_mul_left m)), ⟨_, ⟨m, hm, rfl⟩⟩, _⟩,
        rintros _ _ ⟨m'', hm'', rfl⟩ ⟨m', hm', rfl⟩,
        exact ⟨m'' * m * m', N_mul _ _ (N_mul _ _ hm'' hm) hm', mul_assoc _ _ _⟩, },
      { rintros _ ⟨m', hm', rfl⟩,
        exact N_mul _ _ hm' hm, }, },
/- In particular, this means that `m' * m = m` for some `m'`. We now use minimality again to show
that this holds for _all_ `m' ∈ N`. -/
    have absorbing_eq_self : N ∩ { m' | m' * m = m} = N,
    { apply N_minimal,
      { refine ⟨N_closed.inter (is_closed.preimage (continuous_mul_left m) (t1_space.t1 m)), _, _⟩,
        { rw ←scaling_eq_self at hm, exact hm },
        { rintros m'' m' ⟨mem'', eq'' : _ = m⟩ ⟨mem', eq' : _ = m⟩,
          refine ⟨N_mul _ _ mem'' mem', _⟩,
          rw [set.mem_set_of_eq, mul_assoc, eq', eq''], }, },
      apply set.inter_subset_left, },
/- Thus `m * m = m` as desired. -/
    rw ←absorbing_eq_self at hm,
    exact hm.2, },
  apply zorn.zorn_superset,
  intros c hcs hc,
  refine ⟨⋂₀ c, ⟨is_closed_sInter $ λ t ht, (hcs ht).1, _, _⟩, _⟩,
  { obtain rfl | hcnemp := c.eq_empty_or_nonempty,
    { rw set.sInter_empty, apply set.univ_nonempty, },
    convert @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ _
      (c.nonempty_coe_sort.mpr hcnemp) (coe : c → set M) _ _ _ _,
    { simp only [subtype.range_coe_subtype, set.set_of_mem_eq] } ,
    { refine directed_on_iff_directed.mp (zorn.chain.directed_on _), exact hc.symm, },
    { intro i, exact (hcs i.property).2.1, },
    { intro i, exact is_closed.is_compact (hcs i.property).1, },
    { intro i, exact (hcs i.property).1, }, },
  { intros m m' hm hm',
    rw set.mem_sInter,
    intros t ht,
    exact (hcs ht).2.2 m m' (set.mem_sInter.mp hm t ht) (set.mem_sInter.mp hm' t ht), },
  { intros s hs, exact set.sInter_subset_of_mem hs, },
end

/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[to_additive exists_idempotent_in_compact_add_subsemigoup "A version of
`exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in some specified
nonempty compact additive subsemigroup."]
lemma exists_idempotent_in_compact_subsemigroup {M} [semigroup M] [topological_space M] [t2_space M]
  (continuous_mul_left : ∀ r : M, continuous (* r))
  (s : set M) (snemp : s.nonempty) (s_compact : is_compact s) (s_add : ∀ x y ∈ s, x * y ∈ s) :
  ∃ m ∈ s, m * m = m :=
begin
  let M' := { m // m ∈ s },
  letI : semigroup M' :=
    { mul       := λ p q, ⟨p.1 * q.1, s_add _ _ p.2 q.2⟩,
      mul_assoc := λ p q r, subtype.eq (mul_assoc _ _ _) },
  haveI : compact_space M' := is_compact_iff_compact_space.mp s_compact,
  haveI : nonempty M' := nonempty_subtype.mpr snemp,
  have : ∀ p : M', continuous (* p) := λ p, continuous_subtype_mk _
    ((continuous_mul_left p.1).comp continuous_subtype_val),
  obtain ⟨⟨m, hm⟩, idem⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left this,
  exact ⟨m, hm, subtype.ext_iff.mp idem⟩,
end

/-- `FS_aux a m` says that `m : M` is the sum of a finite nonempty subsequence of `a : stream M`. We
define it directly as an inductive prop instead of talking about finite subsequences. -/
inductive FS_aux {M} [add_semigroup M] : stream M → M → Prop
| singleton (a : stream M) : FS_aux a a.head
| tail (a : stream M) (m : M) (h : FS_aux a.tail m) : FS_aux a m
| cons (a : stream M) (m : M) (h : FS_aux a.tail m) : FS_aux a (a.head + m)

/-- The set of finite sums in a sequence. -/
def FS {M} [add_semigroup M] (a : stream M) : set M := { m | FS_aux a m }

/-- If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'` is obtained from
a subsequence of `M` starting sufficiently late. -/
lemma FS_add {M} [add_semigroup M] {a : stream M} {m : M} (hm : m ∈ FS a) :
  ∃ n, ∀ m' ∈ FS (stream.tail^[n] a), m + m' ∈ FS a :=
begin
  induction hm with a a m hm ih a m hm ih,
  { exact ⟨1, λ m hm, FS_aux.cons a m hm⟩, },
  { cases ih with n hn, use n+1, intros m' hm', exact FS_aux.tail _ _ (hn _ hm'), },
  { cases ih with n hn, use n+1, intros m' hm', rw add_assoc, exact FS_aux.cons _ _ (hn _ hm'), },
end

lemma exists_idempotent_ultrafilter_le_FS {M} [add_semigroup M] (a : stream M) :
  ∃ U : ultrafilter M, U + U = U ∧ ∀ᶠ m in U, m ∈ FS a :=
begin
  let S : set (ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FS (stream.tail^[n] a) },
  obtain ⟨U, hU, U_idem⟩ :=
    exists_idempotent_in_compact_add_subsemigoup _ S _ _ _,
  { refine ⟨U, U_idem, _⟩, convert set.mem_Inter.mp hU 0, },
  { exact continuous_add_left },
  { let f : filter M := ⨅ n, principal (FS $ stream.tail^[n] a),
    haveI : ne_bot f := sorry,
    obtain ⟨U, hU⟩ := ultrafilter.exists_le f,
    refine ⟨U, _⟩,
    intro n,
    sorry, },
  { apply is_closed.is_compact, exact is_closed_Inter (λ i, ultrafilter_is_closed_basic _) },
  { intros U V hU hV, rw set.mem_Inter at *,
    intro n,
    rw [set.mem_set_of_eq, eventually_add],
    apply eventually.mono (hU n),
    intros m hm,
    obtain ⟨n', hn⟩ := FS_add hm,
    apply eventually.mono (hV (n' + n)),
    intros m' hm',
    apply hn,
    simpa only [function.iterate_add_apply] using hm', }
end

lemma exists_FS_of_large {M} [add_semigroup M] (U : ultrafilter M) (U_idem : U + U = U)
  (s₀ : set M) (sU : s₀ ∈ U) : ∃ a, FS a ⊆ s₀ :=
begin
  have exists_elem : ∀ (s : set M) (hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m + m' ∈ s }).nonempty :=
    λ s hs, ultrafilter.nonempty_of_mem (inter_mem hs $ by { rw ←U_idem at hs, exact hs }),
  let elem : { s // s ∈ U } → M := λ p, set.nonempty.some (exists_elem p.val p.property),
  let succ : { s // s ∈ U } → { s // s ∈ U } := λ p, ⟨p.val ∩ { m | elem p + m ∈ p.val }, _⟩,
  use stream.corec elem succ (subtype.mk s₀ sU),
  { suffices : ∀ (a : stream M) (m ∈ FS a), ∀ p, a = stream.corec elem succ p → m ∈ p.val,
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
  ∃ (c ∈ s) (a : stream M), FS a ⊆ c :=
begin
  have : ∃ U : ultrafilter M, U + U = U,
  { apply exists_idempotent_of_compact_t2_of_continuous_add_left, apply continuous_add_left, },
  obtain ⟨U, U_idem⟩ := this,
  obtain ⟨c, c_s, hc⟩ := (ultrafilter.finite_sUnion_mem_iff s_finite).mp _,
  refine ⟨c, c_s, exists_FS_of_large U U_idem c hc⟩,
  rw s_covers,
  exact univ_mem,
end
