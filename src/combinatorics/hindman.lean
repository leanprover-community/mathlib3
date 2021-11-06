/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import topology.stone_cech
import topology.algebra.semigroup
import data.stream

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/

open filter

@[to_additive]
instance {M} [has_mul M] : has_mul (ultrafilter M) := { mul := λ U V, (*) <$> U <*> V }

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
lemma ultrafilter.eventually_mul {M} [has_mul M] (U V : ultrafilter M) (p : M → Prop) :
  (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') := iff.rfl

@[to_additive]
instance {M} [semigroup M] : semigroup (ultrafilter M) :=
{ mul_assoc := λ U V W, ultrafilter.coe_inj.mp $ filter.ext' $ λ p,
    by simp only [ultrafilter.eventually_mul, mul_assoc]
  ..ultrafilter.has_mul }

/- We don't prove `continuous_mul_right`, because in general it is false! -/
@[to_additive]
lemma ultrafilter.continuous_mul_left {M} [semigroup M] (V : ultrafilter M) : continuous (* V) :=
topological_space.is_topological_basis.continuous ultrafilter_basis_is_basis _ $
set.forall_range_iff.mpr $ λ s, ultrafilter_is_open_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }

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
  obtain ⟨U, hU, U_idem⟩ := exists_idempotent_in_compact_add_subsemigoup _ S _ _ _,
  { refine ⟨U, U_idem, _⟩, convert set.mem_Inter.mp hU 0, },
  { exact ultrafilter.continuous_add_left },
  { apply is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed,
    { intros n U hU,
      apply eventually.mono hU,
      intros m hm,
      apply FS_aux.tail,
      simpa only [function.iterate_succ_apply'] using hm, },
    { intro n, exact ⟨pure _, mem_pure.mpr $ FS_aux.singleton _⟩, },
    { exact (ultrafilter_is_closed_basic _).is_compact, },
    { intro n, apply ultrafilter_is_closed_basic, }, },
  { exact is_closed.is_compact (is_closed_Inter $ λ i, ultrafilter_is_closed_basic _) },
  { intros U V hU hV,
    rw set.mem_Inter at *,
    intro n,
    rw [set.mem_set_of_eq, ultrafilter.eventually_add],
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
/- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m + m' ∈ s₀ }` is also
`U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
let `s₁` be the intersection `s₀ ∩ { m | a₀ + m ∈ s₀ }`. By choice of `a₀`, this is again `U`-large,
so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc. This gives the desired
infinite sequence. -/
  have exists_elem : ∀ {s : set M} (hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m + m' ∈ s }).nonempty :=
    λ s hs, ultrafilter.nonempty_of_mem (inter_mem hs $ by { rw ←U_idem at hs, exact hs }),
  let elem : { s // s ∈ U } → M := λ p, (exists_elem p.property).some,
  let succ : { s // s ∈ U } → { s // s ∈ U } := λ p, ⟨p.val ∩ { m | elem p + m ∈ p.val },
    inter_mem p.2 $ show _, from set.inter_subset_right _ _ (exists_elem p.2).some_mem⟩,
  use stream.corec elem succ (subtype.mk s₀ sU),
  suffices : ∀ (a : stream M) (m ∈ FS a), ∀ p, a = stream.corec elem succ p → m ∈ p.val,
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
    rw [stream.corec_eq, stream.tail_cons], },
end

/-- The strong form of **Hindman's theorem**: in any finite cover of an FS-set, one the parts
contains an FS-set. -/
lemma FS_partition_regular {M} [add_semigroup M] (a : stream M) (s : set (set M)) (sfin : s.finite)
  (scov : FS a ⊆ ⋃₀ s) : ∃ (c ∈ s) (b : stream M), FS b ⊆ c :=
let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FS a in
let ⟨c, cs, hc⟩ := (ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov) in
⟨c, cs, exists_FS_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FS-set. -/
lemma exists_FS_of_finite_cover {M} [add_semigroup M] [nonempty M] (s : set (set M))
  (sfin : s.finite) (scov : ⊤ ⊆ ⋃₀ s) : ∃ (c ∈ s) (a : stream M), FS a ⊆ c :=
let ⟨U, hU⟩ := exists_idempotent_of_compact_t2_of_continuous_add_left
  (@ultrafilter.continuous_add_left M _) in
let ⟨c, c_s, hc⟩ := (ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov) in
⟨c, c_s, exists_FS_of_large U hU c hc⟩
