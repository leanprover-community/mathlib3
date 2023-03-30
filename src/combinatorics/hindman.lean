/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import topology.stone_cech
import topology.algebra.semigroup
import data.stream.init

/-!
# Hindman's theorem on finite sums

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive "Addition of ultrafilters given by
`∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`." ]
def ultrafilter.has_mul {M} [has_mul M] : has_mul (ultrafilter M) :=
{ mul := λ U V, (*) <$> U <*> V }

local attribute [instance] ultrafilter.has_mul ultrafilter.has_add

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
lemma ultrafilter.eventually_mul {M} [has_mul M] (U V : ultrafilter M) (p : M → Prop) :
  (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') := iff.rfl

/-- Semigroup structure on `ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive "Additive semigroup structure on `ultrafilter M` induced by an additive semigroup
structure on `M`."]
def ultrafilter.semigroup {M} [semigroup M] : semigroup (ultrafilter M) :=
{ mul_assoc := λ U V W, ultrafilter.coe_inj.mp $ filter.ext' $ λ p,
    by simp only [ultrafilter.eventually_mul, mul_assoc]
  ..ultrafilter.has_mul }

local attribute [instance] ultrafilter.semigroup ultrafilter.add_semigroup

/- We don't prove `continuous_mul_right`, because in general it is false! -/
@[to_additive]
lemma ultrafilter.continuous_mul_left {M} [semigroup M] (V : ultrafilter M) : continuous (* V) :=
topological_space.is_topological_basis.continuous ultrafilter_basis_is_basis _ $
set.forall_range_iff.mpr $ λ s, ultrafilter_is_open_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }

namespace hindman

/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
inductive FS {M} [add_semigroup M] : stream M → set M
| head (a : stream M) : FS a a.head
| tail (a : stream M) (m : M) (h : FS a.tail m) : FS a m
| cons (a : stream M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
inductive FP {M} [semigroup M] : stream M → set M
| head (a : stream M) : FP a a.head
| tail (a : stream M) (m : M) (h : FP a.tail m) : FP a m
| cons (a : stream M) (m : M) (h : FP a.tail m) : FP a (a.head * m)

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive "If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
is obtained from a subsequence of `M` starting sufficiently late."]
lemma FP.mul {M} [semigroup M] {a : stream M} {m : M} (hm : m ∈ FP a) :
  ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a :=
begin
  induction hm with a a m hm ih a m hm ih,
  { exact ⟨1, λ m hm, FP.cons a m hm⟩, },
  { cases ih with n hn, use n+1, intros m' hm', exact FP.tail _ _ (hn _ hm'), },
  { cases ih with n hn, use n+1, intros m' hm', rw mul_assoc, exact FP.cons _ _ (hn _ hm'), },
end

@[to_additive exists_idempotent_ultrafilter_le_FS]
lemma exists_idempotent_ultrafilter_le_FP {M} [semigroup M] (a : stream M) :
  ∃ U : ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a :=
begin
  let S : set (ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FP (a.drop n) },
  obtain ⟨U, hU, U_idem⟩ := exists_idempotent_in_compact_subsemigroup _ S _ _ _,
  { refine ⟨U, U_idem, _⟩, convert set.mem_Inter.mp hU 0, },
  { exact ultrafilter.continuous_mul_left },
  { apply is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed,
    { intros n U hU,
      apply eventually.mono hU,
      rw [add_comm, ←stream.drop_drop, ←stream.tail_eq_drop],
      exact FP.tail _ },
    { intro n, exact ⟨pure _, mem_pure.mpr $ FP.head _⟩, },
    { exact (ultrafilter_is_closed_basic _).is_compact, },
    { intro n, apply ultrafilter_is_closed_basic, }, },
  { exact is_closed.is_compact (is_closed_Inter $ λ i, ultrafilter_is_closed_basic _) },
  { intros U hU V hV,
    rw set.mem_Inter at *,
    intro n,
    rw [set.mem_set_of_eq, ultrafilter.eventually_mul],
    apply eventually.mono (hU n),
    intros m hm,
    obtain ⟨n', hn⟩ := FP.mul hm,
    apply eventually.mono (hV (n' + n)),
    intros m' hm',
    apply hn,
    simpa only [stream.drop_drop] using hm', }
end

@[to_additive exists_FS_of_large]
lemma exists_FP_of_large {M} [semigroup M] (U : ultrafilter M) (U_idem : U * U = U)
  (s₀ : set M) (sU : s₀ ∈ U) : ∃ a, FP a ⊆ s₀ :=
begin
/- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
`U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again `U`-large,
so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc. This gives the desired
infinite sequence. -/
  have exists_elem : ∀ {s : set M} (hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m * m' ∈ s }).nonempty :=
    λ s hs, ultrafilter.nonempty_of_mem (inter_mem hs $ by { rw ←U_idem at hs, exact hs }),
  let elem : { s // s ∈ U } → M := λ p, (exists_elem p.property).some,
  let succ : { s // s ∈ U } → { s // s ∈ U } := λ p, ⟨p.val ∩ { m | elem p * m ∈ p.val },
    inter_mem p.2 $ show _, from set.inter_subset_right _ _ (exists_elem p.2).some_mem⟩,
  use stream.corec elem succ (subtype.mk s₀ sU),
  suffices : ∀ (a : stream M) (m ∈ FP a), ∀ p, a = stream.corec elem succ p → m ∈ p.val,
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

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular "The strong form of **Hindman's theorem**: in any finite cover of
an FS-set, one the parts contains an FS-set."]
lemma FP_partition_regular {M} [semigroup M] (a : stream M) (s : set (set M)) (sfin : s.finite)
  (scov : FP a ⊆ ⋃₀ s) : ∃ (c ∈ s) (b : stream M), FP b ⊆ c :=
let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a in
let ⟨c, cs, hc⟩ := (ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov) in
⟨c, cs, exists_FP_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover "The weak form of **Hindman's theorem**: in any finite cover
of a nonempty additive semigroup, one of the parts contains an FS-set."]
lemma exists_FP_of_finite_cover {M} [semigroup M] [nonempty M] (s : set (set M))
  (sfin : s.finite) (scov : ⊤ ⊆ ⋃₀ s) : ∃ (c ∈ s) (a : stream M), FP a ⊆ c :=
let ⟨U, hU⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left
  (@ultrafilter.continuous_mul_left M _) in
let ⟨c, c_s, hc⟩ := (ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov) in
⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]
lemma FP_drop_subset_FP {M} [semigroup M] (a : stream M) (n : ℕ) :
  FP (a.drop n) ⊆ FP a :=
begin
  induction n with n ih, { refl },
  rw [nat.succ_eq_one_add, ←stream.drop_drop],
  exact trans (FP.tail _) ih,
end

@[to_additive]
lemma FP.singleton {M} [semigroup M] (a : stream M) (i : ℕ) : a.nth i ∈ FP a :=
by { induction i with i ih generalizing a, { apply FP.head }, { apply FP.tail, apply ih } }

@[to_additive]
lemma FP.mul_two {M} [semigroup M] (a : stream M) (i j : ℕ) (ij : i < j) :
  a.nth i * a.nth j ∈ FP a :=
begin
  refine FP_drop_subset_FP _ i _,
  rw ←stream.head_drop,
  apply FP.cons,
  rcases le_iff_exists_add.mp (nat.succ_le_of_lt ij) with ⟨d, hd⟩,
  have := FP.singleton (a.drop i).tail d,
  rw [stream.tail_eq_drop, stream.nth_drop, stream.nth_drop] at this,
  convert this,
  rw [hd, add_comm, nat.succ_add, nat.add_succ],
end

@[to_additive]
lemma FP.finset_prod {M} [comm_monoid M] (a : stream M) (s : finset ℕ) (hs : s.nonempty) :
  s.prod (λ i, a.nth i) ∈ FP a :=
begin
  refine FP_drop_subset_FP _ (s.min' hs) _,
  induction s using finset.strong_induction with s ih,
  rw [←finset.mul_prod_erase _ _ (s.min'_mem hs), ←stream.head_drop],
  cases (s.erase (s.min' hs)).eq_empty_or_nonempty with h h,
  { rw [h, finset.prod_empty, mul_one], exact FP.head _ },
  { apply FP.cons, rw [stream.tail_eq_drop, stream.drop_drop, add_comm],
    refine set.mem_of_subset_of_mem _ (ih _ (finset.erase_ssubset $ s.min'_mem hs) h),
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      nat.succ_le_of_lt (finset.min'_lt_of_mem_erase_min' _ _ $ finset.min'_mem _ _),
    cases le_iff_exists_add.mp this with d hd,
    rw [hd, add_comm, ←stream.drop_drop],
    apply FP_drop_subset_FP }
end

end hindman
