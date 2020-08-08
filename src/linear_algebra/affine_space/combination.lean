/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import linear_algebra.affine_space.basic
import linear_algebra.finsupp

noncomputable theory
open_locale big_operators
open_locale classical

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weighted_vsub_of_point` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weighted_vsub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affine_combination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `finset`; versions for a
`fintype` may be obtained using `finset.univ`, while versions for a
`finsupp` may be obtained using `finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

open add_action add_torsor affine_space

namespace finset

variables {k : Type*} (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [S : affine_space k V P]
include S

variables {ι : Type*} (s : finset ι)

/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weighted_vsub_of_point (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
∑ i in s, (linear_map.proj i : (ι → k) →ₗ[k] k).smul_right (p i -ᵥ b)

@[simp] lemma weighted_vsub_of_point_apply (w : ι → k) (p : ι → P) (b : P) :
  s.weighted_vsub_of_point V p b w = ∑ i in s, w i • (p i -ᵥ b) :=
by simp [weighted_vsub_of_point, linear_map.sum_apply]

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
lemma weighted_vsub_of_point_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 0)
    (b₁ b₂ : P) : s.weighted_vsub_of_point V p b₁ w = s.weighted_vsub_of_point V p b₂ w :=
begin
  apply eq_of_sub_eq_zero,
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←sum_smul, h, zero_smul]
end

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
lemma weighted_vsub_of_point_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 1)
    (b₁ b₂ : P) :
  s.weighted_vsub_of_point V p b₁ w +ᵥ b₁ = s.weighted_vsub_of_point V p b₂ w +ᵥ b₂ :=
begin
  erw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←vsub_eq_zero_iff_eq V,
       vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ←add_sub_assoc, add_comm, add_sub_assoc,
       ←sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]
end

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp] lemma weighted_vsub_of_point_erase (w : ι → k) (p : ι → P) (i : ι) :
  (s.erase i).weighted_vsub_of_point V p (p i) w = s.weighted_vsub_of_point V p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply sum_erase,
  rw [vsub_self, smul_zero]
end

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp] lemma weighted_vsub_of_point_insert (w : ι → k) (p : ι → P) (i : ι) :
  (insert i s).weighted_vsub_of_point V p (p i) w = s.weighted_vsub_of_point V p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply sum_insert_zero,
  rw [vsub_self, smul_zero]
end

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma weighted_vsub_of_point_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : finset ι}
    (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub_of_point V p b w = s₂.weighted_vsub_of_point V p b (set.indicator ↑s₁ w) :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  exact set.sum_indicator_subset_of_eq_zero w (λ i wi, wi • (p i -ᵥ b : V)) h (λ i, zero_smul k _)
end

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weighted_vsub (p : ι → P) : (ι → k) →ₗ[k] V :=
s.weighted_vsub_of_point V p (classical.choice S.nonempty)

/-- Applying `weighted_vsub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weighted_vsub` would involve selecting a preferred base point with
`weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero` and then
using `weighted_vsub_of_point_apply`. -/
lemma weighted_vsub_apply (w : ι → k) (p : ι → P) :
  s.weighted_vsub V p w = ∑ i in s, w i • (p i -ᵥ (classical.choice S.nonempty)) :=
by simp [weighted_vsub, linear_map.sum_apply]

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
lemma weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 0) (b : P) : s.weighted_vsub V p w = s.weighted_vsub_of_point V p b w :=
s.weighted_vsub_of_point_eq_of_sum_eq_zero V w p h _ _

/-- The `weighted_vsub` for an empty set is 0. -/
@[simp] lemma weighted_vsub_empty (w : ι → k) (p : ι → P) :
  (∅ : finset ι).weighted_vsub V p w = 0 :=
by simp [weighted_vsub_apply]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma weighted_vsub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : finset ι} (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub V p w = s₂.weighted_vsub V p (set.indicator ↑s₁ w) :=
weighted_vsub_of_point_indicator_subset _ _ _ _ h

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point.  This is intended to
be used when the sum of the weights is 1, in which case it is an
affine combination (barycenter) of the points with the given weights;
that condition is specified as a hypothesis on those lemmas that
require it. -/
def affine_combination (w : ι → k) (p : ι → P) : P :=
s.weighted_vsub_of_point V p (classical.choice S.nonempty) w +ᵥ (classical.choice S.nonempty)

/-- Applying `affine_combination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affine_combination` would involve selecting a preferred base
point with
`affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one` and
then using `weighted_vsub_of_point_apply`. -/
lemma affine_combination_apply (w : ι → k) (p : ι → P) :
  s.affine_combination V w p =
    s.weighted_vsub_of_point V p (classical.choice S.nonempty) w +ᵥ (classical.choice S.nonempty) :=
rfl

/-- `affine_combination` gives the sum with any base point, when the
sum of the weights is 1. -/
lemma affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 1) (b : P) :
  s.affine_combination V w p = s.weighted_vsub_of_point V p b w +ᵥ b :=
s.weighted_vsub_of_point_vadd_eq_of_sum_eq_one V w p h _ _

/-- Adding a `weighted_vsub` to an `affine_combination`. -/
lemma weighted_vsub_vadd_affine_combination (w₁ w₂ : ι → k) (p : ι → P) :
  s.weighted_vsub V p w₁ +ᵥ s.affine_combination V w₂ p = s.affine_combination V (w₁ + w₂) p :=
begin
  erw vadd_assoc,
  congr,
  exact (linear_map.map_add _ _ _).symm
end

/-- Subtracting two `affine_combination`s. -/
lemma affine_combination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
  s.affine_combination V w₁ p -ᵥ s.affine_combination V w₂ p = s.weighted_vsub V p (w₁ - w₂) :=
begin
  erw vadd_vsub_vadd_cancel_right,
  exact (linear_map.map_sub _ _ _).symm
end

/-- An `affine_combination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
@[simp] lemma affine_combination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι}
    (his : i ∈ s) (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) :
  s.affine_combination V w p = p i :=
begin
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 (λ h, false.elim (h his)),
  rw [s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one V w p h1 (p i),
      weighted_vsub_of_point_apply],
  convert zero_vadd V (p i),
  convert sum_eq_zero _,
  intros i2 hi2,
  by_cases h : i2 = i,
  { simp [h] },
  { simp [hw0 i2 hi2 h] }
end

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma affine_combination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : finset ι}
    (h : s₁ ⊆ s₂) :
  s₁.affine_combination V w p = s₂.affine_combination V (set.indicator ↑s₁ w) p :=
by rw [affine_combination_apply, affine_combination_apply,
       weighted_vsub_of_point_indicator_subset _ _ _ _ h]

variables {V}

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weighted_vsub_of_point` using a `finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weighted_vsub_of_point` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
lemma eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype {v : V} {x : k}
    {s : set ι} {p : ι → P} {b : P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = x),
    v = fs.weighted_vsub_of_point V p b w) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = x),
    v = fs.weighted_vsub_of_point V (λ (i : s), p i) b w :=
begin
  simp_rw weighted_vsub_of_point_apply,
  split,
  { rintros ⟨fs, hfs, w, rfl, rfl⟩,
    use [fs.subtype s, λ i, w i, sum_subtype_of_mem _ hfs, (sum_subtype_of_mem _ hfs).symm] },
  { rintros ⟨fs, w, rfl, rfl⟩,
    refine ⟨fs.map (function.embedding.subtype _), map_subtype_subset _,
         λ i, if h : i ∈ s then w ⟨i, h⟩ else 0, _, _⟩;
      simp }
end

variables (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weighted_vsub` using
a `finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weighted_vsub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
lemma eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype {v : V} {s : set ι} {p : ι → P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = 0),
    v = fs.weighted_vsub V p w) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = 0),
    v = fs.weighted_vsub V (λ (i : s), p i) w :=
eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype

variables (V)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affine_combination` using a `finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affine_combination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
lemma eq_affine_combination_subset_iff_eq_affine_combination_subtype {p0 : P} {s : set ι}
    {p : ι → P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = 1),
    p0 = fs.affine_combination V w p) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = 1),
    p0 = fs.affine_combination V w (λ (i : s), p i) :=
begin
  simp_rw [affine_combination_apply, eq_vadd_iff_vsub_eq],
  exact eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
end

end finset

namespace affine_space

variables {k : Type*} (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]
variables {ι : Type*}

/-- A `weighted_vsub` with sum of weights 0 is in the `vector_span` of
an indexed family. -/
lemma weighted_vsub_mem_vector_span {s : finset ι} {w : ι → k}
    (h : ∑ i in s, w i = 0) (p : ι → P) :
    s.weighted_vsub V p w ∈ vector_span k V (set.range p) :=
begin
  by_cases hn : nonempty ι,
  { cases hn with i0,
    rw [vector_span_range_eq_span_range_vsub_right k V p i0, ←set.image_univ,
        finsupp.mem_span_iff_total,
        finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero V s w p h (p i0),
        finset.weighted_vsub_of_point_apply],
    let w' := set.indicator ↑s w,
    have hwx : ∀ i, w' i ≠ 0 → i ∈ s := λ i, set.mem_of_indicator_ne_zero,
    use [finsupp.on_finset s w' hwx, set.subset_univ _],
    rw [finsupp.total_apply, finsupp.on_finset_sum hwx],
    { apply finset.sum_congr rfl,
      intros i hi,
      simp [w', set.indicator_apply, if_pos hi] },
    { exact λ _, zero_smul k _ } },
  { simp [finset.eq_empty_of_not_nonempty hn s] }
end

/-- An `affine_combination` with sum of weights 1 is in the
`affine_span` of an indexed family, if the underlying ring is
nontrivial. -/
lemma affine_combination_mem_affine_span [nontrivial k] {s : finset ι} {w : ι → k}
    (h : ∑ i in s, w i = 1) (p : ι → P) :
  s.affine_combination V w p ∈ affine_span k V (set.range p) :=
begin
  have hnz : ∑ i in s, w i ≠ 0 := h.symm ▸ one_ne_zero,
  have hn : s.nonempty := finset.nonempty_of_sum_ne_zero hnz,
  cases hn with i1 hi1,
  let w1 : ι → k := function.update (function.const ι 0) i1 1,
  have hw1 : ∑ i in s, w1 i = 1,
  { rw [finset.sum_update_of_mem hi1, finset.sum_const_zero, add_zero] },
  have hw1s : s.affine_combination V w1 p = p i1 :=
    s.affine_combination_of_eq_one_of_eq_zero V w1 p hi1 (function.update_same _ _ _)
                                              (λ _ _ hne, function.update_noteq hne _ _),
  have hv : s.affine_combination V w p -ᵥ p i1 ∈ (affine_span k V (set.range p)).direction,
  { rw [direction_affine_span, ←hw1s, finset.affine_combination_vsub],
    apply weighted_vsub_mem_vector_span,
    simp [pi.sub_apply, h, hw1] },
  rw ←vsub_vadd V (s.affine_combination V w p) (p i1),
  exact affine_subspace.vadd_mem_of_mem_direction hv (mem_affine_span k V (set.mem_range_self _))
end

variables (k) {V}

/-- A vector is in the `vector_span` of an indexed family if and only
if it is a `weighted_vsub` with sum of weights 0. -/
lemma mem_vector_span_iff_eq_weighted_vsub {v : V} {p : ι → P} :
  v ∈ vector_span k V (set.range p) ↔
    ∃ (s : finset ι) (w : ι → k) (h : ∑ i in s, w i = 0), v = s.weighted_vsub V p w :=
begin
  split,
  { by_cases hn : nonempty ι,
    { cases hn with i0,
      rw [vector_span_range_eq_span_range_vsub_right k V p i0, ←set.image_univ,
          finsupp.mem_span_iff_total],
      rintros ⟨l, hl, hv⟩,
      use insert i0 l.support,
      set w := (l : ι → k) -
        function.update (function.const ι 0 : ι → k) i0 (∑ i in l.support, l i) with hwdef,
      use w,
      have hw : ∑ i in insert i0 l.support, w i = 0,
      { rw hwdef,
        simp_rw [pi.sub_apply, finset.sum_sub_distrib,
                 finset.sum_update_of_mem (finset.mem_insert_self _ _), finset.sum_const_zero,
                 finset.sum_insert_of_eq_zero_if_not_mem finsupp.not_mem_support_iff.1,
                 add_zero, sub_self] },
      use hw,
      have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self V (p i0)).symm ▸ smul_zero _,
      change (λ i, w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz,
      rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero V _ w p hw (p i0),
          finset.weighted_vsub_of_point_apply, ←hv, finsupp.total_apply,
          finset.sum_insert_zero hz],
      change ∑ i in l.support, l i • _ = _,
      congr,
      ext i,
      by_cases h : i = i0,
      { simp [h] },
      { simp [hwdef, h] } },
    { rw [set.range_eq_empty.2 hn, vector_span_empty, submodule.mem_bot],
      intro hv,
      use [∅],
      simp [hv] } },
  { rintros ⟨s, w, hw, rfl⟩,
    exact weighted_vsub_mem_vector_span V hw p }
end

variables {k}

/-- A point in the `affine_span` of an indexed family is an
`affine_combination` with sum of weights 1. -/
lemma eq_affine_combination_of_mem_affine_span {p1 : P} {p : ι → P}
    (h : p1 ∈ affine_span k V (set.range p)) :
  ∃ (s : finset ι) (w : ι → k) (hw : ∑ i in s, w i = 1), p1 = s.affine_combination V w p :=
begin
  have hn : ((affine_span k V (set.range p)) : set P).nonempty := ⟨p1, h⟩,
  rw [affine_span_nonempty, set.range_nonempty_iff_nonempty] at hn,
  cases hn with i0,
  have h0 : p i0 ∈ affine_span k V (set.range p) := mem_affine_span k V (set.mem_range_self i0),
  have hd : p1 -ᵥ p i0 ∈ (affine_span k V (set.range p)).direction :=
    affine_subspace.vsub_mem_direction h h0,
  rw [direction_affine_span, mem_vector_span_iff_eq_weighted_vsub] at hd,
  rcases hd with ⟨s, w, h, hs⟩,
  let s' := insert i0 s,
  let w' := set.indicator ↑s w,
  have h' : ∑ i in s', w' i = 0,
  { rw [←h, set.sum_indicator_subset _ (finset.subset_insert i0 s)] },
  have hs' : s'.weighted_vsub V p w' = p1 -ᵥ p i0,
  { rw hs,
    exact (finset.weighted_vsub_indicator_subset _ _ _ (finset.subset_insert i0 s)).symm },
  let w0 : ι → k := function.update (function.const ι 0) i0 1,
  have hw0 : ∑ i in s', w0 i = 1,
  { rw [finset.sum_update_of_mem (finset.mem_insert_self _ _), finset.sum_const_zero, add_zero] },
  have hw0s : s'.affine_combination V w0 p = p i0 :=
    s'.affine_combination_of_eq_one_of_eq_zero V w0 p
                                               (finset.mem_insert_self _ _)
                                               (function.update_same _ _ _)
                                               (λ _ _ hne, function.update_noteq hne _ _),
  use [s', w0 + w'],
  split,
  { simp [pi.add_apply, finset.sum_add_distrib, hw0, h'] },
  { rw [add_comm, ←finset.weighted_vsub_vadd_affine_combination, hw0s, hs', vsub_vadd] }
end

variables (k V)

/-- A point is in the `affine_span` of an indexed family if and only
if it is an `affine_combination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
lemma mem_affine_span_iff_eq_affine_combination [nontrivial k] {p1 : P} {p : ι → P} :
  p1 ∈ affine_span k V (set.range p) ↔
    ∃ (s : finset ι) (w : ι → k) (hw : ∑ i in s, w i = 1), p1 = s.affine_combination V w p :=
begin
  split,
  { exact eq_affine_combination_of_mem_affine_span },
  { rintros ⟨s, w, hw, rfl⟩,
    exact affine_combination_mem_affine_span V hw p }
end

end affine_space

namespace affine_map
variables {k : Type*} (V : Type*) (P : Type*) [comm_ring k] [add_comm_group V] [module k V]
variables [affine_space k V P] {ι : Type*} (s : finset ι)

-- TODO: define `affine_map.proj`, `affine_map.fst`, `affine_map.snd`
/-- A weighted sum, as an affine map on the points involved. -/
def weighted_vsub_of_point (w : ι → k) : affine_map k ((ι → V) × V) ((ι → P) × P) V V :=
{ to_fun := λ p, s.weighted_vsub_of_point _ p.fst p.snd w,
  linear := ∑ i in s,
    w i • ((linear_map.proj i).comp (linear_map.fst _ _ _) - linear_map.snd _ _ _),
  map_vadd' := begin
    rintros ⟨p, b⟩ ⟨v, b'⟩,
    simp [linear_map.sum_apply, finset.weighted_vsub_of_point, vsub_vadd_eq_vsub_sub,
          vadd_vsub_assoc, add_sub, ← sub_add_eq_add_sub, smul_add, finset.sum_add_distrib]
  end }

end affine_map
