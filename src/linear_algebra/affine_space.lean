/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
import data.indicator_function
import linear_algebra.basis

noncomputable theory
open_locale big_operators
open_locale classical

/-!
# Affine spaces

This file defines affine spaces (over modules) and subspaces, affine
maps, affine combinations of points, and the affine span of a set of
points.

## Implementation notes

This file is very minimal and many things are surely omitted. Most
results can be deduced from corresponding results for modules or
vector spaces.  The variables `k` and `V` are explicit rather than
implicit arguments to lemmas because otherwise the elaborator
sometimes has problems inferring appropriate types and type class
instances.  Definitions of affine spaces vary as to whether a space
with no points is permitted; here, we require a nonempty type of
points (via the definition of torsors requiring a nonempty type).

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space

-/

open add_action
open add_torsor

/-- `affine_space` is an abbreviation for `add_torsor` in the case
where the group is a vector space, or more generally a module, but we
omit the type classes `[ring k]` and `[module k V]` in the type
synonym itself to simplify type class search.. -/
@[nolint unused_arguments]
abbreviation affine_space (k : Type*) (V : Type*) (P : Type*) [add_comm_group V] :=
add_torsor V P

namespace affine_space

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space k V P]

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (s : set P) : submodule k V := submodule.span k (vsub_set V s)

/-- The definition of `vector_span`, for rewriting. -/
lemma vector_span_def (s : set P) : vector_span k V s = submodule.span k (vsub_set V s) :=
rfl

variables (P)

/-- The `vector_span` of the empty set is `⊥`. -/
@[simp] lemma vector_span_empty : vector_span k V (∅ : set P) = ⊥ :=
by rw [vector_span_def, vsub_set_empty, submodule.span_empty]

variables {P}

/-- The `vsub_set` lies within the `vector_span`. -/
lemma vsub_set_subset_vector_span (s : set P) : vsub_set V s ⊆ vector_span k V s :=
submodule.subset_span

/-- Each pairwise difference is in the `vector_span`. -/
lemma vsub_mem_vector_span {s : set P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  p1 -ᵥ p2 ∈ vector_span k V s :=
begin
  rw ←submodule.mem_coe,
  exact set.mem_of_mem_of_subset (vsub_mem_vsub_set V hp1 hp2)
                                 (vsub_set_subset_vector_span k V s)
end

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k V P`. -/
def span_points (s : set P) : set P :=
{p | ∃ p1 ∈ s, ∃ v ∈ (vector_span k V s), p = v +ᵥ p1}

/-- A point in a set is in its affine span. -/
lemma mem_span_points (p : P) (s : set P) : p ∈ s → p ∈ span_points k V s
| hp := ⟨p, hp, 0, submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- A set is contained in its `span_points`. -/
lemma subset_span_points (s : set P) : s ⊆ span_points k V s :=
λ p, mem_span_points k V p s

/-- The `span_points` of a set is nonempty if and only if that set
is. -/
@[simp] lemma span_points_nonempty (s : set P) :
  (span_points k V s).nonempty ↔ s.nonempty :=
begin
  split,
  { contrapose,
    rw [set.not_nonempty_iff_eq_empty, set.not_nonempty_iff_eq_empty],
    intro h,
    simp [h, span_points] },
  { exact λ ⟨p, hp⟩, ⟨p, mem_span_points k V p s hp⟩ }
end

/-- Adding a point in the affine span and a vector in the spanning
submodule produces a point in the affine span. -/
lemma vadd_mem_span_points_of_mem_span_points_of_mem_vector_span {s : set P} {p : P} {v : V}
    (hp : p ∈ span_points k V s) (hv : v ∈ vector_span k V s) : v +ᵥ p ∈ span_points k V s :=
begin
  rcases hp with ⟨p2, ⟨hp2, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv2p, vadd_assoc],
  use [p2, hp2, v + v2, (vector_span k V s).add_mem hv hv2, rfl]
end

/-- Subtracting two points in the affine span produces a vector in the
spanning submodule. -/
lemma vsub_mem_vector_span_of_mem_span_points_of_mem_span_points {s : set P} {p1 p2 : P}
    (hp1 : p1 ∈ span_points k V s) (hp2 : p2 ∈ span_points k V s) :
  p1 -ᵥ p2 ∈ vector_span k V s :=
begin
  rcases hp1 with ⟨p1a, ⟨hp1a, ⟨v1, ⟨hv1, hv1p⟩⟩⟩⟩,
  rcases hp2 with ⟨p2a, ⟨hp2a, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv1p, hv2p, vsub_vadd_eq_vsub_sub V (v1 +ᵥ p1a), vadd_vsub_assoc, add_comm, add_sub_assoc],
  have hv1v2 : v1 - v2 ∈ vector_span k V s,
  { apply (vector_span k V s).add_mem hv1,
    rw ←neg_one_smul k v2,
    exact (vector_span k V s).smul_mem (-1 : k) hv2 },
  refine (vector_span k V s).add_mem _ hv1v2,
  exact vsub_mem_vector_span k V hp1a hp2a
end

end affine_space

open affine_space

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
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←finset.sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←finset.sum_smul, h, zero_smul]
end

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
lemma weighted_vsub_of_point_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 1)
    (b₁ b₂ : P) :
  s.weighted_vsub_of_point V p b₁ w +ᵥ b₁ = s.weighted_vsub_of_point V p b₂ w +ᵥ b₂ :=
begin
  erw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←vsub_eq_zero_iff_eq V,
       vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ←add_sub_assoc, add_comm, add_sub_assoc,
       ←finset.sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←finset.sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]
end

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp] lemma weighted_vsub_of_point_erase (w : ι → k) (p : ι → P) (i : ι) :
  (s.erase i).weighted_vsub_of_point V p (p i) w = s.weighted_vsub_of_point V p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply finset.sum_erase,
  rw [vsub_self, smul_zero]
end

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp] lemma weighted_vsub_of_point_insert (w : ι → k) (p : ι → P) (i : ι) :
  (insert i s).weighted_vsub_of_point V p (p i) w = s.weighted_vsub_of_point V p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply finset.sum_insert_zero,
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
  have h1 : ∑ i in s, w i = 1 := hwi ▸ finset.sum_eq_single i hw0 (λ h, false.elim (h his)),
  rw [s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one V w p h1 (p i),
      weighted_vsub_of_point_apply],
  convert zero_vadd V (p i),
  convert finset.sum_eq_zero _,
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

end finset

section affine_independent

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space k V P] {ι : Type*}

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def affine_independent (p : ι → P) : Prop :=
∀ (s : finset ι) (w : ι → k), ∑ i in s, w i = 0 → s.weighted_vsub V p w = 0 → ∀ i ∈ s, w i = 0

/-- A family with at most one point is affinely independent. -/
lemma affine_independent_of_subsingleton [subsingleton ι] (p : ι → P) :
  affine_independent k V p :=
λ s w h hs i hi, fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
lemma affine_independent_iff_linear_independent_vsub (p : ι → P) (i1 : ι) :
  affine_independent k V p ↔ linear_independent k (λ i : {x // x ≠ i1}, (p i -ᵥ p i1 : V)) :=
begin
  split,
  { intro h,
    rw linear_independent_iff',
    intros s g hg i hi,
    set f : ι → k := λ x, if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef,
    let s2 : finset ι := insert i1 (s.map (function.embedding.subtype _)),
    have hfg : ∀ x : {x // x ≠ i1}, g x = f x,
    { intro x,
      rw hfdef,
      dsimp only [],
      erw [dif_neg x.property, subtype.coe_eta] },
    rw hfg,
    have hf : ∑ ι in s2, f ι = 0,
    { rw [finset.sum_insert (finset.not_mem_map_subtype_of_not_property s (not_not.2 rfl)),
          finset.sum_subtype_map_embedding (λ x hx, (hfg x).symm)],
      rw hfdef,
      dsimp only [],
      rw dif_pos rfl,
      exact neg_add_self _ },
    have hs2 : s2.weighted_vsub V p f = 0,
    { set f2 : ι → V := λ x, f x • (p x -ᵥ p i1) with hf2def,
      set g2 : {x // x ≠ i1} → V := λ x, g x • (p x -ᵥ p i1) with hg2def,
      have hf2g2 : ∀ x : {x // x ≠ i1}, f2 x = g2 x,
      { simp_rw [hf2def, hg2def, hfg],
        exact λ x, rfl },
      rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero V s2 f p hf (p i1),
          finset.weighted_vsub_of_point_insert, finset.weighted_vsub_of_point_apply,
          finset.sum_subtype_map_embedding (λ x hx, hf2g2 x)],
      exact hg },
    exact h s2 f hf hs2 i (finset.mem_insert_of_mem (finset.mem_map.2 ⟨i, hi, rfl⟩)) },
  { intro h,
    rw linear_independent_iff' at h,
    intros s w hw hs i hi,
    rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero V s w p hw (p i1),
        ←s.weighted_vsub_of_point_erase V w p i1, finset.weighted_vsub_of_point_apply] at hs,
    let f : ι → V := λ i, w i • (p i -ᵥ p i1),
    have hs2 : ∑ i in (s.erase i1).subtype (λ i, i ≠ i1), f i = 0,
    { rw [←hs],
      convert finset.sum_subtype_of_mem f (λ x, finset.ne_of_mem_erase) },
    have h2 := h ((s.erase i1).subtype (λ i, i ≠ i1)) (λ x, w x) hs2,
    simp_rw [finset.mem_subtype] at h2,
    have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 :=
      λ i his hi, h2 ⟨i, hi⟩ (finset.mem_erase_of_ne_of_mem hi his),
    exact finset.eq_zero_of_sum_eq_zero hw h2b i hi }
end

end affine_independent

/-- An `affine_subspace k V P` is a subset of an `affine_space k V P`
that, if not empty, has an affine space structure induced by a
corresponding subspace of the `module k V`. -/
structure affine_subspace (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V]
    [module k V] [affine_space k V P] :=
(carrier : set P)
(smul_vsub_vadd_mem : ∀ (c : k) (p1 p2 p3 ∈ carrier), c • (p1 -ᵥ p2 : V) +ᵥ p3 ∈ carrier)

namespace affine_subspace

variables (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]

instance : has_coe (affine_subspace k V P) (set P) := ⟨carrier⟩
instance : has_mem P (affine_subspace k V P) := ⟨λ p s, p ∈ (s : set P)⟩

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp] lemma mem_coe (p : P) (s : affine_subspace k V P) :
  p ∈ (s : set P) ↔ p ∈ s :=
iff.rfl

variables {k V P}

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.) -/
def direction (s : affine_subspace k V P) : submodule k V := vector_span k V (s : set P)

/-- The direction equals the `vector_span`. -/
lemma direction_eq_vector_span (s : affine_subspace k V P) :
  s.direction = vector_span k V (s : set P) :=
rfl

/-- Alternative definition of the direction when the affine subspace
is nonempty.  This is defined so that the order on submodules (as used
in the definition of `submodule.span`) can be used in the proof of
`coe_direction_eq_vsub_set`, and is not intended to be used beyond
that proof. -/
def direction_of_nonempty {s : affine_subspace k V P} (h : (s : set P).nonempty) :
  submodule k V :=
{ carrier := vsub_set V (s : set P),
  zero_mem' := begin
    cases h with p hp,
    exact (vsub_self V p) ▸ vsub_mem_vsub_set V hp hp
  end,
  add_mem' := begin
    intros a b ha hb,
    rcases ha with ⟨p1, hp1, p2, hp2, ha⟩,
    rcases hb with ⟨p3, hp3, p4, hp4, hb⟩,
    rw [ha, hb, ←vadd_vsub_assoc],
    refine vsub_mem_vsub_set V _ hp4,
    convert s.smul_vsub_vadd_mem 1 p1 p2 p3 hp1 hp2 hp3,
    rw one_smul
  end,
  smul_mem' := begin
    intros c v hv,
    rcases hv with ⟨p1, hp1, p2, hp2, hv⟩,
    rw [hv, ←vadd_vsub V (c • (p1 -ᵥ p2)) p2],
    refine vsub_mem_vsub_set V _ hp2,
    exact s.smul_vsub_vadd_mem c p1 p2 p2 hp1 hp2 hp2
  end }

/-- `direction_of_nonempty` gives the same submodule as
`direction`. -/
lemma direction_of_nonempty_eq_direction {s : affine_subspace k V P} (h : (s : set P).nonempty) :
  direction_of_nonempty h = s.direction :=
le_antisymm (vsub_set_subset_vector_span k V s) (submodule.span_le.2 set.subset.rfl)

/-- The set of vectors in the direction of a nonempty affine subspace
is given by `vsub_set`. -/
lemma coe_direction_eq_vsub_set {s : affine_subspace k V P} (h : (s : set P).nonempty) :
  (s.direction : set V) = vsub_set V (s : set P) :=
direction_of_nonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and
only if it is the subtraction of two vectors in the subspace. -/
lemma mem_direction_iff_eq_vsub {s : affine_subspace k V P} (h : (s : set P).nonempty) (v : V) :
  v ∈ s.direction ↔ ∃ p1 ∈ s, ∃ p2 ∈ s, v = p1 -ᵥ p2 :=
begin
  rw [←submodule.mem_coe, coe_direction_eq_vsub_set h],
  exact iff.rfl
end

/-- Adding a vector in the direction to a point in the subspace
produces a point in the subspace. -/
lemma vadd_mem_of_mem_direction {s : affine_subspace k V P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s :=
begin
  rw mem_direction_iff_eq_vsub ⟨p, hp⟩ at hv,
  rcases hv with ⟨p1, hp1, p2, hp2, hv⟩,
  rw hv,
  convert s.smul_vsub_vadd_mem 1 p1 p2 p hp1 hp2 hp,
  rw one_smul
end

/-- Subtracting two points in the subspace produces a vector in the
direction. -/
lemma vsub_mem_direction {s : affine_subspace k V P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  (p1 -ᵥ p2) ∈ s.direction :=
vsub_mem_vector_span k V hp1 hp2

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
right. -/
lemma coe_direction_eq_vsub_set_right {s : affine_subspace k V P} {p : P} (hp : p ∈ s) :
  (s.direction : set V) = {v | ∃ p2 ∈ s, v = p2 -ᵥ p} :=
begin
  rw coe_direction_eq_vsub_set ⟨p, hp⟩,
  refine le_antisymm _ _,
  { rintros v ⟨p1, hp1, p2, hp2, hv⟩,
    exact ⟨v +ᵥ p,
           vadd_mem_of_mem_direction (hv.symm ▸ vsub_mem_direction hp1 hp2) hp,
           (vadd_vsub _ _ _).symm⟩ },
  { rintros v ⟨p2, hp2, hv⟩,
    exact ⟨p2, hp2, p, hp, hv⟩ }
end

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
left. -/
lemma coe_direction_eq_vsub_set_left {s : affine_subspace k V P} {p : P} (hp : p ∈ s) :
  (s.direction : set V) = {v | ∃ p2 ∈ s, v = p -ᵥ p2} :=
begin
  ext v,
  rw [submodule.mem_coe, ←submodule.neg_mem_iff, ←submodule.mem_coe,
      coe_direction_eq_vsub_set_right hp, set.mem_set_of_eq, set.mem_set_of_eq],
  conv_lhs { congr, funext, rw [←neg_vsub_eq_vsub_rev, neg_inj] }
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the right. -/
lemma mem_direction_iff_eq_vsub_right {s : affine_subspace k V P} {p : P} (hp : p ∈ s) (v : V) :
  v ∈ s.direction ↔ ∃ p2 ∈ s, v = p2 -ᵥ p :=
begin
  rw [←submodule.mem_coe, coe_direction_eq_vsub_set_right hp],
  exact iff.rfl
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the left. -/
lemma mem_direction_iff_eq_vsub_left {s : affine_subspace k V P} {p : P} (hp : p ∈ s) (v : V) :
  v ∈ s.direction ↔ ∃ p2 ∈ s, v = p -ᵥ p2 :=
begin
  rw [←submodule.mem_coe, coe_direction_eq_vsub_set_left hp],
  exact iff.rfl
end

/-- Given a point in an affine subspace, a result of subtracting that
point on the right is in the direction if and only if the other point
is in the subspace. -/
lemma vsub_right_mem_direction_iff_mem {s : affine_subspace k V P} {p : P} (hp : p ∈ s) (p2 : P) :
  p2 -ᵥ p ∈ s.direction ↔ p2 ∈ s :=
begin
  rw mem_direction_iff_eq_vsub_right hp,
  simp
end

/-- Given a point in an affine subspace, a result of subtracting that
point on the left is in the direction if and only if the other point
is in the subspace. -/
lemma vsub_left_mem_direction_iff_mem {s : affine_subspace k V P} {p : P} (hp : p ∈ s) (p2 : P) :
  p -ᵥ p2 ∈ s.direction ↔ p2 ∈ s :=
begin
  rw mem_direction_iff_eq_vsub_left hp,
  simp
end

/-- Two affine subspaces are equal if they have the same points. -/
@[ext] lemma ext {s1 s2 : affine_subspace k V P} (h : (s1 : set P) = s2) : s1 = s2 :=
begin
  cases s1,
  cases s2,
  congr,
  exact h
end

/-- Two affine subspaces with the same direction and nonempty
intersection are equal. -/
lemma ext_of_direction_eq {s1 s2 : affine_subspace k V P} (hd : s1.direction = s2.direction)
    (hn : ((s1 : set P) ∩ s2).nonempty) : s1 = s2 :=
begin
  ext p,
  have hq1 := set.mem_of_mem_inter_left hn.some_mem,
  have hq2 := set.mem_of_mem_inter_right hn.some_mem,
  split,
  { intro hp,
    rw ←vsub_vadd V p hn.some,
    refine vadd_mem_of_mem_direction _ hq2,
    rw ←hd,
    exact vsub_mem_direction hp hq1 },
  { intro hp,
    rw ←vsub_vadd V p hn.some,
    refine vadd_mem_of_mem_direction _ hq1,
    rw hd,
    exact vsub_mem_direction hp hq2 }
end

/-- Construct an affine subspace from a point and a direction. -/
def mk' (p : P) (direction : submodule k V) : affine_subspace k V P :=
{ carrier := {q | ∃ v ∈ direction, q = v +ᵥ p},
  smul_vsub_vadd_mem := λ c p1 p2 p3 hp1 hp2 hp3, begin
    rcases hp1 with ⟨v1, hv1, hp1⟩,
    rcases hp2 with ⟨v2, hv2, hp2⟩,
    rcases hp3 with ⟨v3, hv3, hp3⟩,
    use [c • (v1 - v2) + v3,
         direction.add_mem (direction.smul_mem c (direction.sub_mem hv1 hv2)) hv3],
    simp [hp1, hp2, hp3, vadd_assoc]
  end }

/-- An affine space constructed from a point and a direction contains
that point. -/
lemma self_mem_mk' (p : P) (direction : submodule k V) :
  p ∈ mk' p direction :=
⟨0, ⟨direction.zero_mem, (add_action.zero_vadd _ _).symm⟩⟩

/-- An affine space constructed from a point and a direction contains
the result of adding a vector in that direction to that point. -/
lemma vadd_mem_mk' {v : V} (p : P) {direction : submodule k V} (hv : v ∈ direction) :
  v +ᵥ p ∈ mk' p direction :=
⟨v, hv, rfl⟩

/-- An affine space constructed from a point and a direction is
nonempty. -/
lemma mk'_nonempty (p : P) (direction : submodule k V) : (mk' p direction : set P).nonempty :=
⟨p, self_mem_mk' p direction⟩

/-- The direction of an affine space constructed from a point and a
direction. -/
@[simp] lemma direction_mk' (p : P) (direction : submodule k V) :
  (mk' p direction).direction = direction :=
begin
  ext v,
  rw mem_direction_iff_eq_vsub (mk'_nonempty _ _),
  split,
  { rintros ⟨p1, ⟨v1, hv1, hp1⟩, p2, ⟨v2, hv2, hp2⟩, hv⟩,
    rw [hv, hp1, hp2, vadd_vsub_vadd_cancel_right],
    exact direction.sub_mem  hv1 hv2 },
  { exact λ hv, ⟨v +ᵥ p, vadd_mem_mk' _ hv, p,
                 self_mem_mk' _ _, (vadd_vsub _ _ _).symm⟩ }
end

/-- Constructing an affine subspace from a point in a subspace and
that subspace's direction yields the original subspace. -/
@[simp] lemma mk'_eq {s : affine_subspace k V P} {p : P} (hp : p ∈ s) : mk' p s.direction = s :=
ext_of_direction_eq (direction_mk' p s.direction)
                    ⟨p, set.mem_inter (self_mem_mk' _ _) hp⟩

/-- If an affine subspace contains a set of points, it contains the
`span_points` of that set. -/
lemma span_points_subset_coe_of_subset_coe {s : set P} {s1 : affine_subspace k V P} (h : s ⊆ s1) :
  span_points k V s ⊆ s1 :=
begin
  rintros p ⟨p1, hp1, v, hv, hp⟩,
  rw hp,
  have hp1s1 : p1 ∈ (s1 : set P) := set.mem_of_mem_of_subset hp1 h,
  refine vadd_mem_of_mem_direction _ hp1s1,
  have hs : vector_span k V s ≤ s1.direction := submodule.span_mono (vsub_set_mono V h),
  rw submodule.le_def at hs,
  rw ←submodule.mem_coe,
  exact set.mem_of_mem_of_subset hv hs
end

end affine_subspace

section affine_span

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]

/-- The affine span of a set of points is the smallest affine subspace
containing those points. (Actually defined here in terms of spans in
modules.) -/
def affine_span (s : set P) : affine_subspace k V P :=
{ carrier := span_points k V s,
  smul_vsub_vadd_mem := λ c p1 p2 p3 hp1 hp2 hp3,
    vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k V hp3
      ((vector_span k V s).smul_mem c
        (vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k V hp1 hp2)) }

/-- The affine span, converted to a set, is `span_points`. -/
@[simp] lemma coe_affine_span (s : set P) :
  (affine_span k V s : set P) = span_points k V s :=
rfl

/-- The direction of the affine span is the `vector_span`. -/
lemma direction_affine_span (s : set P) : (affine_span k V s).direction = vector_span k V s :=
begin
  apply le_antisymm,
  { refine submodule.span_le.2 _,
    rintros v ⟨p1, ⟨p2, hp2, v1, hv1, hp1⟩, p3, ⟨p4, hp4, v2, hv2, hp3⟩, hv⟩,
    rw [hv, hp1, hp3, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, submodule.mem_coe],
    exact (vector_span k V s).sub_mem ((vector_span k V s).add_mem hv1
      (vsub_mem_vector_span k V hp2 hp4)) hv2 },
  { exact submodule.span_mono (vsub_set_mono V (subset_span_points k V s)) }
end

/-- A point in a set is in its affine span. -/
lemma mem_affine_span {p : P} {s : set P} (hp : p ∈ s) : p ∈ affine_span k V s :=
mem_span_points k V p s hp

end affine_span

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [S : affine_space k V P]
include S

instance : complete_lattice (affine_subspace k V P) :=
{ sup := λ s1 s2, affine_span k V (s1 ∪ s2),
  le_sup_left := λ s1 s2, set.subset.trans (set.subset_union_left s1 s2)
                                           (subset_span_points k V _),
  le_sup_right :=  λ s1 s2, set.subset.trans (set.subset_union_right s1 s2)
                                             (subset_span_points k V _),
  sup_le := λ s1 s2 s3 hs1 hs2, span_points_subset_coe_of_subset_coe (set.union_subset hs1 hs2),
  inf := λ s1 s2, mk (s1 ∩ s2)
                     (λ c p1 p2 p3 hp1 hp2 hp3,
                       ⟨s1.smul_vsub_vadd_mem c p1 p2 p3 hp1.1 hp2.1 hp3.1,
                       s2.smul_vsub_vadd_mem c p1 p2 p3 hp1.2 hp2.2 hp3.2⟩),
  inf_le_left := λ _ _, set.inter_subset_left _ _,
  inf_le_right := λ _ _, set.inter_subset_right _ _,
  le_inf := λ _ _ _, set.subset_inter,
  top := { carrier := set.univ,
    smul_vsub_vadd_mem := λ _ _ _ _ _ _ _, set.mem_univ _ },
  le_top := λ _ _ _, set.mem_univ _,
  bot := { carrier := ∅,
    smul_vsub_vadd_mem := λ _ _ _ _, false.elim },
  bot_le := λ _ _, false.elim,
  Sup := λ s, affine_span k V (⋃ s' ∈ s, (s' : set P)),
  Inf := λ s, mk (⋂ s' ∈ s, (s' : set P))
                 (λ c p1 p2 p3 hp1 hp2 hp3, set.mem_bInter_iff.2 $ λ s2 hs2,
                   s2.smul_vsub_vadd_mem c p1 p2 p3 (set.mem_bInter_iff.1 hp1 s2 hs2)
                                                    (set.mem_bInter_iff.1 hp2 s2 hs2)
                                                    (set.mem_bInter_iff.1 hp3 s2 hs2)),
  le_Sup := λ _ _ h, set.subset.trans (set.subset_bUnion_of_mem h) (subset_span_points k V _),
  Sup_le := λ _ _ h, span_points_subset_coe_of_subset_coe (set.bUnion_subset h),
  Inf_le := λ _ _, set.bInter_subset_of_mem,
  le_Inf := λ _ _, set.subset_bInter,
  .. partial_order.lift (coe : affine_subspace k V P → set P) (λ _ _, ext) }

instance : inhabited (affine_subspace k V P) := ⟨⊤⟩

/-- The `≤` order on subspaces is the same as that on the corresponding
sets. -/
lemma le_def (s1 s2 : affine_subspace k V P) : s1 ≤ s2 ↔ (s1 : set P) ⊆ s2 :=
iff.rfl

/-- One subspace is less than or equal to another if and only if all
its points are in the second subspace. -/
lemma le_def' (s1 s2 : affine_subspace k V P) : s1 ≤ s2 ↔ ∀ p ∈ s1, p ∈ s2 :=
iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding
sets. -/
lemma lt_def (s1 s2 : affine_subspace k V P) : s1 < s2 ↔ (s1 : set P) ⊂ s2 :=
iff.rfl

/-- One subspace is not less than or equal to another if and only if
it has a point not in the second subspace. -/
lemma not_le_iff_exists (s1 s2 : affine_subspace k V P) : ¬ s1 ≤ s2 ↔ ∃ p ∈ s1, p ∉ s2 :=
set.not_subset

/-- If a subspace is less than another, there is a point only in the
second. -/
lemma exists_of_lt {s1 s2 : affine_subspace k V P} (h : s1 < s2) : ∃ p ∈ s2, p ∉ s1 :=
set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or
equal to the second subspace and there is a point only in the
second. -/
lemma lt_iff_le_and_exists (s1 s2 : affine_subspace k V P) : s1 < s2 ↔ s1 ≤ s2 ∧ ∃ p ∈ s2, p ∉ s1 :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

variables (k V)

/-- The affine span is the `Inf` of subspaces containing the given
points. -/
lemma affine_span_eq_Inf (s : set P) : affine_span k V s = Inf {s' | s ⊆ s'} :=
le_antisymm (span_points_subset_coe_of_subset_coe (set.subset_bInter (λ _ h, h)))
            (Inf_le (subset_span_points k V _))

variables (P)

/-- The Galois insertion formed by `affine_span` and coercion back to
a set. -/
protected def gi : galois_insertion (affine_span k V) (coe : affine_subspace k V P → set P) :=
{ choice := λ s _, affine_span k V s,
  gc := λ s1 s2, ⟨λ h, set.subset.trans (subset_span_points k V s1) h,
                       span_points_subset_coe_of_subset_coe⟩,
  le_l_u := λ _, subset_span_points k V _,
  choice_eq := λ _ _, rfl }

/-- The span of the empty set is `⊥`. -/
@[simp] lemma span_empty : affine_span k V (∅ : set P) = ⊥ :=
(affine_subspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp] lemma span_univ : affine_span k V (set.univ : set P) = ⊤ :=
eq_top_iff.2 $ subset_span_points k V _

variables {P}

/-- The span of a union of sets is the sup of their spans. -/
lemma span_union (s t : set P) : affine_span k V (s ∪ t) = affine_span k V s ⊔ affine_span k V t :=
(affine_subspace.gi k V P).gc.l_sup

/-- The span of a union of an indexed family of sets is the sup of
their spans. -/
lemma span_Union {ι : Type*} (s : ι → set P) :
  affine_span k V (⋃ i, s i) = ⨆ i, affine_span k V (s i) :=
(affine_subspace.gi k V P).gc.l_supr

variables (P)

/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp] lemma top_coe : ((⊤ : affine_subspace k V P) : set P) = set.univ :=
rfl

variables {P}

/-- All points are in `⊤`. -/
lemma mem_top (p : P) : p ∈ (⊤ : affine_subspace k V P) :=
set.mem_univ p

variables (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp] lemma direction_top : (⊤ : affine_subspace k V P).direction = ⊤ :=
begin
  cases S.nonempty with p,
  ext v,
  refine ⟨imp_intro submodule.mem_top, λ hv, _⟩,
  have hpv : (v +ᵥ p -ᵥ p : V) ∈ (⊤ : affine_subspace k V P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _),
  rwa vadd_vsub at hpv
end

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp] lemma bot_coe : ((⊥ : affine_subspace k V P) : set P) = ∅ :=
rfl

variables {P}

/-- No points are in `⊥`. -/
lemma not_mem_bot (p : P) : p ∉ (⊥ : affine_subspace k V P) :=
set.not_mem_empty p

variables (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp] lemma direction_bot : (⊥ : affine_subspace k V P).direction = ⊥ :=
by rw [direction_eq_vector_span, bot_coe, vector_span_def, vsub_set_empty, submodule.span_empty]

variables {k V P}

/-- The inf of two affine subspaces, coerced to a set, is the
intersection of the two sets of points. -/
@[simp] lemma inf_coe (s1 s2 : affine_subspace k V P) : ((s1 ⊓ s2) : set P) = s1 ∩ s2 :=
rfl

/-- A point is in the inf of two affine subspaces if and only if it is
in both of them. -/
lemma mem_inf_iff (p : P) (s1 s2 : affine_subspace k V P) : p ∈ s1 ⊓ s2 ↔ p ∈ s1 ∧ p ∈ s2 :=
iff.rfl

/-- The direction of the inf of two affine subspaces is less than or
equal to the inf of their directions. -/
lemma direction_inf (s1 s2 : affine_subspace k V P) :
  (s1 ⊓ s2).direction ≤ s1.direction ⊓ s2.direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact le_inf
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_set_mono V (set.inter_subset_left _ _)) hp))
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_set_mono V (set.inter_subset_right _ _)) hp))
end

/-- If one affine subspace is less than or equal to another, the same
applies to their directions. -/
lemma direction_le {s1 s2 : affine_subspace k V P} (h : s1 ≤ s2) : s1.direction ≤ s2.direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact submodule.span_mono (vsub_set_mono _ h)
end

/-- If one nonempty affine subspace is less than another, the same
applies to their directions -/
lemma direction_lt_of_nonempty {s1 s2 : affine_subspace k V P} (h : s1 < s2)
    (hn : (s1 : set P).nonempty) : s1.direction < s2.direction :=
begin
  cases hn with p hp,
  rw lt_iff_le_and_exists at h,
  rcases h with ⟨hle, p2, hp2, hp2s1⟩,
  rw submodule.lt_iff_le_and_exists,
  use [direction_le hle, p2 -ᵥ p, vsub_mem_direction hp2 (hle hp)],
  intro hm,
  rw vsub_right_mem_direction_iff_mem hp p2 at hm,
  exact hp2s1 hm
end

/-- The sup of the directions of two affine subspaces is less than or
equal to the direction of their sup. -/
lemma sup_direction_le (s1 s2 : affine_subspace k V P) :
  s1.direction ⊔ s2.direction ≤ (s1 ⊔ s2).direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact sup_le
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_set_mono V (le_sup_left : s1 ≤ s1 ⊔ s2)) hp))
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_set_mono V (le_sup_right : s2 ≤ s1 ⊔ s2)) hp))
end

/-- The sup of the directions of two nonempty affine subspaces with
empty intersection is less than the direction of their sup. -/
lemma sup_direction_lt_of_nonempty_of_inter_empty {s1 s2 : affine_subspace k V P}
    (h1 : (s1 : set P).nonempty) (h2 : (s2 : set P).nonempty) (he : (s1 ∩ s2 : set P) = ∅) :
  s1.direction ⊔ s2.direction < (s1 ⊔ s2).direction :=
begin
  cases h1 with p1 hp1,
  cases h2 with p2 hp2,
  rw submodule.lt_iff_le_and_exists,
  use [sup_direction_le s1 s2, p2 -ᵥ p1,
       vsub_mem_direction ((le_sup_right : s2 ≤ s1 ⊔ s2) hp2) ((le_sup_left : s1 ≤ s1 ⊔ s2) hp1)],
  intro h,
  rw submodule.mem_sup at h,
  rcases h with ⟨v1, hv1, v2, hv2, hv1v2⟩,
  rw [←sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm v1, add_assoc,
      ←vadd_vsub_assoc, ←neg_neg v2, add_comm, ←sub_eq_add_neg, ←vsub_vadd_eq_vsub_sub,
      vsub_eq_zero_iff_eq] at hv1v2,
  refine set.nonempty.ne_empty _ he,
  use [v1 +ᵥ p1, vadd_mem_of_mem_direction hv1 hp1],
  rw hv1v2,
  exact vadd_mem_of_mem_direction (submodule.neg_mem _ hv2) hp2
end

/-- If the directions of two nonempty affine subspaces span the whole
module, they have nonempty intersection. -/
lemma inter_nonempty_of_nonempty_of_sup_direction_eq_top {s1 s2 : affine_subspace k V P}
    (h1 : (s1 : set P).nonempty) (h2 : (s2 : set P).nonempty)
    (hd : s1.direction ⊔ s2.direction = ⊤) : ((s1 : set P) ∩ s2).nonempty :=
begin
  by_contradiction h,
  rw set.not_nonempty_iff_eq_empty at h,
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h,
  rw hd at hlt,
  exact not_top_lt hlt
end

/-- If the directions of two nonempty affine subspaces are complements
of each other, they intersect in exactly one point. -/
lemma inter_eq_singleton_of_nonempty_of_is_compl {s1 s2 : affine_subspace k V P}
    (h1 : (s1 : set P).nonempty) (h2 : (s2 : set P).nonempty)
    (hd : is_compl s1.direction s2.direction) : ∃ p, (s1 : set P) ∩ s2 = {p} :=
begin
  cases inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top with p hp,
  use p,
  ext q,
  rw set.mem_singleton_iff,
  split,
  { rintros ⟨hq1, hq2⟩,
    have hqp : q -ᵥ p ∈ s1.direction ⊓ s2.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩,
    rwa [hd.inf_eq_bot, submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp },
  { exact λ h, h.symm ▸ hp }
end

end affine_subspace

namespace affine_space

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]
variables {ι : Type*}

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left. -/
lemma vector_span_eq_span_vsub_set_left {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k V s = submodule.span k {v | ∃ p2 ∈ s, v = p -ᵥ p2} :=
begin
  rw vector_span_def,
  refine le_antisymm _ (submodule.span_mono _),
  { rw submodule.span_le,
    rintros v ⟨p1, hp1, p2, hp2, hv⟩,
    rw ←vsub_sub_vsub_cancel_left V p1 p2 p at hv,
    rw [hv, submodule.mem_coe, submodule.mem_span],
    exact λ m hm, submodule.sub_mem _ (hm ⟨p2, hp2, rfl⟩) (hm ⟨p1, hp1, rfl⟩) },
  { rintros v ⟨p2, hp2, hv⟩,
    exact ⟨p, hp, p2, hp2, hv⟩ }
end

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right. -/
lemma vector_span_eq_span_vsub_set_right {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k V s = submodule.span k {v | ∃ p2 ∈ s, v = p2 -ᵥ p} :=
begin
  rw vector_span_def,
  refine le_antisymm _ (submodule.span_mono _),
  { rw submodule.span_le,
    rintros v ⟨p1, hp1, p2, hp2, hv⟩,
    rw ←vsub_sub_vsub_cancel_right V p1 p2 p at hv,
    rw [hv, submodule.mem_coe, submodule.mem_span],
    exact λ m hm, submodule.sub_mem _ (hm ⟨p1, hp1, rfl⟩) (hm ⟨p2, hp2, rfl⟩) },
  { rintros v ⟨p2, hp2, hv⟩,
    exact ⟨p2, hp2, p, hp, hv⟩ }
end

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left. -/
lemma vector_span_range_eq_span_range_vsub_left (p : ι → P) (i0 : ι) :
  vector_span k V (set.range p) = submodule.span k (set.range (λ (i : ι), p i0 -ᵥ p i)) :=
begin
  simp_rw [vector_span_eq_span_vsub_set_left k V (set.mem_range_self i0), set.exists_range_iff],
  conv_lhs { congr, congr, funext, conv { congr, funext, rw eq_comm } },
  refl
end

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right. -/
lemma vector_span_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
  vector_span k V (set.range p) = submodule.span k (set.range (λ (i : ι), p i -ᵥ p i0)) :=
begin
  simp_rw [vector_span_eq_span_vsub_set_right k V (set.mem_range_self i0), set.exists_range_iff],
  conv_lhs { congr, congr, funext, conv { congr, funext, rw eq_comm } },
  refl
end

/-- The affine span of a set is nonempty if and only if that set
is. -/
lemma affine_span_nonempty (s : set P) :
  (affine_span k V s : set P).nonempty ↔ s.nonempty :=
span_points_nonempty k V s

variables {k}

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

/-- An `affine_map k V1 P1 V2 P2` is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map (k : Type*) (V1 : Type*) (P1 : Type*) (V2 : Type*) (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space k V1 P1]
    [add_comm_group V2] [module k V2] [affine_space k V2 P2] :=
(to_fun : P1 → P2)
(linear : linear_map k V1 V2)
(map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) =  linear v +ᵥ to_fun p)

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
    {V3 : Type*} {P3 : Type*} {V4 : Type*} {P4 : Type*} [ring k]
    [add_comm_group V1] [module k V1] [affine_space k V1 P1]
    [add_comm_group V2] [module k V2] [affine_space k V2 P2]
    [add_comm_group V3] [module k V3] [affine_space k V3 P3]
    [add_comm_group V4] [module k V4] [affine_space k V4 P4]

instance: has_coe_to_fun (affine_map k V1 P1 V2 P2) := ⟨_, to_fun⟩

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp] lemma coe_mk (f : P1 → P2) (linear add) :
  ((mk f linear add : affine_map k V1 P1 V2 P2) : P1 → P2) = f := rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp] lemma to_fun_eq_coe (f : affine_map k V1 P1 V2 P2) : f.to_fun = ⇑f := rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp] lemma map_vadd (f : affine_map k V1 P1 V2 P2) (p : P1) (v : V1) :
  f (v +ᵥ p) = f.linear v +ᵥ f p := f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp] lemma linear_map_vsub (f : affine_map k V1 P1 V2 P2) (p1 p2 : P1) :
  f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
by conv_rhs { rw [←vsub_vadd V1 p1 p2, map_vadd, vadd_vsub] }

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext] lemma ext {f g : affine_map k V1 P1 V2 P2} (h : ∀ p, f p = g p) : f = g :=
begin
  rcases f with ⟨f, f_linear, f_add⟩,
  rcases g with ⟨g, g_linear, g_add⟩,
  have : f = g := funext h,
  subst g,
  congr',
  ext v,
  cases (add_torsor.nonempty V1 : nonempty P1) with p,
  apply vadd_right_cancel (f p),
  erw [← f_add, ← g_add]
end

lemma ext_iff {f g : affine_map k V1 P1 V2 P2} : f = g ↔ ∀ p, f p = g p := ⟨λ h p, h ▸ rfl, ext⟩

variables (k V1 P1 V2)

/-- Constant function as an `affine_map`. -/
def const (p : P2) : affine_map k V1 P1 V2 P2 :=
{ to_fun := function.const P1 p,
  linear := 0,
  map_vadd' := λ p v, by simp }

@[simp] lemma coe_const (p : P2) : ⇑(const k V1 P1 V2 p) = function.const P1 p := rfl

@[simp] lemma const_linear (p : P2) : (const k V1 P1 V2 p).linear = 0 := rfl

variables {k V1 P1 V2}

instance nonempty : nonempty (affine_map k V1 P1 V2 P2) :=
⟨const k V1 P1 V2 (classical.choice $ add_torsor.nonempty V2)⟩

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
  affine_map k V1 P1 V2 P2 :=
{ to_fun := f,
  linear := f',
  map_vadd' := λ p' v, by rw [h, h p', vadd_vsub_assoc, f'.map_add, add_action.vadd_assoc] }

@[simp] lemma coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f := rfl

@[simp] lemma mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' := rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
instance : add_comm_group (affine_map k V1 P1 V2 V2) :=
{ zero := ⟨0, 0, λ p v, (add_action.zero_vadd _ _).symm⟩,
  add := λ f g, ⟨f + g, f.linear + g.linear, λ p v, by simp [add_add_add_comm]⟩,
  neg := λ f, ⟨-f, -f.linear, λ p v, by simp [add_comm]⟩,
  add_assoc := λ f₁ f₂ f₃, ext $ λ p, add_assoc _ _ _,
  zero_add := λ f, ext $ λ p, zero_add (f p),
  add_zero := λ f, ext $ λ p, add_zero (f p),
  add_comm := λ f g, ext $ λ p, add_comm (f p) (g p),
  add_left_neg := λ f, ext $ λ p, add_left_neg (f p) }

@[simp, norm_cast] lemma coe_zero : ⇑(0 : affine_map k V1 P1 V2 V2) = 0 := rfl
@[simp] lemma zero_linear : (0 : affine_map k V1 P1 V2 V2).linear = 0 := rfl
@[simp, norm_cast] lemma coe_add (f g : affine_map k V1 P1 V2 V2) : ⇑(f + g) = f + g := rfl
@[simp]
lemma add_linear (f g : affine_map k V1 P1 V2 V2) : (f + g).linear = f.linear + g.linear := rfl

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine spaces
from `P1` to the vector `V2` corresponding to `P2`. -/
instance : affine_space k (affine_map k V1 P1 V2 V2) (affine_map k V1 P1 V2 P2) :=
{ vadd := λ f g, ⟨λ p, f p +ᵥ g p, f.linear + g.linear, λ p v,
    by simp [add_action.vadd_assoc, add_right_comm]⟩,
  zero_vadd' := λ f, ext $ λ p, add_action.zero_vadd _ (f p),
  vadd_assoc' := λ f₁ f₂ f₃, ext $ λ p, add_action.vadd_assoc V2 (f₁ p) (f₂ p) (f₃ p),
  vsub := λ f g, ⟨λ p, f p -ᵥ g p, f.linear - g.linear, λ p v,
    by simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub, sub_add_eq_add_sub]⟩,
  vsub_vadd' := λ f g, ext $ λ p, vsub_vadd V2 (f p) (g p),
  vadd_vsub' := λ f g, ext $ λ p, vadd_vsub V2 (f p) (g p) }

@[simp] lemma vadd_apply (f : affine_map k V1 P1 V2 V2) (g : affine_map k V1 P1 V2 P2) (p : P1) :
  (f +ᵥ g) p = f p +ᵥ g p :=
rfl

@[simp] lemma vsub_apply (f g : affine_map k V1 P1 V2 P2) (p : P1) :
  (f -ᵥ g : affine_map k V1 P1 V2 V2) p = f p -ᵥ g p :=
rfl

variables (k V1 P1)

/-- Identity map as an affine map. -/
def id : affine_map k V1 P1 V1 P1 :=
{ to_fun := id,
  linear := linear_map.id,
  map_vadd' := λ p v, rfl }

/-- The identity affine map acts as the identity. -/
@[simp] lemma coe_id : ⇑(id k V1 P1) = _root_.id := rfl

@[simp] lemma id_linear : (id k V1 P1).linear = linear_map.id := rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
lemma id_apply (p : P1) : id k V1 P1 p = p := rfl

variables {k V1 P1 V2}

instance : inhabited (affine_map k V1 P1 V1 P1) := ⟨id k V1 P1⟩

/-- Composition of affine maps. -/
def comp (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) :
  affine_map k V1 P1 V3 P3 :=
{ to_fun := f ∘ g,
  linear := f.linear.comp g.linear,
  map_vadd' := begin
    intros p v,
    rw [function.comp_app, g.map_vadd, f.map_vadd],
    refl
  end }

/-- Composition of affine maps acts as applying the two functions. -/
@[simp] lemma coe_comp (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) :
  ⇑(f.comp g) = f ∘ g := rfl

/-- Composition of affine maps acts as applying the two functions. -/
lemma comp_apply (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) (p : P1) :
  f.comp g p = f (g p) := rfl

@[simp] lemma comp_id (f : affine_map k V1 P1 V2 P2) : f.comp (id k V1 P1) = f := ext $ λ p, rfl

@[simp] lemma id_comp (f : affine_map k V1 P1 V2 P2) : (id k V2 P2).comp f = f := ext $ λ p, rfl

lemma comp_assoc (f₃₄ : affine_map k V3 P3 V4 P4) (f₂₃ : affine_map k V2 P2 V3 P3)
  (f₁₂ : affine_map k V1 P1 V2 P2) :
  (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
rfl

instance : monoid (affine_map k V1 P1 V1 P1) :=
{ one := id k V1 P1,
  mul := comp,
  one_mul := id_comp,
  mul_one := comp_id,
  mul_assoc := comp_assoc }

@[simp] lemma coe_mul (f g : affine_map k V1 P1 V1 P1) : ⇑(f * g) = f ∘ g := rfl
@[simp] lemma coe_one : ⇑(1 : affine_map k V1 P1 V1 P1) = _root_.id := rfl

/-- The affine map from `k` to `P1` sending `0` to `p` and `1` to `v +ᵥ p`. -/
def line_map (p : P1) (v : V1) : affine_map k k k V1 P1 :=
{ to_fun := λ c, c • v +ᵥ p,
  linear := linear_map.id.smul_right v,
  map_vadd' := λ a b, by simp [add_smul, add_action.vadd_assoc] }

lemma line_map_apply (p : P1) (v : V1) (c : k) : line_map p v c = c • v +ᵥ p := rfl

@[simp] lemma line_map_linear (p : P1) (v : V1) :
  (line_map p v : affine_map k k k V1 P1).linear = linear_map.id.smul_right v :=
rfl

@[simp] lemma line_map_zero (p : P1) : line_map p (0:V1) = const k k k V1 p :=
by { ext c, simp [line_map_apply] }

@[simp] lemma line_map_apply_zero (p : P1) (v : V1) : line_map p v (0:k) = p :=
by simp [line_map_apply]

@[simp] lemma affine_apply_line_map (f : affine_map k V1 P1 V2 P2) (p : P1) (v : V1) (c : k) :
  f (line_map p v c) = line_map (f p) (f.linear v) c :=
by simp [line_map_apply]

@[simp] lemma affine_comp_line_map (f : affine_map k V1 P1 V2 P2) (p : P1) (v : V1) :
  f.comp (line_map p v) = line_map (f p) (f.linear v) :=
ext $ f.affine_apply_line_map p v

lemma line_map_vadd_neg (p : P1) (v : V1) :
  line_map (v +ᵥ p) (-v) = (line_map p v).comp (line_map (1:k) (-1:k)) :=
by { rw [affine_comp_line_map], simp [line_map_apply] }

end affine_map

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} [comm_ring k]
    [add_comm_group V1] [module k V1] [affine_space k V1 P1] [add_comm_group V2] [module k V2]

/-- If `k` is a commutative ring, then the set of affine maps with codomain in a `k`-module
is a `k`-module. -/
instance : module k (affine_map k V1 P1 V2 V2) :=
{ smul := λ c f, ⟨c • f, c • f.linear, λ p v, by simp [smul_add]⟩,
  one_smul := λ f, ext $ λ p, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ p, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ p, smul_add _ _ _,
  smul_zero := λ c, ext $ λ p, smul_zero _,
  add_smul := λ c₁ c₂ f, ext $ λ p, add_smul _ _ _,
  zero_smul := λ f, ext $ λ p, zero_smul _ _ }

@[simp] lemma coe_smul (c : k) (f : affine_map k V1 P1 V2 V2) : ⇑(c • f) = c • f := rfl

variable (V1)

/-- `homothety V c r` is the homothety about `c` with scale factor `r`. -/
def homothety (c : P1) (r : k) : affine_map k V1 P1 V1 P1 :=
r • (id k V1 P1 -ᵥ const k V1 P1 V1 c : affine_map k V1 P1 V1 V1) +ᵥ const k V1 P1 V1 c

lemma homothety_def (c : P1) (r : k) :
  homothety V1 c r = r • (id k V1 P1 -ᵥ const k V1 P1 V1 c : affine_map k V1 P1 V1 V1) +ᵥ
    const k V1 P1 V1 c :=
rfl

lemma homothety_apply (c : P1) (r : k) (p : P1)  :
  homothety V1 c r p = r • (p -ᵥ c : V1) +ᵥ c := rfl

@[simp] lemma homothety_one (c : P1) : homothety V1 c (1:k) = id k V1 P1 :=
by { ext p, simp [homothety_apply] }

lemma homothety_mul (c : P1) (r₁ r₂ : k) :
  homothety V1 c (r₁ * r₂) = (homothety V1 c r₁).comp (homothety V1 c r₂) :=
by { ext p, simp [homothety_apply, mul_smul] }

@[simp] lemma homothety_zero (c : P1) : homothety V1 c (0:k) = const k V1 P1 V1 c :=
by { ext p, simp [homothety_apply] }

@[simp] lemma homothety_add (c : P1) (r₁ r₂ : k) :
  homothety V1 c (r₁ + r₂) =
    r₁ • (id k V1 P1 -ᵥ const k V1 P1 V1 c : affine_map k V1 P1 V1 V1) +ᵥ homothety V1 c r₂ :=
by simp only [homothety_def, add_smul, add_action.vadd_assoc]

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothety_hom (c : P1) : k →* affine_map k V1 P1 V1 P1 :=
⟨homothety V1 c, homothety_one V1 c, homothety_mul V1 c⟩

@[simp] lemma coe_homothety_hom (c : P1) : ⇑(homothety_hom V1 c : k →* _) = homothety V1 c := rfl

/-- `homothety` as an affine map. -/
def homothety_affine (c : P1) :
  affine_map k k k (affine_map k V1 P1 V1 V1) (affine_map k V1 P1 V1 P1) :=
⟨homothety V1 c, (linear_map.lsmul k _).flip (id k V1 P1 -ᵥ const k V1 P1 V1 c),
  function.swap (homothety_add V1 c)⟩

@[simp] lemma coe_homothety_affine (c : P1) :
  ⇑(homothety_affine V1 c : affine_map k k k _ _) = homothety V1 c :=
rfl

end affine_map

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

namespace linear_map

variables {k : Type*} {V₁ : Type*} {V₂ : Type*} [ring k] [add_comm_group V₁] [module k V₁]
  [add_comm_group V₂] [module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def to_affine_map : affine_map k V₁ V₁ V₂ V₂ :=
{ to_fun := f,
  linear := f,
  map_vadd' := λ p v, f.map_add v p }

@[simp] lemma coe_to_affine_map : ⇑f.to_affine_map = f := rfl

@[simp] lemma to_affine_map_linear : f.to_affine_map.linear = f := rfl

end linear_map
