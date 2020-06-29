/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
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

/-- `affine_space` is an abbreviation for `add_torsor` in the case
where the group is a vector space, or more generally a module, but we
omit the type classes `[ring k]` and `[module k V]` in the type
synonym itself to simplify type class search.. -/
@[nolint unused_arguments]
abbreviation affine_space (k : Type*) (V : Type*) (P : Type*) [add_comm_group V] :=
add_torsor V P

namespace affine_space

open add_action
open add_torsor

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [S : affine_space k V P]
include S

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (s : set P) : submodule k V := submodule.span k (vsub_set V s)

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k V P`,
if the set of points is known to be nonempty. -/
def span_points (s : set P) : set P :=
{p | ∃ p1 ∈ s, ∃ v ∈ (vector_span k V s), p = v +ᵥ p1}

/-- A point in a set is in its affine span. -/
lemma mem_span_points (p : P) (s : set P) : p ∈ s → p ∈ span_points k V s
| hp := ⟨p, hp, 0, submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- The set of points in the affine span of a nonempty set of points
is nonempty. -/
lemma span_points_nonempty_of_nonempty {s : set P} :
  s.nonempty → (span_points k V s).nonempty 
| ⟨p, hp⟩ := ⟨p, mem_span_points k V p s hp⟩

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
  unfold vector_span,
  change p1a -ᵥ p2a ∈ submodule.span k (vsub_set V s),
  have hp1p2 : p1a -ᵥ p2a ∈ vsub_set V s, { use [p1a, hp1a, p2a, hp2a] },
  have hp1p2s : vsub_set V s ⊆ submodule.span k (vsub_set V s) := submodule.subset_span,
  apply set.mem_of_mem_of_subset hp1p2 hp1p2s
end

end affine_space

namespace finset

open add_action
open add_torsor

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

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weighted_vsub (p : ι → P) : (ι → k) →ₗ[k] V :=
s.weighted_vsub_of_point V p (classical.choice S.nonempty)

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
lemma weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 0) (b : P) : s.weighted_vsub V p w = s.weighted_vsub_of_point V p b w :=
s.weighted_vsub_of_point_eq_of_sum_eq_zero V w p h _ _

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point.  This is intended to
be used when the sum of the weights is 1, in which case it is an
affine combination (barycenter) of the points with the given weights;
that condition is specified as a hypothesis on those lemmas that
require it. -/
def affine_combination (w : ι → k) (p : ι → P) : P :=
s.weighted_vsub_of_point V p (classical.choice S.nonempty) w +ᵥ (classical.choice S.nonempty)

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

end finset

section affine_independent

open add_torsor

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

open add_torsor affine_space

/-- An `affine_subspace k V P` is a subset of an `affine_space k V P`
that has an affine space structure induced by a corresponding subspace
of the `module k V`. -/
structure affine_subspace (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V]
    [module k V] [affine_space k V P] :=
(carrier : set P)
(direction : submodule k V)
(nonempty : carrier.nonempty)
(add : ∀ (p : P) (v : V), p ∈ carrier → v ∈ direction → v +ᵥ p ∈ carrier)
(sub : ∀ (p1 p2 : P), p1 ∈ carrier → p2 ∈ carrier → p1 -ᵥ p2 ∈ direction)

namespace affine_subspace

variables (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V] [module k V]
          [S : affine_space k V P]
include S

instance : has_coe (affine_subspace k V P) (set P) := ⟨carrier⟩
instance : has_mem P (affine_subspace k V P) := ⟨λ p s, p ∈ (s : set P)⟩

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp] lemma mem_coe (p : P) (s : affine_subspace k V P) :
  p ∈ (s : set P) ↔ p ∈ s :=
iff.rfl

/-- The whole affine space as a subspace of itself. -/
def univ : affine_subspace k V P :=
{ carrier := set.univ,
  direction := submodule.span k set.univ,
  nonempty := set.nonempty_iff_univ_nonempty.1 S.nonempty,
  add := λ p v hp hv, set.mem_univ _,
  sub := begin
    intros p1 p2 hp1 hp2,
    apply set.mem_bInter,
    intros x hx,
    rw set.mem_set_of_eq at hx,
    exact set.mem_of_mem_of_subset (set.mem_univ _) hx
  end }

/-- `univ`, coerced to a set, is the whole set of points. -/
@[simp] lemma univ_coe : (univ k V P : set P) = set.univ :=
rfl

/-- All points are in `univ`. -/
lemma mem_univ (p : P) : p ∈ univ k V P :=
set.mem_univ p

instance : inhabited (affine_subspace k V P) := ⟨univ k V P⟩

variables {k V P}

/-- Two affine subspaces are equal if they have the same points. -/
@[ext] lemma ext {s1 s2 : affine_subspace k V P} (h : (s1 : set P) = s2) : s1 = s2 :=
begin
  cases s1,
  cases s2,
  change s1_carrier = s2_carrier at h,
  congr,
  { exact h },
  { ext v,
    split,
    { intro hv,
      have hm := s1_nonempty.some_mem,
      have hvp := s1_add s1_nonempty.some v hm hv,
      conv_rhs at hm { rw h },
      conv_rhs at hvp { rw h },
      rw ←vadd_vsub V v s1_nonempty.some,
      exact s2_sub _ _ hvp hm },
    { intro hv,
      have hm := s2_nonempty.some_mem,
      have hvp := s2_add s2_nonempty.some v hm hv,
      conv_rhs at hm { rw ←h },
      conv_rhs at hvp { rw ←h },
      rw ←vadd_vsub V v s2_nonempty.some,
      exact s1_sub _ _ hvp hm } }
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
    refine s2.add _ _ hq2 _,
    rw ←hd,
    exact s1.sub _ _ hp hq1 },
  { intro hp,
    rw ←vsub_vadd V p hn.some,
    refine s1.add _ _ hq1 _,
    rw hd,
    exact s2.sub _ _ hp hq2 }
end

/-- Construct an affine subspace from a point and a direction. -/
def mk_of_point_of_direction (p : P) (direction : submodule k V) : affine_subspace k V P :=
{ carrier := {q | ∃ v ∈ direction, q = v +ᵥ p},
  direction := direction,
  nonempty := ⟨p, ⟨0, ⟨direction.zero_mem, (add_action.zero_vadd _ _).symm⟩⟩⟩,
  add := λ p2 v hp2 hv, begin
    rcases hp2 with ⟨v2, hv2, hp2⟩,
    use [v + v2, direction.add_mem hv hv2],
    rw [←add_action.vadd_assoc, hp2]
  end,
  sub := λ p1 p2 hp1 hp2, begin
    rcases hp1 with ⟨v1, hv1, hp1⟩,
    rcases hp2 with ⟨v2, hv2, hp2⟩,
    rw [hp1, hp2, vadd_vsub_vadd_cancel_right],
    exact direction.sub_mem hv1 hv2
  end }

/-- The direction of an affine space constructed from a point and a
direction. -/
@[simp] lemma direction_mk_of_point_of_direction (p : P) (direction : submodule k V) :
  (mk_of_point_of_direction p direction).direction = direction :=
rfl

/-- An affine space constructed from a point and a direction contains
that point. -/
lemma mem_mk_of_point_of_direction (p : P) (direction : submodule k V) :
  p ∈ mk_of_point_of_direction p direction :=
⟨0, ⟨direction.zero_mem, (add_action.zero_vadd _ _).symm⟩⟩

/-- Constructing an affine subspace from a point in a subspace and
that subspace's direction yields the original subspace. -/
@[simp] lemma mk_of_point_of_direction_eq {s : affine_subspace k V P} {p : P} (hp : p ∈ s) :
  mk_of_point_of_direction p s.direction = s :=
ext_of_direction_eq rfl ⟨p, set.mem_inter (mem_mk_of_point_of_direction _ _) hp⟩

end affine_subspace

section affine_span

variables (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]

/-- The affine span of a nonempty set of points is the smallest affine
subspace containing those points. (Actually defined here in terms of
spans in modules.) -/
def affine_span (s : set P) (h : s.nonempty) : affine_subspace k V P :=
{ carrier := span_points k V s,
  direction := vector_span k V s,
  nonempty := span_points_nonempty_of_nonempty k V h,
  add := λ p v hp hv, vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k V hp hv,
  sub := λ p1 p2 hp1 hp2, vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k V hp1 hp2 }

/-- The affine span, converted to a set, is `span_points`. -/
@[simp] lemma affine_span_coe (s : set P) (h : s.nonempty) :
  (affine_span k V P s h : set P) = span_points k V s :=
rfl

/-- A point in a set is in its affine span. -/
lemma affine_span_mem (p : P) (s : set P) (hp : p ∈ s) : p ∈ affine_span k V P s ⟨p, hp⟩ :=
mem_span_points k V p s hp

end affine_span

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
