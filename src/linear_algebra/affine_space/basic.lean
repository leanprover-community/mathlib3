/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
import linear_algebra.tensor_product
import data.set.intervals.unordered_interval
import order.copy

noncomputable theory
open_locale big_operators
open_locale classical

/-!
# Affine spaces

This file defines affine spaces (over modules) and subspaces, affine
maps, and the affine span of a set of points.  For affine combinations
of points, see `linear_algebra.affine_space.combination`.  For
affinely independent families of points, see
`linear_algebra.affine_space.independent`.  For some additional
results relating to finite-dimensional subspaces of affine spaces, see
`linear_algebra.affine_space.finite_dimensional`.

## Main definitions

* `affine_space V P` is an abbreviation for `add_torsor V P` in the
  case of `module k V`.  `P` is the type of points in the space and
  `V` the `k`-module of displacement vectors.  Definitions and results
  not depending on the `module` structure appear in
  `algebra.add_torsor` instead of here; that includes the instance of
  an `add_group` as an `add_torsor` over itself, which thus gives a
  `module` as an `affine_space` over itself.  Definitions of affine
  spaces vary as to whether a space with no points is permitted; here,
  we require a nonempty type of points (via the definition of torsors
  requiring a nonempty type).  Affine spaces are defined over any
  module, with stronger type class requirements on `k` being used for
  individual lemmas where needed.
* `affine_subspace k P` is the type of affine subspaces.  Unlike
  affine spaces, affine subspaces are allowed to be empty, and lemmas
  that do not apply to empty affine subspaces have `nonempty`
  hypotheses.  There is a `complete_lattice` structure on affine
  subspaces.
* `affine_subspace.direction` gives the `submodule` spanned by the
  pairwise differences of points in an `affine_subspace`.  There are
  various lemmas relating to the set of vectors in the `direction`,
  and relating the lattice structure on affine subspaces to that on
  their directions.
* `affine_span` gives the affine subspace spanned by a set of points,
  with `vector_span` giving its direction.  `affine_span` is defined
  in terms of `span_points`, which gives an explicit description of
  the points contained in the affine span; `span_points` itself should
  generally only be used when that description is required, with
  `affine_span` being the main definition for other purposes.  Two
  other descriptions of the affine span are proved equivalent: it is
  the `Inf` of affine subspaces containing the points, and (if
  `[nontrivial k]`) it contains exactly those points that are affine
  combinations of points in the given set.
* `affine_map` is the type of affine maps between two affine spaces
  with the same ring `k`.  Various basic examples of affine maps are
  defined, including `const`, `id`, `line_map` and `homothety`.

## Notations

* `P1 →ᵃ[k] P2` is a notation for `affine_map k P1 P2`

## Implementation notes

`out_param` is used to make `V` an implicit argument (deduced from
`P`) in most cases; `include V` is needed in many cases for `V`, and
type classes using it, to be added as implicit arguments to
individual lemmas.  As for modules, `k` is an explicit argument rather
than implied by `P` or `V`.

This file only provides purely algebraic definitions and results.
Those depending on analysis or topology are defined elsewhere; see
`analysis.normed_space.add_torsor` and `topology.algebra.affine`.

TODO: Some key definitions are not yet present.

* Coercions from an `affine_subspace` to the subtype of its points,
  and a corresponding `affine_space` instance on that subtype in the
  case of a nonempty subspace.
* `affine_equiv` (see issue #2909).
* Affine frames.  An affine frame might perhaps be represented as an
  `affine_equiv` to a `finsupp` (in the general case) or function type
  (in the finite-dimensional case) that gives the coordinates, with
  appropriate proofs of existence when `k` is a field.
* Although results on affine combinations implicitly provide
  barycentric frames and coordinates, there is no explicit
  representation of the map from a point to its coordinates.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space

-/

/- `affine_space` is an abbreviation for `add_torsor` in the case where the group is a vector
space, or more generally a module. We omit the arguments `(k : Type*) [ring k] [module k V]`
in the type synonym itself to simplify type class search. -/
notation `affine_space` := add_torsor

open set

section

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (s : set P) : submodule k V := submodule.span k (s -ᵥ s)

/-- The definition of `vector_span`, for rewriting. -/
lemma vector_span_def (s : set P) : vector_span k s = submodule.span k (s -ᵥ s) :=
rfl

/-- `vector_span` is monotone. -/
@[mono] lemma vector_span_mono {s₁ s₂ : set P} (h : s₁ ⊆ s₂) :
  vector_span k s₁ ≤ vector_span k s₂ :=
submodule.span_mono (vsub_self_mono h)

variables (P)

/-- The `vector_span` of the empty set is `⊥`. -/
@[simp] lemma vector_span_empty : vector_span k (∅ : set P) = (⊥ : submodule k V) :=
by rw [vector_span_def, vsub_empty, submodule.span_empty]

variables {P}

/-- The `vector_span` of a single point is `⊥`. -/
@[simp] lemma vector_span_singleton (p : P) : vector_span k ({p} : set P) = ⊥ :=
by simp [vector_span_def]

/-- The `s -ᵥ s` lies within the `vector_span k s`. -/
lemma vsub_set_subset_vector_span (s : set P) : s -ᵥ s ⊆ ↑(vector_span k s) :=
submodule.subset_span

/-- Each pairwise difference is in the `vector_span`. -/
lemma vsub_mem_vector_span {s : set P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  p1 -ᵥ p2 ∈ vector_span k s :=
vsub_set_subset_vector_span k s (vsub_mem_vsub hp1 hp2)

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left. -/
lemma vector_span_eq_span_vsub_set_left {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ) p '' s) :=
begin
  refine submodule.span_eq_of_le _ _ (submodule.span_le.2 _),
  { rintros _ ⟨x, y, hx, hy, rfl⟩,
    rw [← vsub_sub_vsub_cancel_left _ _ p, submodule.mem_coe],
    exact submodule.sub_mem _ (submodule.subset_span $ mem_image_of_mem _ hy)
      (submodule.subset_span $ mem_image_of_mem _ hx) },
  { rintros _ ⟨x, hx, rfl⟩,
    exact submodule.subset_span (mem_image2_of_mem hp hx)  }
end

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right. -/
lemma vector_span_eq_span_vsub_set_right {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ p) '' s) :=
begin
  rw [vector_span_eq_span_vsub_set_left k hp, ← submodule.span_neg, ← image_neg, ← image_comp],
  simp only [(∘), neg_vsub_eq_vsub_rev]
end

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left, excluding the subtraction of that point from
itself. -/
lemma vector_span_eq_span_vsub_set_left_ne {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ) p '' (s \ {p})) :=
begin
  conv_lhs { rw [vector_span_eq_span_vsub_set_left k hp, ←set.insert_eq_of_mem hp,
                 ←set.insert_diff_singleton, set.image_insert_eq] },
  simp [submodule.span_insert_eq_span]
end

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from
itself. -/
lemma vector_span_eq_span_vsub_set_right_ne {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ p) '' (s \ {p})) :=
begin
  conv_lhs { rw [vector_span_eq_span_vsub_set_right k hp, ←set.insert_eq_of_mem hp,
                 ←set.insert_diff_singleton, set.image_insert_eq] },
  simp [submodule.span_insert_eq_span]
end

end

/-- An `affine_subspace k P` is a subset of an `affine_space V P`
that, if not empty, has an affine space structure induced by a
corresponding subspace of the `module k V`. -/
structure affine_subspace (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V]
    [module k V] [affine_space V P] :=
(carrier : set P)
(direction : submodule k V)
(vadd_mem_iff' : ∀ (p ∈ carrier) (v), v +ᵥ p ∈ carrier ↔ v ∈ direction)
(nonempty' : direction ≠ ⊥ → carrier.nonempty)

namespace submodule

variables {k V : Type*} [ring k] [add_comm_group V] [module k V]

/-- Reinterpret `p : submodule k V` as an `affine_subspace k V`. -/
def to_affine_subspace (p : submodule k V) : affine_subspace k V :=
{ carrier := p,
  direction := p,
  vadd_mem_iff' := λ v h v', p.add_mem_iff_left h,
  nonempty' := λ _, p.nonempty }

end submodule

namespace affine_subspace

variables (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

instance : has_coe (affine_subspace k P) (set P) := ⟨carrier⟩
instance : has_mem P (affine_subspace k P) := ⟨λ p s, p ∈ (s : set P)⟩

variables {k P} (s : affine_subspace k P) {v v₁ v₂ : V} {p p₁ p₂ : P}

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp, norm_cast] lemma mem_coe (p : P) (s : affine_subspace k P) :
  p ∈ (s : set P) ↔ p ∈ s :=
iff.rfl

/-- Adding a vector to a point in a subspace produces a point in the
subspace if and only if the vector is in the direction. -/
lemma vadd_mem_iff_mem_direction (h : p ∈ s) : v +ᵥ p ∈ s ↔ v ∈ s.direction :=
s.vadd_mem_iff' p h v

/-- Adding a vector in the direction to a point in the subspace
produces a point in the subspace. -/
lemma vadd_mem (hv : v ∈ s.direction) (hp : p ∈ s) : v +ᵥ p ∈ s :=
(s.vadd_mem_iff_mem_direction hp).2 hv

lemma vadd_mem_iff_mem (hv : v ∈ s.direction) : v +ᵥ p ∈ s ↔ p ∈ s :=
⟨λ h, by { rw [← zero_vadd V p, ← neg_add_self v, ← vadd_assoc],
  exact s.vadd_mem (s.direction.neg_mem hv) h}, s.vadd_mem hv⟩

lemma vsub_mem_direction_iff_left (h : p₂ ∈ s) : p₁ -ᵥ p₂ ∈ s.direction ↔ p₁ ∈ s :=
by rw [← s.vadd_mem_iff_mem_direction h, vsub_vadd]

lemma vsub_mem_direction_iff_right (h : p₁ ∈ s) : p₁ -ᵥ p₂ ∈ s.direction ↔ p₂ ∈ s :=
by rw [← s.direction.neg_mem_iff, neg_vsub_eq_vsub_rev, s.vsub_mem_direction_iff_left h]

/-- Subtracting two points in the subspace produces a vector in the
direction. -/
lemma vsub_mem_direction (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) : p₁ -ᵥ p₂ ∈ s.direction :=
(s.vsub_mem_direction_iff_left h₂).2 h₁

lemma vsub_set_subset_coe_direction : (s : set P) -ᵥ (s : set P) ⊆ ↑s.direction :=
image2_subset_iff.2 $ λ x hx y hy, s.vsub_mem_direction hx hy

protected lemma nonempty (hd : s.direction ≠ ⊥) : set.nonempty (s : set P) := s.nonempty' hd

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
right. -/
lemma coe_direction_eq_vsub_set_right (hp : p ∈ s) :
  (s.direction : set V) = (-ᵥ p) '' s :=
subset.antisymm (λ v hv, ⟨v +ᵥ p, s.vadd_mem hv hp, vadd_vsub v p⟩) $
  subset.trans (image_vsub_const_subset_vsub hp) s.vsub_set_subset_coe_direction

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
left. -/
lemma coe_direction_eq_vsub_set_left (hp : p ∈ s) :
  (s.direction : set V) = (-ᵥ) p '' s :=
subset.antisymm (λ v hv, ⟨-v +ᵥ p, s.vadd_mem (submodule.neg_mem _ hv) hp,
  by rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_neg]⟩) $
  subset.trans (image_const_vsub_subset_vsub hp) s.vsub_set_subset_coe_direction

/-- The set of vectors in the direction of a nonempty affine subspace
is given by `s -ᵥ s`. -/
lemma coe_direction_eq_vsub_set (hs : (s : set P).nonempty) :
  ↑s.direction = (s : set P) -ᵥ s :=
subset.antisymm (exists.elim hs $ λ p hp v hv, ⟨v +ᵥ p, p, s.vadd_mem hv hp, hp, vadd_vsub v p⟩)
  s.vsub_set_subset_coe_direction

/-- A vector is in the direction of a nonempty affine subspace if and
only if it is the subtraction of two vectors in the subspace. -/
lemma mem_direction_iff_eq_vsub (h : (s : set P).nonempty) {v : V} :
  v ∈ s.direction ↔ ∃ (p₁ ∈ s) (p₂ ∈ s), p₁ -ᵥ p₂ = v :=
begin
  rw [←submodule.mem_coe, s.coe_direction_eq_vsub_set h],
  exact mem_image2_iff'
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the right. -/
lemma mem_direction_iff_eq_vsub_right (hp : p ∈ s) {v : V} :
  v ∈ s.direction ↔ ∃ p2 ∈ s, p2 -ᵥ p = v :=
begin
  rw [←submodule.mem_coe, s.coe_direction_eq_vsub_set_right hp, mem_image_iff_bex],
  refl
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the left. -/
lemma mem_direction_iff_eq_vsub_left (hp : p ∈ s) {v : V} :
  v ∈ s.direction ↔ ∃ p2 ∈ s, p -ᵥ p2 = v :=
begin
  rw [←submodule.mem_coe, s.coe_direction_eq_vsub_set_left hp, mem_image_iff_bex],
  refl
end

lemma direction_eq_span (s : affine_subspace k P) :
  s.direction = submodule.span k ((s : set P) -ᵥ s) :=
begin
  by_cases hbot : s.direction = ⊥,
  { refine (submodule.span_eq_of_le _ s.vsub_set_subset_coe_direction _).symm,
    rw hbot,
    exact bot_le },
  { rw [← s.coe_direction_eq_vsub_set (s.nonempty hbot), submodule.span_eq] }
end

/-- Two affine subspaces are equal if they have the same points. -/
lemma injective_coe_set : function.injective (coe : affine_subspace k P → set P) :=
begin
  intros s s' h,
  have : s.direction = s'.direction,
  { rw [s.direction_eq_span, s'.direction_eq_span, h] },
  cases s, cases s',
  congr, exacts [h, this]
end

variables {s} {s' : affine_subspace k P}

/-- Two affine subspaces are equal if they have the same points. -/
@[ext] lemma ext (h : ∀ x, x ∈ s ↔ x ∈ s') : s = s' :=
injective_coe_set $ set.ext h

/-- Two affine subspaces with the same direction and nonempty
intersection are equal. -/
lemma ext_of_direction_eq (hd : s.direction = s'.direction) (hn : ((s : set P) ∩ s').nonempty) :
  s = s' :=
begin
  ext p,
  rcases hn with ⟨x, h : x ∈ s, h' : x ∈ s'⟩,
  rw [← s.vsub_mem_direction_iff_left h, hd, s'.vsub_mem_direction_iff_left h']
end

/-- Two affine subspaces with nonempty intersection are equal if and
only if their directions are equal. -/
lemma eq_iff_direction_eq_of_mem (h : p ∈ s) (h' : p ∈ s') :
  s = s' ↔ s.direction = s'.direction :=
⟨λ h, h ▸ rfl, λ hd, ext_of_direction_eq hd ⟨p, h, h'⟩⟩

/-- Construct an affine subspace from a point and a direction. -/
def mk' (p : P) (direction : submodule k V) : affine_subspace k P :=
{ carrier := (+ᵥ p) '' (direction : set V),
  direction := direction,
  nonempty' := λ _, direction.nonempty.image _,
  vadd_mem_iff' :=
    begin
      simp only [mem_image_eq, direction.mem_coe],
      rintro _ ⟨v, hv, rfl⟩ v',
      simp [vadd_assoc, direction.add_mem_iff_left hv]
    end }

/-- An affine subspace constructed from a point and a direction contains that point. -/
lemma self_mem_mk' (p : P) (direction : submodule k V) :
  p ∈ mk' p direction :=
⟨0, ⟨direction.zero_mem, zero_vadd _ _⟩⟩

/-- An affine subspace constructed from a point and a direction contains
the result of adding a vector in that direction to that point. -/
lemma vadd_mem_mk' {v : V} (p : P) {direction : submodule k V} (hv : v ∈ direction) :
  v +ᵥ p ∈ mk' p direction :=
⟨v, hv, rfl⟩

/-- An affine subspace constructed from a point and a direction is nonempty. -/
lemma mk'_nonempty (p : P) (direction : submodule k V) : (mk' p direction : set P).nonempty :=
⟨p, self_mem_mk' p direction⟩

/-- The direction of an affine subspace constructed from a point and a direction. -/
@[simp] lemma direction_mk' (p : P) (direction : submodule k V) :
  (mk' p direction).direction = direction :=
rfl

protected def copy (orig : affine_subspace k P) (s : set P) (d : submodule k V) (hs : ↑orig = s)
  (hd : orig.direction = d) : affine_subspace k P :=
{ carrier := s,
  direction := d,
  nonempty' := hd ▸ hs ▸ orig.nonempty,
  vadd_mem_iff' := hd ▸ hs ▸ orig.vadd_mem_iff' }

variables (s s')

/-- Constructing an affine subspace from a point in a subspace and that subspace's direction yields
the original subspace. -/
@[simp] lemma mk'_eq (hp : p ∈ s) : mk' p s.direction = s :=
ext_of_direction_eq (direction_mk' p s.direction) ⟨p, ⟨self_mem_mk' _ _, hp⟩⟩

section lattice

instance : has_Inf (affine_subspace k P) :=
{ Inf := λ S,
  { carrier := ⋂ s ∈ S, ↑(s : affine_subspace k P),
    direction := if (⋂ s ∈ S, ((s : affine_subspace k P) : set P)).nonempty
                 then ⨅ s ∈ S, direction s else ⊥,
    nonempty' := λ hd, by_contra $ λ h, hd $ if_neg h,
    vadd_mem_iff' :=
      begin
        intros p hp v,
        rw [if_pos (show (⋂ s ∈ S, ((s : affine_subspace k P) : set P)).nonempty, from ⟨p, hp⟩)],
        simp only [mem_Inter, mem_coe] at hp,
        simp only [mem_Inter, submodule.mem_infi, mem_coe],
        exact forall_congr (λ s, forall_congr (λ hs, vadd_mem_iff_mem_direction _ (hp _ hs)))
      end } }

@[simp] lemma coe_Inf (S : set (affine_subspace k P)) : (↑(Inf S) : set P) = ⋂ s ∈ S, ↑s := rfl

@[simp] lemma mem_Inf {S : set (affine_subspace k P)} {x : P} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s :=
mem_bInter_iff

lemma direction_Inf_of_nonempty {S : set (affine_subspace k P)} (hS : (↑(Inf S) : set P).nonempty) :
  (Inf S).direction = ⨅ s ∈ S, direction s :=
if_pos hS

lemma direction_Inf_of_mem {S : set (affine_subspace k P)} {x : P} (hx : x ∈ Inf S) :
  (Inf S).direction = ⨅ s ∈ S, direction s :=
if_pos ⟨x, hx⟩

lemma direction_Inf_of_forall_mem {S : set (affine_subspace k P)} {x : P} (hx : ∀ s ∈ S, x ∈ s) :
  (Inf S).direction = ⨅ s ∈ S, direction s :=
direction_Inf_of_mem (mem_Inf.2 hx)

lemma direction_Inf_of_empty {S : set (affine_subspace k P)} (hx : (⋂ s ∈ S, (s : set P)) = ∅) :
  (Inf S).direction = ⊥ :=
if_neg $ not_nonempty_iff_eq_empty.2 hx

variable {ι : Sort*}

@[simp] lemma coe_infi {s : ι → affine_subspace k P} : (↑(⨅ i, s i) : set P) = ⋂ i, s i :=
by rw [infi, coe_Inf, bInter_range]

@[simp] lemma mem_infi {s : ι → affine_subspace k P} {x : P} : (x ∈ ⨅ i, s i) ↔ ∀ i, x ∈ s i :=
by simp only [infi, mem_Inf, forall_range_iff]

lemma direction_infi_of_nonempty {s : ι → affine_subspace k P}
  (hs : (↑(⨅ i, s i) : set P).nonempty) :
  (⨅ i, s i).direction = ⨅ i, (s i).direction :=
by rw [infi, direction_Inf_of_nonempty hs, infi_range]

instance : has_inf (affine_subspace k P) :=
{ inf := λ s t, affine_subspace.copy (Inf {s, t}) (s ∩ t)
    (if ((s : set P) ∩ t).nonempty then s.direction ⊓ t.direction else ⊥)
    (bInter_pair _ _ _) (if_congr (by rw [bInter_pair]) infi_pair rfl) }

@[simp] lemma coe_inf (s t : affine_subspace k P) : ((s ⊓ t) : set P) = s ∩ t := rfl

@[simp] lemma mem_inf {s t : affine_subspace k P} {x : P} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl

lemma direction_inf_of_nonempty {s t : affine_subspace k P} (hS : ((s ⊓ t) : set P).nonempty) :
  (s ⊓ t).direction = s.direction ⊓ t.direction :=
if_pos hS

lemma direction_inf_of_mem_inf {s t : affine_subspace k P} {x : P} (hx : x ∈ s ⊓ t) :
  (s ⊓ t).direction = s.direction ⊓ t.direction :=
if_pos ⟨x, hx⟩

lemma direction_inf_of_mem {s t : affine_subspace k P} {x : P} (hs : x ∈ s) (ht : x ∈ t) :
  (s ⊓ t).direction = s.direction ⊓ t.direction :=
if_pos ⟨x, hs, ht⟩

lemma direction_inf_of_empty {s t : affine_subspace k P} (hx : (s ∩ t : set P) = ∅) :
  (s ⊓ t).direction = ⊥ :=
if_neg $ not_nonempty_iff_eq_empty.2 hx

instance : has_le (affine_subspace k P) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

instance : partial_order (affine_subspace k P) :=
{ le := (≤),
  lt := λ s t, s ≤ t ∧ ¬t ≤ s,
  ..partial_order.lift (coe : affine_subspace k P → set P) injective_coe_set }

instance : complete_lattice (affine_subspace k P) :=
have ∀ S : set (affine_subspace k P), is_glb S (Inf S),
  from λ S, ⟨λ s hs x hx, mem_Inf.1 hx _ hs, λ s hs x hx, mem_Inf.2 $ λ t ht, hs ht hx⟩,
{ bot := ⟨∅, ⊥, λ x hx, hx.elim, λ h, (h rfl).elim⟩,
  bot_le := λ s x hx, hx.elim,
  top := ⟨univ, ⊤, λ p hp v, iff.rfl, λ _, univ_nonempty⟩,
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t u ht hu x hx, ⟨ht hx, hu hx⟩,
  .. complete_lattice_of_Inf _ this }

end lattice


end affine_subspace

section affine_span

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

/-- The affine span of a set of points is the smallest affine subspace
containing those points. -/
def affine_span (s : set P) : affine_subspace k P :=

/-- The affine span, converted to a set, is `span_points`. -/
@[simp] lemma coe_affine_span (s : set P) :
  (affine_span k s : set P) = span_points k s :=
rfl

/-- A set is contained in its affine span. -/
lemma subset_affine_span (s : set P) : s ⊆ affine_span k s :=
subset_span_points k s

/-- The direction of the affine span is the `vector_span`. -/
lemma direction_affine_span (s : set P) : (affine_span k s).direction = vector_span k s :=
begin
  apply le_antisymm,
  { refine submodule.span_le.2 _,
    rintros v ⟨p1, p3, ⟨p2, hp2, v1, hv1, hp1⟩, ⟨p4, hp4, v2, hv2, hp3⟩, rfl⟩,
    rw [hp1, hp3, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, submodule.mem_coe],
    exact (vector_span k s).sub_mem ((vector_span k s).add_mem hv1
      (vsub_mem_vector_span k hp2 hp4)) hv2 },
  { exact vector_span_mono k (subset_span_points k s) }
end

/-- A point in a set is in its affine span. -/
lemma mem_affine_span {p : P} {s : set P} (hp : p ∈ s) : p ∈ affine_span k s :=
mem_span_points k p s hp

end affine_span

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [S : affine_space V P]
include S

instance : complete_lattice (affine_subspace k P) :=
{ sup := λ s1 s2, affine_span k (s1 ∪ s2),
  le_sup_left := λ s1 s2, set.subset.trans (set.subset_union_left s1 s2)
                                           (subset_span_points k _),
  le_sup_right :=  λ s1 s2, set.subset.trans (set.subset_union_right s1 s2)
                                             (subset_span_points k _),
  sup_le := λ s1 s2 s3 hs1 hs2, span_points_subset_coe_of_subset_coe (set.union_subset hs1 hs2),
  inf := λ s1 s2, mk (s1 ∩ s2)
                     (λ c p1 p2 p3 hp1 hp2 hp3,
                       ⟨s1.smul_vsub_vadd_mem c hp1.1 hp2.1 hp3.1,
                       s2.smul_vsub_vadd_mem c hp1.2 hp2.2 hp3.2⟩),
  inf_le_left := λ _ _, set.inter_subset_left _ _,
  inf_le_right := λ _ _, set.inter_subset_right _ _,
  le_inf := λ _ _ _, set.subset_inter,
  top := { carrier := set.univ,
    smul_vsub_vadd_mem := λ _ _ _ _ _ _ _, set.mem_univ _ },
  le_top := λ _ _ _, set.mem_univ _,
  bot := { carrier := ∅,
    smul_vsub_vadd_mem := λ _ _ _ _, false.elim },
  bot_le := λ _ _, false.elim,
  Sup := λ s, affine_span k (⋃ s' ∈ s, (s' : set P)),
  Inf := λ s, mk (⋂ s' ∈ s, (s' : set P))
                 (λ c p1 p2 p3 hp1 hp2 hp3, set.mem_bInter_iff.2 $ λ s2 hs2,
                   s2.smul_vsub_vadd_mem c (set.mem_bInter_iff.1 hp1 s2 hs2)
                                           (set.mem_bInter_iff.1 hp2 s2 hs2)
                                           (set.mem_bInter_iff.1 hp3 s2 hs2)),
  le_Sup := λ _ _ h, set.subset.trans (set.subset_bUnion_of_mem h) (subset_span_points k _),
  Sup_le := λ _ _ h, span_points_subset_coe_of_subset_coe (set.bUnion_subset h),
  Inf_le := λ _ _, set.bInter_subset_of_mem,
  le_Inf := λ _ _, set.subset_bInter,
  .. partial_order.lift (coe : affine_subspace k P → set P) (λ _ _, ext) }

instance : inhabited (affine_subspace k P) := ⟨⊤⟩

/-- The `≤` order on subspaces is the same as that on the corresponding
sets. -/
lemma le_def (s1 s2 : affine_subspace k P) : s1 ≤ s2 ↔ (s1 : set P) ⊆ s2 :=
iff.rfl

/-- One subspace is less than or equal to another if and only if all
its points are in the second subspace. -/
lemma le_def' (s1 s2 : affine_subspace k P) : s1 ≤ s2 ↔ ∀ p ∈ s1, p ∈ s2 :=
iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding
sets. -/
lemma lt_def (s1 s2 : affine_subspace k P) : s1 < s2 ↔ (s1 : set P) ⊂ s2 :=
iff.rfl

/-- One subspace is not less than or equal to another if and only if
it has a point not in the second subspace. -/
lemma not_le_iff_exists (s1 s2 : affine_subspace k P) : ¬ s1 ≤ s2 ↔ ∃ p ∈ s1, p ∉ s2 :=
set.not_subset

/-- If a subspace is less than another, there is a point only in the
second. -/
lemma exists_of_lt {s1 s2 : affine_subspace k P} (h : s1 < s2) : ∃ p ∈ s2, p ∉ s1 :=
set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or
equal to the second subspace and there is a point only in the
second. -/
lemma lt_iff_le_and_exists (s1 s2 : affine_subspace k P) : s1 < s2 ↔ s1 ≤ s2 ∧ ∃ p ∈ s2, p ∉ s1 :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

/-- If an affine subspace is nonempty and contained in another with
the same direction, they are equal. -/
lemma eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : affine_subspace k P}
  (hd : s₁.direction = s₂.direction) (hn : (s₁ : set P).nonempty) (hle : s₁ ≤ s₂) :
  s₁ = s₂ :=
let ⟨p, hp⟩ := hn in ext_of_direction_eq hd ⟨p, hp, hle hp⟩

variables (k V)

/-- The affine span is the `Inf` of subspaces containing the given
points. -/
lemma affine_span_eq_Inf (s : set P) : affine_span k s = Inf {s' | s ⊆ s'} :=
le_antisymm (span_points_subset_coe_of_subset_coe (set.subset_bInter (λ _ h, h)))
            (Inf_le (subset_span_points k _))

variables (P)

/-- The Galois insertion formed by `affine_span` and coercion back to
a set. -/
protected def gi : galois_insertion (affine_span k) (coe : affine_subspace k P → set P) :=
{ choice := λ s _, affine_span k s,
  gc := λ s1 s2, ⟨λ h, set.subset.trans (subset_span_points k s1) h,
                       span_points_subset_coe_of_subset_coe⟩,
  le_l_u := λ _, subset_span_points k _,
  choice_eq := λ _ _, rfl }

/-- The span of the empty set is `⊥`. -/
@[simp] lemma span_empty : affine_span k (∅ : set P) = ⊥ :=
(affine_subspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp] lemma span_univ : affine_span k (set.univ : set P) = ⊤ :=
eq_top_iff.2 $ subset_span_points k _

variables {P}

/-- The affine span of a single point, coerced to a set, contains just
that point. -/
@[simp] lemma coe_affine_span_singleton (p : P) : (affine_span k ({p} : set P) : set P) = {p} :=
begin
  ext x,
  rw [mem_coe, ←vsub_right_mem_direction_iff_mem (mem_affine_span k (set.mem_singleton p)) _,
      direction_affine_span],
  simp
end

/-- A point is in the affine span of a single point if and only if
they are equal. -/
@[simp] lemma mem_affine_span_singleton (p1 p2 : P) :
  p1 ∈ affine_span k ({p2} : set P) ↔ p1 = p2 :=
by simp [←mem_coe]

/-- The span of a union of sets is the sup of their spans. -/
lemma span_union (s t : set P) : affine_span k (s ∪ t) = affine_span k s ⊔ affine_span k t :=
(affine_subspace.gi k V P).gc.l_sup

/-- The span of a union of an indexed family of sets is the sup of
their spans. -/
lemma span_Union {ι : Type*} (s : ι → set P) :
  affine_span k (⋃ i, s i) = ⨆ i, affine_span k (s i) :=
(affine_subspace.gi k V P).gc.l_supr

variables (P)

/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp] lemma top_coe : ((⊤ : affine_subspace k P) : set P) = set.univ :=
rfl

variables {P}

/-- All points are in `⊤`. -/
lemma mem_top (p : P) : p ∈ (⊤ : affine_subspace k P) :=
set.mem_univ p

variables (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp] lemma direction_top : (⊤ : affine_subspace k P).direction = ⊤ :=
begin
  cases S.nonempty with p,
  ext v,
  refine ⟨imp_intro submodule.mem_top, λ hv, _⟩,
  have hpv : (v +ᵥ p -ᵥ p : V) ∈ (⊤ : affine_subspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _),
  rwa vadd_vsub at hpv
end

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp] lemma bot_coe : ((⊥ : affine_subspace k P) : set P) = ∅ :=
rfl

variables {P}

/-- No points are in `⊥`. -/
lemma not_mem_bot (p : P) : p ∉ (⊥ : affine_subspace k P) :=
set.not_mem_empty p

variables (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp] lemma direction_bot : (⊥ : affine_subspace k P).direction = ⊥ :=
by rw [direction_eq_vector_span, bot_coe, vector_span_def, vsub_empty, submodule.span_empty]

variables {k V P}

/-- A nonempty affine subspace is `⊤` if and only if its direction is
`⊤`. -/
@[simp] lemma direction_eq_top_iff_of_nonempty {s : affine_subspace k P}
  (h : (s : set P).nonempty) : s.direction = ⊤ ↔ s = ⊤ :=
begin
  split,
  { intro hd,
    rw ←direction_top k V P at hd,
    refine ext_of_direction_eq hd _,
    simp [h] },
  { rintro rfl,
    simp }
end

/-- The inf of two affine subspaces, coerced to a set, is the
intersection of the two sets of points. -/
@[simp] lemma inf_coe (s1 s2 : affine_subspace k P) : ((s1 ⊓ s2) : set P) = s1 ∩ s2 :=
rfl

/-- A point is in the inf of two affine subspaces if and only if it is
in both of them. -/
lemma mem_inf_iff (p : P) (s1 s2 : affine_subspace k P) : p ∈ s1 ⊓ s2 ↔ p ∈ s1 ∧ p ∈ s2 :=
iff.rfl

/-- The direction of the inf of two affine subspaces is less than or
equal to the inf of their directions. -/
lemma direction_inf (s1 s2 : affine_subspace k P) :
  (s1 ⊓ s2).direction ≤ s1.direction ⊓ s2.direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact le_inf
    (Inf_le_Inf (λ p hp, trans (vsub_self_mono (inter_subset_left _ _)) hp))
    (Inf_le_Inf (λ p hp, trans (vsub_self_mono (inter_subset_right _ _)) hp))
end

/-- If two affine subspaces have a point in common, the direction of
their inf equals the inf of their directions. -/
lemma direction_inf_of_mem {s₁ s₂ : affine_subspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
  (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
begin
  ext v,
  rw [submodule.mem_inf, ←vadd_mem_iff_mem_direction v h₁, ←vadd_mem_iff_mem_direction v h₂,
      ←vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), mem_inf_iff]
end

/-- If two affine subspaces have a point in their inf, the direction
of their inf equals the inf of their directions. -/
lemma direction_inf_of_mem_inf {s₁ s₂ : affine_subspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
  (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

/-- If one affine subspace is less than or equal to another, the same
applies to their directions. -/
lemma direction_le {s1 s2 : affine_subspace k P} (h : s1 ≤ s2) : s1.direction ≤ s2.direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact vector_span_mono k h
end

/-- If one nonempty affine subspace is less than another, the same
applies to their directions -/
lemma direction_lt_of_nonempty {s1 s2 : affine_subspace k P} (h : s1 < s2)
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
lemma sup_direction_le (s1 s2 : affine_subspace k P) :
  s1.direction ⊔ s2.direction ≤ (s1 ⊔ s2).direction :=
begin
  repeat { rw [direction_eq_vector_span, vector_span_def] },
  exact sup_le
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_self_mono (le_sup_left : s1 ≤ s1 ⊔ s2)) hp))
    (Inf_le_Inf (λ p hp, set.subset.trans (vsub_self_mono (le_sup_right : s2 ≤ s1 ⊔ s2)) hp))
end

/-- The sup of the directions of two nonempty affine subspaces with
empty intersection is less than the direction of their sup. -/
lemma sup_direction_lt_of_nonempty_of_inter_empty {s1 s2 : affine_subspace k P}
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
lemma inter_nonempty_of_nonempty_of_sup_direction_eq_top {s1 s2 : affine_subspace k P}
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
lemma inter_eq_singleton_of_nonempty_of_is_compl {s1 s2 : affine_subspace k P}
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

/-- Coercing a subspace to a set then taking the affine span produces
the original subspace. -/
@[simp] lemma affine_span_coe (s : affine_subspace k P) : affine_span k (s : set P) = s :=
begin
  refine le_antisymm _ (subset_span_points _ _),
  rintros p ⟨p1, hp1, v, hv, rfl⟩,
  exact vadd_mem_of_mem_direction hv hp1
end

end affine_subspace

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open affine_subspace set

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the left, excluding the
subtraction of that point from itself. -/
lemma vector_span_image_eq_span_vsub_set_left_ne (p : ι → P) {s : set ι} {i : ι} (hi : i ∈ s) :
  vector_span k (p '' s) = submodule.span k ((-ᵥ) (p i) '' (p '' (s \ {i}))) :=
begin
  conv_lhs { rw [vector_span_eq_span_vsub_set_left k (set.mem_image_of_mem p hi),
                 ←set.insert_eq_of_mem hi, ←set.insert_diff_singleton, set.image_insert_eq,
                 set.image_insert_eq] },
  simp [submodule.span_insert_eq_span]
end

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the right, excluding the
subtraction of that point from itself. -/
lemma vector_span_image_eq_span_vsub_set_right_ne (p : ι → P) {s : set ι} {i : ι} (hi : i ∈ s) :
  vector_span k (p '' s) = submodule.span k ((-ᵥ (p i)) '' (p '' (s \ {i}))) :=
begin
  conv_lhs { rw [vector_span_eq_span_vsub_set_right k (set.mem_image_of_mem p hi),
                 ←set.insert_eq_of_mem hi, ←set.insert_diff_singleton, set.image_insert_eq,
                 set.image_insert_eq] },
  simp [submodule.span_insert_eq_span]
end

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left. -/
lemma vector_span_range_eq_span_range_vsub_left (p : ι → P) (i0 : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : ι), p i0 -ᵥ p i)) :=
by rw [vector_span_eq_span_vsub_set_left k (set.mem_range_self i0), ←set.range_comp]

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right. -/
lemma vector_span_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : ι), p i -ᵥ p i0)) :=
by rw [vector_span_eq_span_vsub_set_right k (set.mem_range_self i0), ←set.range_comp]

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left, excluding the subtraction
of that point from itself. -/
lemma vector_span_range_eq_span_range_vsub_left_ne (p : ι → P) (i₀ : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : {x // x ≠ i₀}), p i₀ -ᵥ p i)) :=
begin
  rw [←set.image_univ, vector_span_image_eq_span_vsub_set_left_ne k _ (set.mem_univ i₀)],
  congr' with v,
  simp only [set.mem_range, set.mem_image, set.mem_diff, set.mem_singleton_iff, subtype.exists,
             subtype.coe_mk],
  split,
  { rintros ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩,
    exact ⟨i₁, hi₁, hv⟩ },
  { exact λ ⟨i₁, hi₁, hv⟩, ⟨p i₁, ⟨i₁, ⟨set.mem_univ _, hi₁⟩, rfl⟩, hv⟩ }
end

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right, excluding the subtraction
of that point from itself. -/
lemma vector_span_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
  vector_span k (set.range p) = submodule.span k (set.range (λ (i : {x // x ≠ i₀}), p i -ᵥ p i₀)) :=
begin
  rw [←set.image_univ, vector_span_image_eq_span_vsub_set_right_ne k _ (set.mem_univ i₀)],
  congr' with v,
  simp only [set.mem_range, set.mem_image, set.mem_diff, set.mem_singleton_iff, subtype.exists,
             subtype.coe_mk],
  split,
  { rintros ⟨x, ⟨i₁, ⟨⟨hi₁u, hi₁⟩, rfl⟩⟩, hv⟩,
    exact ⟨i₁, hi₁, hv⟩ },
  { exact λ ⟨i₁, hi₁, hv⟩, ⟨p i₁, ⟨i₁, ⟨set.mem_univ _, hi₁⟩, rfl⟩, hv⟩ }
end

/-- The affine span of a set is nonempty if and only if that set
is. -/
lemma affine_span_nonempty (s : set P) :
  (affine_span k s : set P).nonempty ↔ s.nonempty :=
span_points_nonempty k s

variables {k}

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together
with those vectors added to `p`, spans `P`. -/
lemma affine_span_singleton_union_vadd_eq_top_of_span_eq_top {s : set V} (p : P)
    (h : submodule.span k (set.range (coe : s → V)) = ⊤) :
  affine_span k ({p} ∪ (λ v, v +ᵥ p) '' s) = ⊤ :=
begin
  convert ext_of_direction_eq _
    ⟨p,
     mem_affine_span k (set.mem_union_left _ (set.mem_singleton _)),
     mem_top k V p⟩,
  rw [direction_affine_span, direction_top,
      vector_span_eq_span_vsub_set_right k
        ((set.mem_union_left _ (set.mem_singleton _)) : p ∈ _), eq_top_iff, ←h],
  apply submodule.span_mono,
  rintros v ⟨v', rfl⟩,
  use (v' : V) +ᵥ p,
  simp
end

variables (k)

/-- `affine_span` is monotone. -/
lemma affine_span_mono {s₁ s₂ : set P} (h : s₁ ⊆ s₂) : affine_span k s₁ ≤ affine_span k s₂ :=
span_points_subset_coe_of_subset_coe (set.subset.trans h (subset_affine_span k _))

/-- Taking the affine span of a set, adding a point and taking the
span again produces the same results as adding the point to the set
and taking the span. -/
lemma affine_span_insert_affine_span (p : P) (ps : set P) :
  affine_span k (insert p (affine_span k ps : set P)) = affine_span k (insert p ps) :=
by rw [set.insert_eq, set.insert_eq, span_union, span_union, affine_span_coe]

/-- If a point is in the affine span of a set, adding it to that set
does not change the affine span. -/
lemma affine_span_insert_eq_affine_span {p : P} {ps : set P} (h : p ∈ affine_span k ps) :
  affine_span k (insert p ps) = affine_span k ps :=
begin
  rw ←mem_coe at h,
  rw [←affine_span_insert_affine_span, set.insert_eq_of_mem h, affine_span_coe]
end

end affine_space'

namespace affine_subspace

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

/-- The direction of the sup of two nonempty affine subspaces is the
sup of the two directions and of any one difference between points in
the two subspaces. -/
lemma direction_sup {s1 s2 : affine_subspace k P} {p1 p2 : P} (hp1 : p1 ∈ s1) (hp2 : p2 ∈ s2) :
  (s1 ⊔ s2).direction = s1.direction ⊔ s2.direction ⊔ submodule.span k {p2 -ᵥ p1} :=
begin
  refine le_antisymm _ _,
  { change (affine_span k ((s1 : set P) ∪ s2)).direction ≤ _,
    rw ←mem_coe at hp1,
    rw [direction_affine_span, vector_span_eq_span_vsub_set_right k (set.mem_union_left _ hp1),
        submodule.span_le],
    rintros v ⟨p3, hp3, rfl⟩,
    cases hp3,
    { rw [sup_assoc, sup_comm, submodule.mem_coe, submodule.mem_sup],
      use [0, submodule.zero_mem _, p3 -ᵥ p1, vsub_mem_direction hp3 hp1],
      rw zero_add },
    { rw [sup_assoc, submodule.mem_coe, submodule.mem_sup],
      use [0, submodule.zero_mem _, p3 -ᵥ p1],
      rw [and_comm, zero_add],
      use rfl,
      rw [←vsub_add_vsub_cancel p3 p2 p1, submodule.mem_sup],
      use [p3 -ᵥ p2, vsub_mem_direction hp3 hp2, p2 -ᵥ p1,
           submodule.mem_span_singleton_self _] } },
  { refine sup_le (sup_direction_le _ _) _,
    rw [direction_eq_vector_span, vector_span_def],
    exact Inf_le_Inf (λ p hp, set.subset.trans
      (set.singleton_subset_iff.2
        (vsub_mem_vsub (mem_span_points k p2 _ (set.mem_union_right _ hp2))
                       (mem_span_points k p1 _ (set.mem_union_left _ hp1))))
      hp) }
end

/-- The direction of the span of the result of adding a point to a
nonempty affine subspace is the sup of the direction of that subspace
and of any one difference between that point and a point in the
subspace. -/
lemma direction_affine_span_insert {s : affine_subspace k P} {p1 p2 : P} (hp1 : p1 ∈ s) :
  (affine_span k (insert p2 (s : set P))).direction = submodule.span k {p2 -ᵥ p1} ⊔ s.direction :=
begin
  rw [sup_comm, ←set.union_singleton, ←coe_affine_span_singleton k V p2],
  change (s ⊔ affine_span k {p2}).direction = _,
  rw [direction_sup hp1 (mem_affine_span k (set.mem_singleton _)), direction_affine_span],
  simp
end

/-- Given a point `p1` in an affine subspace `s`, and a point `p2`, a
point `p` is in the span of `s` with `p2` added if and only if it is a
multiple of `p2 -ᵥ p1` added to a point in `s`. -/
lemma mem_affine_span_insert_iff {s : affine_subspace k P} {p1 : P} (hp1 : p1 ∈ s) (p2 p : P) :
  p ∈ affine_span k (insert p2 (s : set P)) ↔
    ∃ (r : k) (p0 : P) (hp0 : p0 ∈ s), p = r • (p2 -ᵥ p1 : V) +ᵥ p0 :=
begin
  rw ←mem_coe at hp1,
  rw [←vsub_right_mem_direction_iff_mem (mem_affine_span k (set.mem_insert_of_mem _ hp1)),
      direction_affine_span_insert hp1, submodule.mem_sup],
  split,
  { rintros ⟨v1, hv1, v2, hv2, hp⟩,
    rw submodule.mem_span_singleton at hv1,
    rcases hv1 with ⟨r, rfl⟩,
    use [r, v2 +ᵥ p1, vadd_mem_of_mem_direction hv2 hp1],
    symmetry' at hp,
    rw [←sub_eq_zero_iff_eq, ←vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp,
    rw [hp, vadd_assoc] },
  { rintros ⟨r, p3, hp3, rfl⟩,
    use [r • (p2 -ᵥ p1), submodule.mem_span_singleton.2 ⟨r, rfl⟩, p3 -ᵥ p1,
         vsub_mem_direction hp3 hp1],
    rw [vadd_vsub_assoc, add_comm] }
end

end affine_subspace

/-- An `affine_map k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2] :=
(to_fun : P1 → P2)
(linear : linear_map k V1 V2)
(map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) =  linear v +ᵥ to_fun p)

notation P1 ` →ᵃ[`:25 k:25 `] `:0 P2:0 := affine_map k P1 P2

instance (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]:
    has_coe_to_fun (P1 →ᵃ[k] P2) := ⟨_, affine_map.to_fun⟩

namespace linear_map

variables {k : Type*} {V₁ : Type*} {V₂ : Type*} [ring k] [add_comm_group V₁] [module k V₁]
  [add_comm_group V₂] [module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def to_affine_map : V₁ →ᵃ[k] V₂ :=
{ to_fun := f,
  linear := f,
  map_vadd' := λ p v, f.map_add v p }

@[simp] lemma coe_to_affine_map : ⇑f.to_affine_map = f := rfl

@[simp] lemma to_affine_map_linear : f.to_affine_map.linear = f := rfl

end linear_map

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
    {V3 : Type*} {P3 : Type*} {V4 : Type*} {P4 : Type*} [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]
    [add_comm_group V3] [module k V3] [affine_space V3 P3]
    [add_comm_group V4] [module k V4] [affine_space V4 P4]
include V1 V2

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp] lemma coe_mk (f : P1 → P2) (linear add) :
  ((mk f linear add : P1 →ᵃ[k] P2) : P1 → P2) = f := rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp] lemma to_fun_eq_coe (f : P1 →ᵃ[k] P2) : f.to_fun = ⇑f := rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp] lemma map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) :
  f (v +ᵥ p) = f.linear v +ᵥ f p := f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp] lemma linear_map_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) :
  f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
by conv_rhs { rw [←vsub_vadd p1 p2, map_vadd, vadd_vsub] }

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext] lemma ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
begin
  rcases f with ⟨f, f_linear, f_add⟩,
  rcases g with ⟨g, g_linear, g_add⟩,
  have : f = g := funext h,
  subst g,
  congr' with v,
  cases (add_torsor.nonempty : nonempty P1) with p,
  apply vadd_right_cancel (f p),
  erw [← f_add, ← g_add]
end

lemma ext_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ ∀ p, f p = g p := ⟨λ h p, h ▸ rfl, ext⟩

lemma injective_coe_fn : function.injective (λ (f : P1 →ᵃ[k] P2) (x : P1), f x) :=
λ f g H, ext $ congr_fun H

protected lemma congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
congr_arg _ h

protected lemma congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
h ▸ rfl

variables (k P1)

/-- Constant function as an `affine_map`. -/
def const (p : P2) : P1 →ᵃ[k] P2 :=
{ to_fun := function.const P1 p,
  linear := 0,
  map_vadd' := λ p v, by simp }

@[simp] lemma coe_const (p : P2) : ⇑(const k P1 p) = function.const P1 p := rfl

@[simp] lemma const_linear (p : P2) : (const k P1 p).linear = 0 := rfl

variables {k P1}

instance nonempty : nonempty (P1 →ᵃ[k] P2) :=
(add_torsor.nonempty : nonempty P2).elim $ λ p, ⟨const k P1 p⟩

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
  P1 →ᵃ[k] P2 :=
{ to_fun := f,
  linear := f',
  map_vadd' := λ p' v, by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_assoc] }

@[simp] lemma coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f := rfl

@[simp] lemma mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' := rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
instance : add_comm_group (P1 →ᵃ[k] V2) :=
{ zero := ⟨0, 0, λ p v, (zero_vadd _ _).symm⟩,
  add := λ f g, ⟨f + g, f.linear + g.linear, λ p v, by simp [add_add_add_comm]⟩,
  neg := λ f, ⟨-f, -f.linear, λ p v, by simp [add_comm]⟩,
  add_assoc := λ f₁ f₂ f₃, ext $ λ p, add_assoc _ _ _,
  zero_add := λ f, ext $ λ p, zero_add (f p),
  add_zero := λ f, ext $ λ p, add_zero (f p),
  add_comm := λ f g, ext $ λ p, add_comm (f p) (g p),
  add_left_neg := λ f, ext $ λ p, add_left_neg (f p) }

@[simp, norm_cast] lemma coe_zero : ⇑(0 : P1 →ᵃ[k] V2) = 0 := rfl
@[simp] lemma zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 := rfl
@[simp, norm_cast] lemma coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g := rfl
@[simp]
lemma add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear := rfl

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
instance : affine_space (P1 →ᵃ[k] V2) (P1 →ᵃ[k] P2) :=
{ vadd := λ f g, ⟨λ p, f p +ᵥ g p, f.linear + g.linear, λ p v,
    by simp [vadd_assoc, add_right_comm]⟩,
  zero_vadd' := λ f, ext $ λ p, zero_vadd _ (f p),
  vadd_assoc' := λ f₁ f₂ f₃, ext $ λ p, vadd_assoc (f₁ p) (f₂ p) (f₃ p),
  vsub := λ f g, ⟨λ p, f p -ᵥ g p, f.linear - g.linear, λ p v,
    by simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub, sub_add_eq_add_sub]⟩,
  vsub_vadd' := λ f g, ext $ λ p, vsub_vadd (f p) (g p),
  vadd_vsub' := λ f g, ext $ λ p, vadd_vsub (f p) (g p) }

@[simp] lemma vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) :
  (f +ᵥ g) p = f p +ᵥ g p :=
rfl

@[simp] lemma vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) :
  (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
rfl

/-- `prod.fst` as an `affine_map`. -/
def fst : (P1 × P2) →ᵃ[k] P1 :=
{ to_fun := prod.fst,
  linear := linear_map.fst k V1 V2,
  map_vadd' := λ _ _, rfl }

@[simp] lemma coe_fst : ⇑(fst : (P1 × P2) →ᵃ[k] P1) = prod.fst := rfl
@[simp] lemma fst_linear : (fst : (P1 × P2) →ᵃ[k] P1).linear = linear_map.fst k V1 V2 := rfl

/-- `prod.snd` as an `affine_map`. -/
def snd : (P1 × P2) →ᵃ[k] P2 :=
{ to_fun := prod.snd,
  linear := linear_map.snd k V1 V2,
  map_vadd' := λ _ _, rfl }

@[simp] lemma coe_snd : ⇑(snd : (P1 × P2) →ᵃ[k] P2) = prod.snd := rfl
@[simp] lemma snd_linear : (snd : (P1 × P2) →ᵃ[k] P2).linear = linear_map.snd k V1 V2 := rfl

variables (k P1)
omit V2

/-- Identity map as an affine map. -/
def id : P1 →ᵃ[k] P1 :=
{ to_fun := id,
  linear := linear_map.id,
  map_vadd' := λ p v, rfl }

/-- The identity affine map acts as the identity. -/
@[simp] lemma coe_id : ⇑(id k P1) = _root_.id := rfl

@[simp] lemma id_linear : (id k P1).linear = linear_map.id := rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
lemma id_apply (p : P1) : id k P1 p = p := rfl

variables {k P1}

instance : inhabited (P1 →ᵃ[k] P1) := ⟨id k P1⟩

include V2 V3

/-- Composition of affine maps. -/
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 :=
{ to_fun := f ∘ g,
  linear := f.linear.comp g.linear,
  map_vadd' := begin
    intros p v,
    rw [function.comp_app, g.map_vadd, f.map_vadd],
    refl
  end }

/-- Composition of affine maps acts as applying the two functions. -/
@[simp] lemma coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) :
  ⇑(f.comp g) = f ∘ g := rfl

/-- Composition of affine maps acts as applying the two functions. -/
lemma comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) :
  f.comp g p = f (g p) := rfl

omit V3

@[simp] lemma comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f := ext $ λ p, rfl

@[simp] lemma id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f := ext $ λ p, rfl

include V3 V4

lemma comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
  (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
rfl

omit V2 V3 V4

instance : monoid (P1 →ᵃ[k] P1) :=
{ one := id k P1,
  mul := comp,
  one_mul := id_comp,
  mul_one := comp_id,
  mul_assoc := comp_assoc }

@[simp] lemma coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g := rfl
@[simp] lemma coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id := rfl

/-! ### Definition of `affine_map.line_map` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def line_map (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
((linear_map.id : k →ₗ[k] k).smul_right (p₁ -ᵥ p₀)).to_affine_map +ᵥ const k k p₀

lemma coe_line_map (p₀ p₁ : P1) : (line_map p₀ p₁ : k → P1) = λ c, c • (p₁ -ᵥ p₀) +ᵥ p₀ := rfl

lemma line_map_apply (p₀ p₁ : P1) (c : k) : line_map p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ := rfl

lemma line_map_apply_module' (p₀ p₁ : V1) (c : k) : line_map p₀ p₁ c = c • (p₁ - p₀) + p₀ := rfl

lemma line_map_apply_module (p₀ p₁ : V1) (c : k) : line_map p₀ p₁ c = (1 - c) • p₀ + c • p₁ :=
by simp [line_map_apply_module', smul_sub, sub_smul]; abel

omit V1

lemma line_map_apply_ring' (a b c : k) : line_map a b c = c * (b - a) + a :=
rfl

lemma line_map_apply_ring (a b c : k) : line_map a b c = (1 - c) * a + c * b :=
line_map_apply_module a b c

include V1

lemma line_map_vadd_apply (p : P1) (v : V1) (c : k) :
  line_map p (v +ᵥ p) c = c • v +ᵥ p :=
by rw [line_map_apply, vadd_vsub]

@[simp] lemma line_map_linear (p₀ p₁ : P1) :
  (line_map p₀ p₁ : k →ᵃ[k] P1).linear = linear_map.id.smul_right (p₁ -ᵥ p₀) :=
add_zero _

lemma line_map_same_apply (p : P1) (c : k) : line_map p p c = p := by simp [line_map_apply]

@[simp] lemma line_map_same (p : P1) : line_map p p = const k k p :=
ext $ line_map_same_apply p

@[simp] lemma line_map_apply_zero (p₀ p₁ : P1) : line_map p₀ p₁ (0:k) = p₀ :=
by simp [line_map_apply]

@[simp] lemma line_map_apply_one (p₀ p₁ : P1) : line_map p₀ p₁ (1:k) = p₁ :=
by simp [line_map_apply]

include V2

@[simp] lemma apply_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
  f (line_map p₀ p₁ c) = line_map (f p₀) (f p₁) c :=
by simp [line_map_apply]

@[simp] lemma comp_line_map (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) :
  f.comp (line_map p₀ p₁) = line_map (f p₀) (f p₁) :=
ext $ f.apply_line_map p₀ p₁

@[simp] lemma fst_line_map (p₀ p₁ : P1 × P2) (c : k) :
  (line_map p₀ p₁ c).1 = line_map p₀.1 p₁.1 c :=
fst.apply_line_map p₀ p₁ c

@[simp] lemma snd_line_map (p₀ p₁ : P1 × P2) (c : k) :
  (line_map p₀ p₁ c).2 = line_map p₀.2 p₁.2 c :=
snd.apply_line_map p₀ p₁ c

omit V2

lemma line_map_symm (p₀ p₁ : P1) :
  line_map p₀ p₁ = (line_map p₁ p₀).comp (line_map (1:k) (0:k)) :=
by { rw [comp_line_map], simp }

lemma line_map_apply_one_sub (p₀ p₁ : P1) (c : k) :
  line_map p₀ p₁ (1 - c) = line_map p₁ p₀ c :=
by { rw [line_map_symm p₀, comp_apply], congr, simp [line_map_apply] }

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
lemma decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = f.linear + (λ z, f 0) :=
begin
  ext x,
  calc
    f x = f.linear x +ᵥ f 0                      : by simp [← f.map_vadd]
    ... = (f.linear.to_fun + λ (z : V1), f 0) x  : by simp
end

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
lemma decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = f - (λ z, f 0) :=
by rw decomp ; simp only [linear_map.map_zero, pi.add_apply, add_sub_cancel, zero_add]

omit V1

lemma image_interval {k : Type*} [discrete_linear_ordered_field k] (f : k →ᵃ[k] k)
  (a b : k) :
  f '' set.interval a b = set.interval (f a) (f b) :=
begin
  have : ⇑f = (λ x, x + f 0) ∘ λ x, x * (f 1 - f 0),
  { ext x,
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0,
    rw [← f.linear_map_vsub, ← f.linear.map_smul, ← f.map_vadd],
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul] },
  rw [this, set.image_comp],
  simp only [set.image_add_const_interval, set.image_mul_const_interval]
end

end affine_map

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} [comm_ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1] [add_comm_group V2] [module k V2]
include V1

/-- If `k` is a commutative ring, then the set of affine maps with codomain in a `k`-module
is a `k`-module. -/
instance : module k (P1 →ᵃ[k] V2) :=
{ smul := λ c f, ⟨c • f, c • f.linear, λ p v, by simp [smul_add]⟩,
  one_smul := λ f, ext $ λ p, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ p, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ p, smul_add _ _ _,
  smul_zero := λ c, ext $ λ p, smul_zero _,
  add_smul := λ c₁ c₂ f, ext $ λ p, add_smul _ _ _,
  zero_smul := λ f, ext $ λ p, zero_smul _ _ }

@[simp] lemma coe_smul (c : k) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • f := rfl

/-- `homothety c r` is the homothety about `c` with scale factor `r`. -/
def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

lemma homothety_def (c : P1) (r : k) :
  homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
rfl

lemma homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c := rfl

@[simp] lemma homothety_one (c : P1) : homothety c (1:k) = id k P1 :=
by { ext p, simp [homothety_apply] }

lemma homothety_mul (c : P1) (r₁ r₂ : k) :
  homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
by { ext p, simp [homothety_apply, mul_smul] }

@[simp] lemma homothety_zero (c : P1) : homothety c (0:k) = const k P1 c :=
by { ext p, simp [homothety_apply] }

@[simp] lemma homothety_add (c : P1) (r₁ r₂ : k) :
  homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ :=
by simp only [homothety_def, add_smul, vadd_assoc]

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothety_hom (c : P1) : k →* P1 →ᵃ[k] P1 :=
⟨homothety c, homothety_one c, homothety_mul c⟩

@[simp] lemma coe_homothety_hom (c : P1) : ⇑(homothety_hom c : k →* _) = homothety c := rfl

/-- `homothety` as an affine map. -/
def homothety_affine (c : P1) : k →ᵃ[k] (P1 →ᵃ[k] P1) :=
⟨homothety c, (linear_map.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
  function.swap (homothety_add c)⟩

@[simp] lemma coe_homothety_affine (c : P1) :
  ⇑(homothety_affine c : k →ᵃ[k] _) = homothety c :=
rfl

end affine_map
