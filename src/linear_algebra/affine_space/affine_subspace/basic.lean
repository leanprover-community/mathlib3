/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.set.intervals.unordered_interval
import linear_algebra.affine_space.affine_subspace.lattice

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

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

## Implementation notes

`out_param` is used in the definiton of `add_torsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes using it, to
be added as implicit arguments to individual lemmas.  As for modules, `k` is an explicit argument
rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results.
Those depending on analysis or topology are defined elsewhere; see
`analysis.normed_space.add_torsor` and `topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

noncomputable theory
open_locale big_operators classical affine

open set

namespace affine_subspace

variables (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

variables {k P}

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.) -/
def direction (s : affine_subspace k P) : submodule k V := vector_span k (s : set P)

/-- The direction equals the `vector_span`. -/
lemma direction_eq_vector_span (s : affine_subspace k P) :
  s.direction = vector_span k (s : set P) :=
rfl

/-- Alternative definition of the direction when the affine subspace
is nonempty.  This is defined so that the order on submodules (as used
in the definition of `submodule.span`) can be used in the proof of
`coe_direction_eq_vsub_set`, and is not intended to be used beyond
that proof. -/
def direction_of_nonempty {s : affine_subspace k P} (h : s ≠ ⊥) :
  submodule k V :=
{ carrier := (s : set P) -ᵥ s,
  zero_mem' := begin
    cases affine_subspace.ne_bot_iff.mp h with p hp,
    exact (vsub_self p) ▸ vsub_mem_vsub hp hp
  end,
  add_mem' := begin
    intros a b ha hb,
    rcases ha with ⟨p1, p2, hp1, hp2, rfl⟩,
    rcases hb with ⟨p3, p4, hp3, hp4, rfl⟩,
    rw [←vadd_vsub_assoc],
    refine vsub_mem_vsub _ hp4,
    convert s.smul_vsub_vadd_mem 1 hp1 hp2 hp3,
    rw one_smul
  end,
  smul_mem' := begin
    intros c v hv,
    rcases hv with ⟨p1, p2, hp1, hp2, rfl⟩,
    rw [←vadd_vsub (c • (p1 -ᵥ p2)) p2],
    refine vsub_mem_vsub _ hp2,
    exact s.smul_vsub_vadd_mem c hp1 hp2 hp2
  end }

/-- `direction_of_nonempty` gives the same submodule as
`direction`. -/
lemma direction_of_nonempty_eq_direction {s : affine_subspace k P} (h : s ≠ ⊥) :
  direction_of_nonempty h = s.direction :=
le_antisymm (vsub_set_subset_vector_span k s) (submodule.span_le.2 set.subset.rfl)

/-- The set of vectors in the direction of a nonempty affine subspace
is given by `vsub_set`. -/
lemma coe_direction_eq_vsub_set {s : affine_subspace k P} (h : s ≠ ⊥) :
  (s.direction : set V) = (s : set P) -ᵥ s :=
direction_of_nonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and
only if it is the subtraction of two vectors in the subspace. -/
lemma mem_direction_iff_eq_vsub {s : affine_subspace k P} (h : s ≠ ⊥) (v : V) :
  v ∈ s.direction ↔ ∃ p1 ∈ s, ∃ p2 ∈ s, v = p1 -ᵥ p2 :=
begin
  rw [←set_like.mem_coe, coe_direction_eq_vsub_set h],
  exact ⟨λ ⟨p1, p2, hp1, hp2, hv⟩, ⟨p1, hp1, p2, hp2, hv.symm⟩,
         λ ⟨p1, hp1, p2, hp2, hv⟩, ⟨p1, p2, hp1, hp2, hv.symm⟩⟩
end

/-- Adding a vector in the direction to a point in the subspace
produces a point in the subspace. -/
lemma vadd_mem_of_mem_direction {s : affine_subspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s :=
begin
  have := affine_subspace.ne_bot_iff.mpr ⟨p, hp⟩,
  rw mem_direction_iff_eq_vsub this at hv,
  rcases hv with ⟨p1, hp1, p2, hp2, hv⟩,
  rw hv,
  convert s.smul_vsub_vadd_mem 1 hp1 hp2 hp,
  rw one_smul
end

/-- Subtracting two points in the subspace produces a vector in the
direction. -/
lemma vsub_mem_direction {s : affine_subspace k P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  (p1 -ᵥ p2) ∈ s.direction :=
vsub_mem_vector_span k hp1 hp2

/-- Adding a vector to a point in a subspace produces a point in the
subspace if and only if the vector is in the direction. -/
lemma vadd_mem_iff_mem_direction {s : affine_subspace k P} (v : V) {p : P} (hp : p ∈ s) :
  v +ᵥ p ∈ s ↔ v ∈ s.direction :=
⟨λ h, by simpa using vsub_mem_direction h hp, λ h, vadd_mem_of_mem_direction h hp⟩

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
right. -/
lemma coe_direction_eq_vsub_set_right {s : affine_subspace k P} {p : P} (hp : p ∈ s) :
  (s.direction : set V) = (-ᵥ p) '' s :=
begin
  have := affine_subspace.ne_bot_iff.mpr ⟨p, hp⟩,
  rw coe_direction_eq_vsub_set this,
  refine le_antisymm _ _,
  { rintros v ⟨p1, p2, hp1, hp2, rfl⟩,
    exact ⟨p1 -ᵥ p2 +ᵥ p,
           vadd_mem_of_mem_direction (vsub_mem_direction hp1 hp2) hp,
           (vadd_vsub _ _)⟩ },
  { rintros v ⟨p2, hp2, rfl⟩,
    exact ⟨p2, p, hp2, hp, rfl⟩ }
end

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
left. -/
lemma coe_direction_eq_vsub_set_left {s : affine_subspace k P} {p : P} (hp : p ∈ s) :
  (s.direction : set V) = (-ᵥ) p '' s :=
begin
  ext v,
  rw [set_like.mem_coe, ←submodule.neg_mem_iff, ←set_like.mem_coe,
      coe_direction_eq_vsub_set_right hp, set.mem_image_iff_bex, set.mem_image_iff_bex],
  conv_lhs { congr, funext, rw [←neg_vsub_eq_vsub_rev, neg_inj] }
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the right. -/
lemma mem_direction_iff_eq_vsub_right {s : affine_subspace k P} {p : P} (hp : p ∈ s) (v : V) :
  v ∈ s.direction ↔ ∃ p2 ∈ s, v = p2 -ᵥ p :=
begin
  rw [←set_like.mem_coe, coe_direction_eq_vsub_set_right hp],
  exact ⟨λ ⟨p2, hp2, hv⟩, ⟨p2, hp2, hv.symm⟩, λ ⟨p2, hp2, hv⟩, ⟨p2, hp2, hv.symm⟩⟩
end

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the left. -/
lemma mem_direction_iff_eq_vsub_left {s : affine_subspace k P} {p : P} (hp : p ∈ s) (v : V) :
  v ∈ s.direction ↔ ∃ p2 ∈ s, v = p -ᵥ p2 :=
begin
  rw [←set_like.mem_coe, coe_direction_eq_vsub_set_left hp],
  exact ⟨λ ⟨p2, hp2, hv⟩, ⟨p2, hp2, hv.symm⟩, λ ⟨p2, hp2, hv⟩, ⟨p2, hp2, hv.symm⟩⟩
end

/-- Given a point in an affine subspace, a result of subtracting that
point on the right is in the direction if and only if the other point
is in the subspace. -/
lemma vsub_right_mem_direction_iff_mem {s : affine_subspace k P} {p : P} (hp : p ∈ s) (p2 : P) :
  p2 -ᵥ p ∈ s.direction ↔ p2 ∈ s :=
begin
  rw mem_direction_iff_eq_vsub_right hp,
  simp
end

/-- Given a point in an affine subspace, a result of subtracting that
point on the left is in the direction if and only if the other point
is in the subspace. -/
lemma vsub_left_mem_direction_iff_mem {s : affine_subspace k P} {p : P} (hp : p ∈ s) (p2 : P) :
  p -ᵥ p2 ∈ s.direction ↔ p2 ∈ s :=
begin
  rw mem_direction_iff_eq_vsub_left hp,
  simp
end

/-- Two affine subspaces with the same direction and nonempty
intersection are equal. -/
lemma ext_of_direction_eq {s1 s2 : affine_subspace k P} (hd : s1.direction = s2.direction)
    (hn : s1 ⊓ s2 ≠ ⊥) : s1 = s2 :=
begin
  ext p,
  rcases affine_subspace.ne_bot_iff.mp hn with ⟨n, hn⟩,
  have hq1 := mem_of_mem_inter_left hn,
  have hq2 := set.mem_of_mem_inter_right hn,
  split,
  { intro hp,
    rw ←vsub_vadd p n,
    refine vadd_mem_of_mem_direction _ hq2,
    rw ←hd,
    exact vsub_mem_direction hp hq1 },
  { intro hp,
    rw ←vsub_vadd p n,
    refine vadd_mem_of_mem_direction _ hq1,
    rw hd,
    exact vsub_mem_direction hp hq2 }
end

instance to_add_torsor (s : affine_subspace k P) [nonempty s] : add_torsor s.direction s :=
{ vadd := λ a b, ⟨(a:V) +ᵥ (b:P), vadd_mem_of_mem_direction a.2 b.2⟩,
  zero_vadd := by simp,
  add_vadd := λ a b c, by { ext, apply add_vadd },
  vsub := λ a b, ⟨(a:P) -ᵥ (b:P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2 ⟩,
  nonempty := by apply_instance,
  vsub_vadd' := λ a b, by { ext, apply add_torsor.vsub_vadd' },
  vadd_vsub' := λ a b, by { ext, apply add_torsor.vadd_vsub' } }

@[simp, norm_cast] lemma coe_vsub (s : affine_subspace k P) [nonempty s] (a b : s) :
  ↑(a -ᵥ b) = (a:P) -ᵥ (b:P) :=
rfl

@[simp, norm_cast] lemma coe_vadd (s : affine_subspace k P) [nonempty s] (a : s.direction) (b : s) :
  ↑(a +ᵥ b) = (a:V) +ᵥ (b:P) :=
rfl

/-- Two affine subspaces with nonempty intersection are equal if and
only if their directions are equal. -/
lemma eq_iff_direction_eq_of_mem {s₁ s₂ : affine_subspace k P} {p : P} (h₁ : p ∈ s₁)
  (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction :=
⟨λ h, h ▸ rfl, λ h, ext_of_direction_eq h $ affine_subspace.ne_bot_iff.mpr ⟨p, h₁, h₂⟩⟩

/-- Construct an affine subspace from a point and a direction. -/
def mk' (p : P) (direction : submodule k V) : affine_subspace k P :=
{ carrier := {q | ∃ v ∈ direction, q = v +ᵥ p},
  smul_vsub_vadd_mem := λ c p1 p2 p3 hp1 hp2 hp3, begin
    rcases hp1 with ⟨v1, hv1, hp1⟩,
    rcases hp2 with ⟨v2, hv2, hp2⟩,
    rcases hp3 with ⟨v3, hv3, hp3⟩,
    use [c • (v1 - v2) + v3,
         direction.add_mem (direction.smul_mem c (direction.sub_mem hv1 hv2)) hv3],
    simp [hp1, hp2, hp3, vadd_vadd]
  end }

/-- An affine subspace constructed from a point and a direction contains
that point. -/
lemma self_mem_mk' (p : P) (direction : submodule k V) :
  p ∈ mk' p direction :=
⟨0, ⟨direction.zero_mem, (zero_vadd _ _).symm⟩⟩

/-- An affine subspace constructed from a point and a direction contains
the result of adding a vector in that direction to that point. -/
lemma vadd_mem_mk' {v : V} (p : P) {direction : submodule k V} (hv : v ∈ direction) :
  v +ᵥ p ∈ mk' p direction :=
⟨v, hv, rfl⟩

/-- An affine subspace constructed from a point and a direction is
nonempty. -/
lemma mk'_ne_bot (p : P) (direction : submodule k V) : mk' p direction ≠ ⊥ :=
affine_subspace.ne_bot_iff.mpr ⟨p, self_mem_mk' p direction⟩

/-- The direction of an affine subspace constructed from a point and a
direction. -/
@[simp] lemma direction_mk' (p : P) (direction : submodule k V) :
  (mk' p direction).direction = direction :=
begin
  ext v,
  rw mem_direction_iff_eq_vsub (mk'_ne_bot _ _),
  split,
  { rintros ⟨p1, ⟨v1, hv1, hp1⟩, p2, ⟨v2, hv2, hp2⟩, hv⟩,
    rw [hv, hp1, hp2, vadd_vsub_vadd_cancel_right],
    exact direction.sub_mem  hv1 hv2 },
  { exact λ hv, ⟨v +ᵥ p, vadd_mem_mk' _ hv, p,
                 self_mem_mk' _ _, (vadd_vsub _ _).symm⟩ }
end

/-- Constructing an affine subspace from a point in a subspace and
that subspace's direction yields the original subspace. -/
@[simp] lemma mk'_eq {s : affine_subspace k P} {p : P} (hp : p ∈ s) : mk' p s.direction = s :=
ext_of_direction_eq (direction_mk' p s.direction) $
  affine_subspace.ne_bot_iff.mpr ⟨p, set.mem_inter (self_mem_mk' _ _) hp⟩

/-- If an affine subspace contains a set of points, it contains the
`span_points` of that set. -/
lemma span_points_subset_coe_of_subset_coe {s : set P} {s1 : affine_subspace k P} (h : s ⊆ s1) :
  span_points k s ⊆ s1 :=
begin
  rintros p ⟨p1, hp1, v, hv, hp⟩,
  rw hp,
  have hp1s1 : p1 ∈ (s1 : set P) := set.mem_of_mem_of_subset hp1 h,
  refine vadd_mem_of_mem_direction _ hp1s1,
  have hs : vector_span k s ≤ s1.direction := vector_span_mono k h,
  rw set_like.le_def at hs,
  rw ←set_like.mem_coe,
  exact set.mem_of_mem_of_subset hv hs
end

end affine_subspace

lemma affine_map.line_map_mem
  {k V P : Type*} [ring k] [add_comm_group V] [module k V] [add_torsor V P]
  {s : affine_subspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ ∈ s) (h₁ : p₁ ∈ s) :
  affine_map.line_map p₀ p₁ c ∈ s :=
begin
  rw affine_map.line_map_apply,
  exact s.smul_vsub_vadd_mem c h₁ h₀ h₀,
end

section affine_span

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

/-- The affine span of a set of points is the smallest affine subspace
containing those points. (Actually defined here in terms of spans in
modules.) -/
def affine_span (s : set P) : affine_subspace k P :=
{ carrier := span_points k s,
  smul_vsub_vadd_mem := λ c p1 p2 p3 hp1 hp2 hp3,
    vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k hp3
      ((vector_span k s).smul_mem c
        (vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k hp1 hp2)) }

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
    rw [hp1, hp3, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, set_like.mem_coe],
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
  (hd : s₁.direction = s₂.direction) (hn : s₁ ≠ ⊥) (hle : s₁ ≤ s₂) :
  s₁ = s₂ :=
begin
  cases affine_subspace.ne_bot_iff.mp hn with p hp,
  refine ext_of_direction_eq hd _,
  rw affine_subspace.ne_bot_iff,
  exact ⟨p, hp, hle hp⟩,
end

variables (k V)

/-- The affine span is the `Inf` of subspaces containing the given
points. -/
lemma affine_span_eq_Inf (s : set P) : affine_span k s = Inf {s' | s ⊆ s'} :=
le_antisymm (span_points_subset_coe_of_subset_coe $ set.subset_Inter₂ $ λ _, id)
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
affine_subspace.eq_top_iff.2 (λ x, subset_span_points k (set.univ : set P) (mem_univ x))

variables {k V P}

lemma _root_.affine_span_le {s : set P} {Q : affine_subspace k P} :
  affine_span k s ≤ Q ↔ s ⊆ (Q : set P) :=
(affine_subspace.gi k V P).gc _ _

variables (k V) {P}

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

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp] lemma direction_top : (⊤ : affine_subspace k P).direction = ⊤ :=
begin
  cases S.nonempty with p,
  ext v,
  refine ⟨imp_intro submodule.mem_top, λ hv, _⟩,
  have hpv : (v +ᵥ p -ᵥ p : V) ∈ (⊤ : affine_subspace k P).direction :=
    vsub_mem_direction mem_top mem_top,
  rwa vadd_vsub at hpv
end

lemma nonempty_of_affine_span_eq_top {s : set P} (h : affine_span k s = ⊤) : s.nonempty :=
begin
  rw ← set.ne_empty_iff_nonempty,
  rintros rfl,
  rw affine_subspace.span_empty at h,
  exact bot_ne_top h,
end

/-- If the affine span of a set is `⊤`, then the vector span of the same set is the `⊤`. -/
lemma vector_span_eq_top_of_affine_span_eq_top {s : set P} (h : affine_span k s = ⊤) :
  vector_span k s = ⊤ :=
by rw [← direction_affine_span, h, direction_top]

/-- For a nonempty set, the affine span is `⊤` iff its vector span is `⊤`. -/
lemma affine_span_eq_top_iff_vector_span_eq_top_of_nonempty {s : set P} (hs : s.nonempty) :
  affine_span k s = ⊤ ↔ vector_span k s = ⊤ :=
begin
  refine ⟨vector_span_eq_top_of_affine_span_eq_top k V P, _⟩,
  intros h,
  suffices : nonempty (affine_span k s),
  { obtain ⟨p, hp : p ∈ affine_span k s⟩ := this,
    rw [eq_iff_direction_eq_of_mem hp mem_top, direction_affine_span, h, direction_top] },
  obtain ⟨x, hx⟩ := hs,
  exact ⟨⟨x, mem_affine_span k hx⟩⟩,
end

/-- For a non-trivial space, the affine span of a set is `⊤` iff its vector span is `⊤`. -/
lemma affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial {s : set P} [nontrivial P] :
  affine_span k s = ⊤ ↔ vector_span k s = ⊤ :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { simp [hs, subsingleton_iff_bot_eq_top, add_torsor.subsingleton_iff V P, not_subsingleton], },
  { rw affine_span_eq_top_iff_vector_span_eq_top_of_nonempty k V P hs, },
end

lemma card_pos_of_affine_span_eq_top {ι : Type*} [fintype ι] {p : ι → P}
  (h : affine_span k (range p) = ⊤) :
  0 < fintype.card ι :=
begin
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affine_span_eq_top k V P h,
  exact fintype.card_pos_iff.mpr ⟨i⟩,
end

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp] lemma direction_bot : (⊥ : affine_subspace k P).direction = ⊥ :=
by rw [direction_eq_vector_span, bot_coe, vector_span_def, vsub_empty, submodule.span_empty]

variables {k V P}

@[simp] lemma coe_eq_bot_iff (Q : affine_subspace k P) : (Q : set P) = ∅ ↔ Q = ⊥ :=
coe_injective.eq_iff' bot_coe

@[simp] lemma coe_eq_univ_iff (Q : affine_subspace k P) : (Q : set P) = univ ↔ Q = ⊤ :=
coe_injective.eq_iff' top_coe

lemma nonempty_iff_ne_bot (Q : affine_subspace k P) : (Q : set P).nonempty ↔ Q ≠ ⊥ :=
by { rw ← ne_empty_iff_nonempty, exact not_congr Q.coe_eq_bot_iff }

lemma eq_bot_or_nonempty (Q : affine_subspace k P) : Q = ⊥ ∨ (Q : set P).nonempty :=
by { rw nonempty_iff_ne_bot, apply eq_or_ne }

lemma subsingleton_of_subsingleton_span_eq_top {s : set P} (h₁ : s.subsingleton)
  (h₂ : affine_span k s = ⊤) : subsingleton P :=
begin
  obtain ⟨p, hp⟩ := affine_subspace.nonempty_of_affine_span_eq_top k V P h₂,
  have : s = {p}, { exact subset.antisymm (λ q hq, h₁ hq hp) (by simp [hp]), },
  rw [this, ← affine_subspace.ext_iff, affine_subspace.coe_affine_span_singleton,
    affine_subspace.top_coe, eq_comm, ← subsingleton_iff_singleton (mem_univ _)] at h₂,
  exact subsingleton_of_univ_subsingleton h₂,
end

lemma eq_univ_of_subsingleton_span_eq_top {s : set P} (h₁ : s.subsingleton)
  (h₂ : affine_span k s = ⊤) : s = (univ : set P) :=
begin
  obtain ⟨p, hp⟩ := affine_subspace.nonempty_of_affine_span_eq_top k V P h₂,
  have : s = {p}, { exact subset.antisymm (λ q hq, h₁ hq hp) (by simp [hp]), },
  rw [this, eq_comm, ← subsingleton_iff_singleton (mem_univ p), subsingleton_univ_iff],
  exact subsingleton_of_subsingleton_span_eq_top h₁ h₂,
end

/-- A nonempty affine subspace is `⊤` if and only if its direction is
`⊤`. -/
@[simp] lemma direction_eq_top_iff_of_nonempty {s : affine_subspace k P}
  (h : s ≠ ⊥) : s.direction = ⊤ ↔ s = ⊤ :=
begin
  split,
  { intro hd,
    rw ←direction_top k V P at hd,
    refine ext_of_direction_eq hd _,
    simp [h] },
  { rintro rfl,
    simp }
end

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
      ←vadd_mem_iff_mem_direction v (mem_inf.2 ⟨h₁, h₂⟩), mem_inf]
end

/-- If two affine subspaces have a point in their inf, the direction
of their inf equals the inf of their directions. -/
lemma direction_inf_of_mem_inf {s₁ s₂ : affine_subspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
  (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
direction_inf_of_mem (mem_inf.1 h).1 (mem_inf.1 h).2

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
    (hn : s1 ≠ ⊥) : s1.direction < s2.direction :=
begin
  cases affine_subspace.ne_bot_iff.mp hn with p hp,
  rw lt_iff_le_and_exists at h,
  rcases h with ⟨hle, p2, hp2, hp2s1⟩,
  rw set_like.lt_iff_le_and_exists,
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
    (h1 : s1 ≠ ⊥) (h2 : s2 ≠ ⊥) (he : (s1 ∩ s2 : set P) = ∅) :
  s1.direction ⊔ s2.direction < (s1 ⊔ s2).direction :=
begin
  cases affine_subspace.ne_bot_iff.mp h1 with p1 hp1,
  cases affine_subspace.ne_bot_iff.mp h2 with p2 hp2,
  rw set_like.lt_iff_le_and_exists,
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
    (h1 : s1 ≠ ⊥) (h2 : s2 ≠ ⊥)
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
    (h1 : s1 ≠ ⊥) (h2 : s2 ≠ ⊥) (hd : is_compl s1.direction s2.direction) :
    ∃ p, (s1 : set P) ∩ s2 = {p} :=
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

lemma affine_span_union (s₁ s₂ : affine_subspace k P) :
  affine_span k (s₁ ∪ s₂ : set P) = s₁ ⊔ s₂ :=
begin
  rw ← affine_span_coe (affine_span k (s₁ ∪ s₂ : set P)),
  rw span_union,
  simp only [affine_span_coe],
end

end affine_subspace

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open affine_subspace set

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left. -/
lemma vector_span_eq_span_vsub_set_left {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ) p '' s) :=
begin
  rw vector_span_def,
  refine le_antisymm _ (submodule.span_mono _),
  { rw submodule.span_le,
    rintros v ⟨p1, p2, hp1, hp2, hv⟩,
    rw ←vsub_sub_vsub_cancel_left p1 p2 p at hv,
    rw [←hv, set_like.mem_coe, submodule.mem_span],
    exact λ m hm, submodule.sub_mem _ (hm ⟨p2, hp2, rfl⟩) (hm ⟨p1, hp1, rfl⟩) },
  { rintros v ⟨p2, hp2, hv⟩,
    exact ⟨p, p2, hp, hp2, hv⟩ }
end

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right. -/
lemma vector_span_eq_span_vsub_set_right {s : set P} {p : P} (hp : p ∈ s) :
  vector_span k s = submodule.span k ((-ᵥ p) '' s) :=
begin
  rw vector_span_def,
  refine le_antisymm _ (submodule.span_mono _),
  { rw submodule.span_le,
    rintros v ⟨p1, p2, hp1, hp2, hv⟩,
    rw ←vsub_sub_vsub_cancel_right p1 p2 p at hv,
    rw [←hv, set_like.mem_coe, submodule.mem_span],
    exact λ m hm, submodule.sub_mem _ (hm ⟨p1, hp1, rfl⟩) (hm ⟨p2, hp2, rfl⟩) },
  { rintros v ⟨p2, hp2, hv⟩,
    exact ⟨p2, p, hp2, hp, hv⟩ }
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

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from
itself. -/
lemma vector_span_eq_span_vsub_finset_right_ne {s : finset P} {p : P} (hp : p ∈ s) :
  vector_span k (s : set P) = submodule.span k ((s.erase p).image (-ᵥ p)) :=
by simp [vector_span_eq_span_vsub_set_right_ne _ (finset.mem_coe.mpr hp)]

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

/-- The affine span of a nonempty set is nonempty. -/
instance {s : set P} [nonempty s] : nonempty (affine_span k s) :=
((affine_span_nonempty k s).mpr (nonempty_subtype.mp ‹_›)).to_subtype

variables {k}

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together
with those vectors added to `p`, spans `P`. -/
lemma affine_span_singleton_union_vadd_eq_top_of_span_eq_top {s : set V} (p : P)
    (h : submodule.span k (set.range (coe : s → V)) = ⊤) :
  affine_span k ({p} ∪ (λ v, v +ᵥ p) '' s) = ⊤ :=
begin
  refine ext_of_direction_eq _ _,
  { rw [direction_affine_span, direction_top],
    rw vector_span_eq_span_vsub_set_right k
      ((set.mem_union_left _ (set.mem_singleton _)) : p ∈ _),
    rw _root_.eq_top_iff, rw ← h,
    apply submodule.span_mono,
    rintros v ⟨v', rfl⟩,
    use (v' : V) +ᵥ p,
    simp, },
  rw affine_subspace.ne_bot_iff,
  refine ⟨p, mem_inf.mpr ⟨mem_affine_span k $ mem_union_left _ (mem_singleton p), mem_top⟩⟩,
end

variables (k)

/-- `affine_span` is monotone. -/
@[mono]
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
  (s1 ⊔ s2).direction = s1.direction ⊔ s2.direction ⊔ k ∙ (p2 -ᵥ p1) :=
begin
  refine le_antisymm _ _,
  { rw ← affine_span_union,
    rw ←mem_coe at hp1,
    rw [direction_affine_span, vector_span_eq_span_vsub_set_right k (set.mem_union_left _ hp1),
        submodule.span_le],
    rintros v ⟨p3, hp3, rfl⟩,
    cases hp3,
    { rw [sup_assoc, sup_comm, set_like.mem_coe, submodule.mem_sup],
      use [0, submodule.zero_mem _, p3 -ᵥ p1, vsub_mem_direction hp3 hp1],
      rw zero_add },
    { rw [sup_assoc, set_like.mem_coe, submodule.mem_sup],
      use [0, submodule.zero_mem _, p3 -ᵥ p1],
      rw [and_comm, zero_add],
      use rfl,
      rw [←vsub_add_vsub_cancel p3 p2 p1, submodule.mem_sup],
      use [p3 -ᵥ p2, vsub_mem_direction hp3 hp2, p2 -ᵥ p1,
           submodule.mem_span_singleton_self _] } },
  { refine sup_le (sup_direction_le _ _) _,
    rw [direction_eq_vector_span, vector_span_def],
    refine Inf_le_Inf (λ p hp, _),
    rw mem_set_of_eq at hp,
    rw mem_set_of_eq,
    refine set.subset.trans _ hp,
    refine set.singleton_subset_iff.2 (vsub_mem_vsub (mem_sup_right hp2) (mem_sup_left hp1)), },
end

/-- The direction of the span of the result of adding a point to a
nonempty affine subspace is the sup of the direction of that subspace
and of any one difference between that point and a point in the
subspace. -/
lemma direction_affine_span_insert {s : affine_subspace k P} {p1 p2 : P} (hp1 : p1 ∈ s) :
  (affine_span k (insert p2 (s : set P))).direction = submodule.span k {p2 -ᵥ p1} ⊔ s.direction :=
begin
  rw [sup_comm, ←set.union_singleton, ←coe_affine_span_singleton k V p2, affine_span_union],
  rw [direction_sup hp1 (mem_affine_span k (set.mem_singleton _)), direction_affine_span],
  simp only [vector_span_singleton, sup_bot_eq]
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
    rw [←sub_eq_zero, ←vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp,
    rw [hp, vadd_vadd] },
  { rintros ⟨r, p3, hp3, rfl⟩,
    use [r • (p2 -ᵥ p1), submodule.mem_span_singleton.2 ⟨r, rfl⟩, p3 -ᵥ p1,
         vsub_mem_direction hp3 hp1],
    rw [vadd_vsub_assoc, add_comm] }
end

end affine_subspace

section map_comap

variables {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [ring k]
variables [add_comm_group V₁] [module k V₁] [add_torsor V₁ P₁]
variables [add_comm_group V₂] [module k V₂] [add_torsor V₂ P₂]
variables [add_comm_group V₃] [module k V₃] [add_torsor V₃ P₃]
include V₁ V₂

section

variables (f : P₁ →ᵃ[k] P₂)

@[simp] lemma affine_map.vector_span_image_eq_submodule_map {s : set P₁} :
  submodule.map f.linear (vector_span k s) = vector_span k (f '' s) :=
by simp [f.image_vsub_image, vector_span_def]

namespace affine_subspace

/-- The image of an affine subspace under an affine map as an affine subspace. -/
def map (s : affine_subspace k P₁) : affine_subspace k P₂ :=
{ carrier := f '' s,
  smul_vsub_vadd_mem :=
    begin
      rintros t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩,
      use t • (p₁ -ᵥ p₂) +ᵥ p₃,
      suffices : t • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ s, { simp [this], },
      exact s.smul_vsub_vadd_mem t h₁ h₂ h₃,
    end }

@[simp] lemma coe_map (s : affine_subspace k P₁) : (s.map f : set P₂) = f '' s := rfl

@[simp] lemma mem_map {f : P₁ →ᵃ[k] P₂} {x : P₂} {s : affine_subspace k P₁} :
  x ∈ s.map f ↔ ∃ y ∈ s, f y = x := mem_image_iff_bex

@[simp] lemma map_bot : (⊥ : affine_subspace k P₁).map f = ⊥ :=
coe_injective $ image_empty f

omit V₂

@[simp] lemma map_id (s : affine_subspace k P₁) : s.map (affine_map.id k P₁) = s :=
coe_injective $ image_id _

include V₂ V₃

lemma map_map (s : affine_subspace k P₁) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
  (s.map f).map g = s.map (g.comp f) :=
coe_injective $ image_image _ _ _

omit V₃

@[simp] lemma map_direction (s : affine_subspace k P₁) :
  (s.map f).direction = s.direction.map f.linear :=
by simp [direction_eq_vector_span]

lemma map_span (s : set P₁) :
  (affine_span k s).map f = affine_span k (f '' s) :=
begin
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩, { simp, },
  apply ext_of_direction_eq,
  { simp [direction_affine_span], },
  { rw affine_subspace.ne_bot_iff,
    exact ⟨f p, mem_image_of_mem f (subset_affine_span k _ hp),
                subset_affine_span k _ (mem_image_of_mem f hp)⟩, },
end

end affine_subspace

namespace affine_map

@[simp] lemma map_top_of_surjective (hf : function.surjective f) : affine_subspace.map f ⊤ = ⊤ :=
begin
  rw ← affine_subspace.ext_iff,
  exact image_univ_of_surjective hf,
end

lemma span_eq_top_of_surjective {s : set P₁}
  (hf : function.surjective f) (h : affine_span k s = ⊤) :
  affine_span k (f '' s) = ⊤ :=
by rw [← affine_subspace.map_span, h, map_top_of_surjective f hf]

end affine_map

lemma affine_equiv.span_eq_top_iff {s : set P₁} (e : P₁ ≃ᵃ[k] P₂) :
  affine_span k s = ⊤ ↔ affine_span k (e '' s) = ⊤ :=
begin
  refine ⟨(e : P₁ →ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, _⟩,
  intros h,
  have : s = e.symm '' (e '' s), { simp [← image_comp], },
  rw this,
  exact (e.symm : P₂ →ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h,
end

end

namespace affine_subspace

/-- The preimage of an affine subspace under an affine map as an affine subspace. -/
def comap (f : P₁ →ᵃ[k] P₂) (s : affine_subspace k P₂) : affine_subspace k P₁ :=
{ carrier := f ⁻¹' s,
  smul_vsub_vadd_mem := λ t p₁ p₂ p₃ (hp₁ : f p₁ ∈ s) (hp₂ : f p₂ ∈ s) (hp₃ : f p₃ ∈ s),
    show f _ ∈ s, begin
      rw [affine_map.map_vadd, linear_map.map_smul, affine_map.linear_map_vsub],
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃,
    end }

@[simp] lemma coe_comap (f : P₁ →ᵃ[k] P₂) (s : affine_subspace k P₂) :
  (s.comap f : set P₁) = f ⁻¹' ↑s := rfl

@[simp] lemma mem_comap {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : affine_subspace k P₂} :
  x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_mono {f : P₁ →ᵃ[k] P₂} {s t : affine_subspace k P₂} : s ≤ t → s.comap f ≤ t.comap f :=
preimage_mono

@[simp] lemma comap_top {f : P₁ →ᵃ[k] P₂} : (⊤ : affine_subspace k P₂).comap f = ⊤ :=
by { rw ← ext_iff, exact preimage_univ, }

omit V₂

@[simp] lemma comap_id (s : affine_subspace k P₁) : s.comap (affine_map.id k P₁) = s :=
coe_injective rfl

include V₂ V₃

lemma comap_comap (s : affine_subspace k P₃) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
  (s.comap g).comap f = s.comap (g.comp f) :=
coe_injective rfl

omit V₃

-- lemmas about map and comap derived from the galois connection

lemma map_le_iff_le_comap {f : P₁ →ᵃ[k] P₂} {s : affine_subspace k P₁} {t : affine_subspace k P₂} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
image_subset_iff

lemma gc_map_comap (f : P₁ →ᵃ[k] P₂) : galois_connection (map f) (comap f) :=
λ _ _, map_le_iff_le_comap

lemma map_comap_le (f : P₁ →ᵃ[k] P₂) (s : affine_subspace k P₂) : (s.comap f).map f ≤ s :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : P₁ →ᵃ[k] P₂) (s : affine_subspace k P₁) : s ≤ (s.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_sup (s t : affine_subspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → affine_subspace k P₁) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (s t : affine_subspace k P₂) (f : P₁ →ᵃ[k] P₂) :
  (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(gc_map_comap f).u_inf

lemma comap_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → affine_subspace k P₂) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

end affine_subspace

end map_comap
