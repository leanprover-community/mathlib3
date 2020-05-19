/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.group.basic

/-!
# Torsors of additive commutative group actions

This file defines torsors of additive commutative group actions.

## Notations

The group elements are referred to as vectors and the elements they
act on are referred to as points, reflecting the use case of affine
spaces.  This file defines the notation `+ᵥ` for adding a vector to a
point and `-ᵥ` for subtracting two points to produce a vector.

## Implementation notes

It may be appropriate to refactor in future as a special case of
torsors of additive group actions, in terms of the general definition
of group actions (currently mathlib only has multiplicative group
actions).  The variable `V` is an explicit rather than implicit
argument to lemmas because otherwise the elaborator has problems
inferring appropriate types and type class instances.

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

/-- Type class for the `+ᵥ` and `-ᵥ` notation. -/
class has_vadd (V : Type*) (P : Type*) :=
(vadd : V → P → P)
(vsub : P → P → V)

infix `+ᵥ`:65 := has_vadd.vadd
infix `-ᵥ`:65 := has_vadd.vsub

section prio
set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true
/-- An `add_comm_torsor V P` gives a structure to the nonempty type
`P`, acted on by an `add_comm_group V` with a transitive and free
action given by the `+ᵥ` operation and a corresponding subtraction
given by the `-ᵥ` operation. In the case of a vector space, it is an
affine space.  (The result of adding a zero vector does not need to be
included here because it is deduced below from the other axioms.) -/
class add_comm_torsor (V : Type*) (P : Type*) [add_comm_group V] [nonempty P]
  extends has_vadd V P :=
(vadd_assoc' : ∀ (v1 v2 : V) (p : P), v1 +ᵥ (v2 +ᵥ p) = (v1 + v2) +ᵥ p)
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : V) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (v : V) (p : P), v +ᵥ p -ᵥ p = v)
end prio

/-- An `add_comm_group V` is a torsor for itself. -/
instance add_comm_group_is_add_comm_torsor (V : Type*) [nonempty V] [add_comm_group V] :
  add_comm_torsor V V :=
{ vadd := has_add.add,
  vsub := has_sub.sub,
  vadd_assoc' := λ a b c, (add_assoc a b c).symm,
  vsub_vadd' := sub_add_cancel,
  vadd_vsub' := add_sub_cancel }

namespace add_comm_torsor

variables (V : Type*) {P : Type*} [add_comm_group V] [nonempty P] [S : add_comm_torsor V P]
include S

/-- Adding two vectors to a point produces the same result as adding
their sum. -/
lemma vadd_assoc (v1 v2 : V) (p : P) : v1 +ᵥ (v2 +ᵥ p) = (v1 + v2) +ᵥ p :=
vadd_assoc' v1 v2 p

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vsub_vadd (p1 p2 : P) : (p1 -ᵥ p2 : V) +ᵥ p2 = p1 :=
vsub_vadd' p1 p2

/-- Adding a vector then subtracting the original point produces that
vector. -/
@[simp] lemma vadd_vsub (v : V) (p : P) : v +ᵥ p -ᵥ p = v :=
vadd_vsub' v p

/-- Adding two vectors to a point produces the same result in either
order. -/
lemma vadd_comm (p : P) (v1 v2 : V) : v1 +ᵥ (v2 +ᵥ p) = v2 +ᵥ (v1 +ᵥ p) :=
by rw [vadd_assoc, vadd_assoc, add_comm]

/-- If the same point added to two vectors produces equal results,
those vectors are equal. -/
lemma vadd_cancel_right (v1 v2 : V) (p : P) (h : v1 +ᵥ p = v2 +ᵥ p) : v1 = v2 :=
by rw [←vadd_vsub V v1, h, vadd_vsub]

/-- Adding the zero vector to a point gives the same point. -/
@[simp] lemma zero_vadd (p : P) : (0 : V) +ᵥ p = p :=
begin
  have h : (p -ᵥ ((0 : V) +ᵥ p)) +ᵥ ((0 : V) +ᵥ ((0 : V) +ᵥ p)) =
    (p -ᵥ ((0 : V) +ᵥ p)) +ᵥ ((0 : V) +ᵥ p),
  { rw [vadd_assoc V (0 : V) (0 : V) p, add_zero] },
  rwa [vsub_vadd, vadd_comm V ((0 : V) +ᵥ p), vsub_vadd] at h
end

/-- Adding a vector to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
vector. -/
lemma vadd_vsub_comm (v : V) (p1 p2 : P) : v +ᵥ p1 -ᵥ p2 = v + (p1 -ᵥ p2) :=
begin
  apply vadd_cancel_right V _ _ p2,
  rw [vsub_vadd, ←vadd_assoc, vsub_vadd]
end

/-- Subtracting the result of adding a vector produces the same result
as subtracting the points and subtracting that vector. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (v : V) : p1 -ᵥ (v +ᵥ p2) = (p1 -ᵥ p2) - v :=
begin
  apply vadd_cancel_right V _ _ (v +ᵥ p2),
  rw [vsub_vadd, vadd_comm, vadd_assoc, add_comm, sub_add_cancel, vsub_vadd]
end

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : V) :=
by rw [←add_zero (p -ᵥ p : V), add_comm, ←vadd_vsub_comm, vadd_vsub]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : V)) : p1 = p2 :=
by rw [←vsub_vadd V p1 p2, h, zero_vadd]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
lemma vsub_eq_zero_iff_eq (p1 p2 : P) : p1 -ᵥ p2 = (0 : V) ↔ p1 = p2 :=
iff.intro (eq_of_vsub_eq_zero V) (λ h, h ▸ vsub_self V _)

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
lemma vsub_rev_eq_neg_vsub (p1 p2 : P) : (p2 -ᵥ p1 : V) = -(p1 -ᵥ p2) :=
begin
  symmetry,
  apply neg_eq_of_add_eq_zero,
  apply vadd_cancel_right V _ _ p1,
  rw [zero_vadd, ←vadd_assoc, vsub_vadd, vsub_vadd]
end

/-- If the same vector added to two points produces equal results,
those points are equal. -/
lemma vadd_cancel_left (p1 p2 : P) (v : V) (h : v +ᵥ p1 = v +ᵥ p2) : p1 = p2 :=
begin
  have h2 : -v +ᵥ (v +ᵥ p1) = -v +ᵥ (v +ᵥ p2), { rw h },
  rwa [vadd_assoc, vadd_assoc, add_left_neg, zero_vadd, zero_vadd] at h2
end

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma vsub_add_vsub_cancel (p1 p2 p3 : P) : (p1 -ᵥ p2 : V) + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_cancel_right V _ _ p3,
  rw [←vadd_assoc, vsub_vadd, vsub_vadd, vsub_vadd]
end

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_right (p1 p2 p3 : P) :
  (p1 -ᵥ p3 : V) - (p2 -ᵥ p3) = (p1 -ᵥ p2) :=
by rw [←vsub_vadd_eq_vsub_sub, vsub_vadd]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_left (p1 p2 p3 : P) :
  (p3 -ᵥ p2 : V) - (p3 -ᵥ p1) = (p1 -ᵥ p2) :=
by rw [sub_eq_add_neg, ←vsub_rev_eq_neg_vsub, add_comm, vsub_add_vsub_cancel]

/-- The pairwise differences of a set of points. -/
def vsub_set (s : set P) : set V := {v | ∃ x ∈ s, ∃ y ∈ s, v = x -ᵥ y}

end add_comm_torsor
