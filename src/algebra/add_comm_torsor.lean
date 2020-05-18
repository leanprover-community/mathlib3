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
(vadd : P → V → P)
(vsub : P → P → V)

infix `+ᵥ`:65 := has_vadd.vadd
infix `-ᵥ`:65 := has_vadd.vsub

section prio
set_option default_priority 100 -- see Note [default priority]
/-- An `add_comm_torsor V P` gives a structure to the nonempty type
`P`, acted on by an `add_comm_group V` with a transitive and free
action given by the `+ᵥ` operation and a corresponding subtraction
given by the `-ᵥ` operation. In the case of a vector space, it is an
affine space.  (The result of adding a zero vector does not need to be
included here because it is deduced below from the other axioms.) -/
class add_comm_torsor (V : Type*) (P : Type*) [add_comm_group V] [nonempty P]
    extends has_vadd V P :=
(vadd_assoc : ∀ (p : P) (v1 v2 : V), p +ᵥ v1 +ᵥ v2 = p +ᵥ (v1 + v2))
(vadd_vsub : ∀ (p1 p2 : P), p1 +ᵥ (p2 -ᵥ p1 : V) = p2)
(vsub_vadd : ∀ (p : P) (v : V), p +ᵥ v -ᵥ p = v)
end prio

/-- An `add_comm_group V` is a torsor for itself. -/
instance add_comm_group_has_vadd (V : Type*) [add_comm_group V] : has_vadd V V :=
{ vadd := has_add.add,
  vsub := has_sub.sub }
instance add_comm_group_is_add_comm_torsor (V : Type*) [nonempty V] [add_comm_group V] :
  add_comm_torsor V V :=
{ vadd_assoc := add_assoc,
  vadd_vsub := λ a b, add_eq_of_eq_sub' rfl,
  vsub_vadd := add_sub_cancel' }

namespace add_comm_torsor

variables (k : Type*) (V : Type*) {P : Type*} [add_comm_group V] [nonempty P]
          [S : add_comm_torsor V P]
include S

/-- Adding two vectors to a point produces the same result as adding
their sum. -/
lemma vadd_add_assoc (p : P) (v1 v2 : V) : p +ᵥ v1 +ᵥ v2 = p +ᵥ (v1 + v2) :=
add_comm_torsor.vadd_assoc p v1 v2

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vadd_vsub_self (p1 p2 : P) : p1 +ᵥ (p2 -ᵥ p1 : V) = p2 :=
add_comm_torsor.vadd_vsub p1 p2

/-- Adding a vector then subtracting the original point produces that
vector. -/
@[simp] lemma vsub_vadd_self (p : P) (v : V) : p +ᵥ v -ᵥ p = v :=
add_comm_torsor.vsub_vadd p v

/-- Adding two vectors to a point produces the same result in either
order. -/
lemma vadd_comm (p : P) (v1 v2 : V) : p +ᵥ v1 +ᵥ v2 = p +ᵥ v2 +ᵥ v1 :=
by rw [vadd_add_assoc V p v1 v2, vadd_add_assoc V p v2 v1, add_comm]

/-- If the same point added to two vectors produces equal results,
those vectors are equal. -/
lemma vadd_cancel_left (p : P) (v1 v2 : V) (h : p +ᵥ v1 = p +ᵥ v2) : v1 = v2 :=
by rw [←vsub_vadd_self V p v1, h, vsub_vadd_self V p v2]

/-- Adding the zero vector to a point gives the same point. -/
@[simp] lemma vadd_zero (p : P) : p +ᵥ (0 : V) = p :=
begin
  have h : p +ᵥ (0 : V) +ᵥ (0 : V) +ᵥ (p -ᵥ (p +ᵥ (0 : V))) = p +ᵥ (0 : V) +ᵥ (p -ᵥ (p +ᵥ (0 : V))),
  { rw [vadd_add_assoc V p (0 : V) (0 : V), add_zero] },
  rwa [vadd_vsub_self V (p +ᵥ (0 : V)), vadd_comm V (p +ᵥ (0 : V)),
       vadd_vsub_self V (p +ᵥ (0 : V))] at h
end

/-- Adding a vector to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
vector. -/
lemma vadd_vsub_comm (p1 p2 : P) (v : V) : p1 +ᵥ v -ᵥ p2 = (p1 -ᵥ p2) + v :=
begin
  apply vadd_cancel_left V p2,
  rw [vadd_vsub_self V p2, ←vadd_add_assoc V p2, vadd_vsub_self V p2]
end

/-- Subtracting the result of adding a vector produces the same result
as subtracting the points and subtracting that vector. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (v : V) : p1 -ᵥ (p2 +ᵥ v) = (p1 -ᵥ p2) - v :=
begin
  apply vadd_cancel_left V (p2 +ᵥ v),
  rw [vadd_vsub_self V (p2 +ᵥ v), vadd_comm V p2, vadd_add_assoc V p2, sub_add_cancel,
      vadd_vsub_self V p2]
end

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : V) :=
by rw [←add_zero (p -ᵥ p : V), ←vadd_vsub_comm V p, vsub_vadd_self V p]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : V)) : p1 = p2 :=
by rw [←vadd_vsub_self V p2 p1, h, vadd_zero V p2]

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
  apply vadd_cancel_left V p2,
  rw [vadd_zero V p2, ←vadd_add_assoc V p2, vadd_vsub_self V p2, vadd_vsub_self V p1]
end

/-- If the same vector added to two points produces equal results,
those points are equal. -/
lemma vadd_cancel_right (p1 p2 : P) (v : V) (h : p1 +ᵥ v = p2 +ᵥ v) : p1 = p2 :=
begin
  have h2 : p1 +ᵥ v +ᵥ -v = p2 +ᵥ v +ᵥ -v, { rw h },
  rwa [vadd_add_assoc V p1 v (-v), vadd_add_assoc V p2 v (-v), add_right_neg,
      vadd_zero V p1, vadd_zero V p2] at h2
end

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma add_vsub_vsub_cancel (p1 p2 p3 : P) : (p1 -ᵥ p2 : V) + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_cancel_left V p3,
  rw [add_comm, ←vadd_add_assoc V p3, vadd_vsub_self V p3, vadd_vsub_self V p2,
      vadd_vsub_self V p3]
end

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma sub_vsub_vsub_cancel_right (p1 p2 p3 : P) :
  (p1 -ᵥ p3 : V) - (p2 -ᵥ p3) = (p1 -ᵥ p2) :=
by rw [←vsub_vadd_eq_vsub_sub V p1 p3, vadd_vsub_self V p3]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma sub_vsub_vsub_cancel_left (p1 p2 p3 : P) :
  (p3 -ᵥ p2 : V) - (p3 -ᵥ p1) = (p1 -ᵥ p2) :=
by rw [sub_eq_add_neg, ←vsub_rev_eq_neg_vsub, add_comm, add_vsub_vsub_cancel]

/-- The pairwise differences of a set of points. -/
def vsub_set (s : set P) : set V := {v | ∃ x ∈ s, ∃ y ∈ s, v = x -ᵥ y}

end add_comm_torsor
