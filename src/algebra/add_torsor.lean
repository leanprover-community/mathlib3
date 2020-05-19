/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.group.basic

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group
actions.  It may be appropriate to refactor in terms of the general
definition of group actions (currently mathlib only has multiplicative
group actions).  The variable `G` is an explicit rather than implicit
argument to lemmas because otherwise the elaborator sometimes has
problems inferring appropriate types and type class instances.

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

/-- Type class for the `+ᵥ` notation. -/
class has_vadd (G : Type*) (P : Type*) :=
(vadd : G → P → P)

/-- Type class for the `-ᵥ` notation. -/
class has_vsub (G : Type*) (P : Type*) :=
(vsub : P → P → G)

infix ` +ᵥ `:65 := has_vadd.vadd
infix ` -ᵥ `:65 := has_vsub.vsub

section prio
set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true
/-- Type class for additive monoid actions. -/
class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd' : ∀ p : P, (0 : G) +ᵥ p = p)
(vadd_assoc' : ∀ (g1 g2 : G) (p : P), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p)

/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class add_torsor (G : Type*) (P : Type*) [add_group G] extends add_action G P, has_vsub G P :=
(nonempty : nonempty P)
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : G) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)
end prio

/-- An `add_group G` is a torsor for itself. -/
instance add_group_is_add_torsor (G : Type*) [add_group G] :
  add_torsor G G :=
{ vadd := has_add.add,
  vsub := has_sub.sub,
  zero_vadd' := zero_add,
  vadd_assoc' := λ a b c, (add_assoc a b c).symm,
  nonempty := ⟨0⟩,
  vsub_vadd' := sub_add_cancel,
  vadd_vsub' := add_sub_cancel }

namespace add_torsor

section general

variables (G : Type*) {P : Type*} [add_group G] [S : add_torsor G P]
include S

/-- Adding the zero group element to a point gives the same point. -/
@[simp] lemma zero_vadd (p : P) : (0 : G) +ᵥ p = p :=
zero_vadd' p

/-- Adding two group elements to a point produces the same result as
adding their sum. -/
lemma vadd_assoc (g1 g2 : G) (p : P) : g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p :=
vadd_assoc' g1 g2 p

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vsub_vadd (p1 p2 : P) : (p1 -ᵥ p2 : G) +ᵥ p2 = p1 :=
vsub_vadd' p1 p2

/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp] lemma vadd_vsub (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
vadd_vsub' g p

/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
lemma vadd_cancel_right (g1 g2 : G) (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 :=
by rw [←vadd_vsub G g1, h, vadd_vsub]

/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
lemma vadd_vsub_assoc (g : G) (p1 p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) :=
begin
  apply vadd_cancel_right G _ _ p2,
  rw [vsub_vadd, ←vadd_assoc, vsub_vadd]
end

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : G) :=
by rw [←zero_add (p -ᵥ p : G), ←vadd_vsub_assoc, vadd_vsub]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : G)) : p1 = p2 :=
by rw [←vsub_vadd G p1 p2, h, zero_vadd]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
lemma vsub_eq_zero_iff_eq (p1 p2 : P) : p1 -ᵥ p2 = (0 : G) ↔ p1 = p2 :=
iff.intro (eq_of_vsub_eq_zero G) (λ h, h ▸ vsub_self G _)

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
lemma vsub_rev_eq_neg_vsub (p1 p2 : P) : (p2 -ᵥ p1 : G) = -(p1 -ᵥ p2) :=
begin
  symmetry,
  apply neg_eq_of_add_eq_zero,
  apply vadd_cancel_right G _ _ p1,
  rw [zero_vadd, ←vadd_assoc, vsub_vadd, vsub_vadd]
end

/-- If the same group element added to two points produces equal results,
those points are equal. -/
lemma vadd_cancel_left (p1 p2 : P) (g : G) (h : g +ᵥ p1 = g +ᵥ p2) : p1 = p2 :=
begin
  have h2 : -g +ᵥ (g +ᵥ p1) = -g +ᵥ (g +ᵥ p2), { rw h },
  rwa [vadd_assoc, vadd_assoc, add_left_neg, zero_vadd, zero_vadd] at h2
end

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma vsub_add_vsub_cancel (p1 p2 p3 : P) : (p1 -ᵥ p2 : G) + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_cancel_right G _ _ p3,
  rw [←vadd_assoc, vsub_vadd, vsub_vadd, vsub_vadd]
end

/-- The pairwise differences of a set of points. -/
def vsub_set (s : set P) : set G := {g | ∃ x ∈ s, ∃ y ∈ s, g = x -ᵥ y}

end general

section comm

variables (G : Type*) {P : Type*} [add_comm_group G] [S : add_torsor G P]
include S

/-- Adding two group elements to a point produces the same result in either
order. -/
lemma vadd_comm (p : P) (g1 g2 : G) : g1 +ᵥ (g2 +ᵥ p) = g2 +ᵥ (g1 +ᵥ p) :=
by rw [vadd_assoc, vadd_assoc, add_comm]

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = (p1 -ᵥ p2) - g :=
begin
  apply vadd_cancel_right G _ _ (g +ᵥ p2),
  rw [vsub_vadd, vadd_comm, vadd_assoc, add_comm, sub_add_cancel, vsub_vadd]
end

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_right (p1 p2 p3 : P) :
  (p1 -ᵥ p3 : G) - (p2 -ᵥ p3) = (p1 -ᵥ p2) :=
by rw [←vsub_vadd_eq_vsub_sub, vsub_vadd]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_left (p1 p2 p3 : P) :
  (p3 -ᵥ p2 : G) - (p3 -ᵥ p1) = (p1 -ᵥ p2) :=
by rw [sub_eq_add_neg, ←vsub_rev_eq_neg_vsub, add_comm, vsub_add_vsub_cancel]

end comm

end add_torsor
