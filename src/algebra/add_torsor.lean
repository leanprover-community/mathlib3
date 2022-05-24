/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import data.set.pointwise

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notations

* `v +ᵥ p` is a notation for `has_vadd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `has_vsub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class add_torsor (G : out_param Type*) (P : Type*) [out_param $ add_group G]
  extends add_action G P, has_vsub G P :=
[nonempty : nonempty P]
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : G) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)

attribute [instance, priority 100, nolint dangerous_instance] add_torsor.nonempty
attribute [nolint dangerous_instance] add_torsor.to_has_vsub

/-- An `add_group G` is a torsor for itself. -/
@[nolint instance_priority]
instance add_group_is_add_torsor (G : Type*) [add_group G] :
  add_torsor G G :=
{ vsub := has_sub.sub,
  vsub_vadd' := sub_add_cancel,
  vadd_vsub' := add_sub_cancel }

/-- Simplify subtraction for a torsor for an `add_group G` over
itself. -/
@[simp] lemma vsub_eq_sub {G : Type*} [add_group G] (g1 g2 : G) : g1 -ᵥ g2 = g1 - g2 :=
rfl

section general

variables {G : Type*} {P : Type*} [add_group G] [T : add_torsor G P]
include T

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vsub_vadd (p1 p2 : P) : p1 -ᵥ p2 +ᵥ p2 = p1 :=
add_torsor.vsub_vadd' p1 p2

/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp] lemma vadd_vsub (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
add_torsor.vadd_vsub' g p

/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
lemma vadd_right_cancel {g1 g2 : G} (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 :=
by rw [←vadd_vsub g1, h, vadd_vsub]

@[simp] lemma vadd_right_cancel_iff {g1 g2 : G} (p : P) :  g1 +ᵥ p = g2 +ᵥ p ↔ g1 = g2 :=
⟨vadd_right_cancel p, λ h, h ▸ rfl⟩

/-- Adding a group element to the point `p` is an injective
function. -/
lemma vadd_right_injective (p : P) : function.injective ((+ᵥ p) : G → P) :=
λ g1 g2, vadd_right_cancel p

/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
lemma vadd_vsub_assoc (g : G) (p1 p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) :=
begin
  apply vadd_right_cancel p2,
  rw [vsub_vadd, add_vadd, vsub_vadd]
end

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : G) :=
by rw [←zero_add (p -ᵥ p), ←vadd_vsub_assoc, vadd_vsub]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : G)) : p1 = p2 :=
by rw [←vsub_vadd p1 p2, h, zero_vadd]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp] lemma vsub_eq_zero_iff_eq {p1 p2 : P} : p1 -ᵥ p2 = (0 : G) ↔ p1 = p2 :=
iff.intro eq_of_vsub_eq_zero (λ h, h ▸ vsub_self _)

lemma vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q :=
not_congr vsub_eq_zero_iff_eq

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma vsub_add_vsub_cancel (p1 p2 p3 : P) : p1 -ᵥ p2 + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_right_cancel p3,
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]
end

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp] lemma neg_vsub_eq_vsub_rev (p1 p2 : P) : -(p1 -ᵥ p2) = (p2 -ᵥ p1) :=
begin
  refine neg_eq_of_add_eq_zero_right (vadd_right_cancel p1 _),
  rw [vsub_add_vsub_cancel, vsub_self],
end

lemma vadd_vsub_eq_sub_vsub (g : G) (p q : P) : g +ᵥ p -ᵥ q = g - (q -ᵥ p) :=
by rw [vadd_vsub_assoc, sub_eq_add_neg, neg_vsub_eq_vsub_rev]

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = (p1 -ᵥ p2) - g :=
by rw [←add_right_inj (p2 -ᵥ p1 : G), vsub_add_vsub_cancel, ←neg_vsub_eq_vsub_rev, vadd_vsub,
       ←add_sub_assoc, ←neg_vsub_eq_vsub_rev, neg_add_self, zero_sub]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_right (p1 p2 p3 : P) :
  (p1 -ᵥ p3) - (p2 -ᵥ p3) = (p1 -ᵥ p2) :=
by rw [←vsub_vadd_eq_vsub_sub, vsub_vadd]

/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
lemma eq_vadd_iff_vsub_eq (p1 : P) (g : G) (p2 : P) : p1 = g +ᵥ p2 ↔ p1 -ᵥ p2 = g :=
⟨λ h, h.symm ▸ vadd_vsub _ _, λ h, h ▸ (vsub_vadd _ _).symm⟩

lemma vadd_eq_vadd_iff_neg_add_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
  v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ - v₁ + v₂ = p₁ -ᵥ p₂ :=
by rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, ← add_right_inj (-v₁), neg_add_cancel_left, eq_comm]

namespace set
open_locale pointwise

@[simp] lemma singleton_vsub_self (p : P) : ({p} : set P) -ᵥ {p} = {(0:G)} :=
by rw [set.singleton_vsub_singleton, vsub_self]

end set

@[simp] lemma vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) :
  (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ - v₂ :=
by rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]

/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
lemma vsub_left_cancel {p1 p2 p : P} (h : p1 -ᵥ p = p2 -ᵥ p) : p1 = p2 :=
by rwa [←sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h

/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp] lemma vsub_left_cancel_iff {p1 p2 p : P} : (p1 -ᵥ p) = p2 -ᵥ p ↔ p1 = p2 :=
⟨vsub_left_cancel, λ h, h ▸ rfl⟩

/-- Subtracting the point `p` is an injective function. -/
lemma vsub_left_injective (p : P) : function.injective ((-ᵥ p) : P → G) :=
λ p2 p3, vsub_left_cancel

/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
lemma vsub_right_cancel {p1 p2 p : P} (h : p -ᵥ p1 = p -ᵥ p2) : p1 = p2 :=
begin
  refine vadd_left_cancel (p -ᵥ p2) _,
  rw [vsub_vadd, ← h, vsub_vadd]
end

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp] lemma vsub_right_cancel_iff {p1 p2 p : P} : p -ᵥ p1 = p -ᵥ p2 ↔ p1 = p2 :=
⟨vsub_right_cancel, λ h, h ▸ rfl⟩

/-- Subtracting a point from the point `p` is an injective
function. -/
lemma vsub_right_injective (p : P) : function.injective ((-ᵥ) p : P → G) :=
λ p2 p3, vsub_right_cancel

end general

section comm

variables {G : Type*} {P : Type*} [add_comm_group G] [add_torsor G P]

include G

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_left (p1 p2 p3 : P) :
  (p3 -ᵥ p2) - (p3 -ᵥ p1) = (p1 -ᵥ p2) :=
by rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]

@[simp] lemma vadd_vsub_vadd_cancel_left (v : G) (p1 p2 : P) :
  (v +ᵥ p1) -ᵥ (v +ᵥ p2) = p1 -ᵥ p2 :=
by rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel']

lemma vsub_vadd_comm (p1 p2 p3 : P) : (p1 -ᵥ p2 : G) +ᵥ p3 = p3 -ᵥ p2 +ᵥ p1 :=
begin
  rw [←@vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub],
  simp
end

lemma vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
  v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ :=
by rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]

lemma vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) :
  (p₁ -ᵥ p₂) - (p₃ -ᵥ p₄) = (p₁ -ᵥ p₃) - (p₂ -ᵥ p₄) :=
by rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]

end comm

namespace prod

variables {G : Type*} {P : Type*} {G' : Type*} {P' : Type*} [add_group G] [add_group G']
  [add_torsor G P] [add_torsor G' P']

instance : add_torsor (G × G') (P × P') :=
{ vadd := λ v p, (v.1 +ᵥ p.1, v.2 +ᵥ p.2),
  zero_vadd := λ p, by simp,
  add_vadd := by simp [add_vadd],
  vsub := λ p₁ p₂, (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2),
  nonempty := prod.nonempty,
  vsub_vadd' := λ p₁ p₂, show (p₁.1 -ᵥ p₂.1 +ᵥ p₂.1, _) = p₁, by simp,
  vadd_vsub' := λ v p, show (v.1 +ᵥ p.1 -ᵥ p.1, v.2 +ᵥ p.2 -ᵥ p.2)  =v, by simp }

@[simp] lemma fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 := rfl
@[simp] lemma snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 := rfl
@[simp] lemma mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') :
  (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') := rfl

@[simp] lemma fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 := rfl
@[simp] lemma snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 := rfl
@[simp] lemma mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
  ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') := rfl

end prod

namespace pi

universes u v w
variables {I : Type u} {fg : I → Type v} [∀ i, add_group (fg i)] {fp : I → Type w}

open add_action add_torsor

/-- A product of `add_torsor`s is an `add_torsor`. -/
instance [T : ∀ i, add_torsor (fg i) (fp i)] : add_torsor (Π i, fg i) (Π i, fp i) :=
{ vadd := λ g p, λ i, g i +ᵥ p i,
  zero_vadd := λ p, funext $ λ i, zero_vadd (fg i) (p i),
  add_vadd := λ g₁ g₂ p, funext $ λ i, add_vadd (g₁ i) (g₂ i) (p i),
  vsub := λ p₁ p₂, λ i, p₁ i -ᵥ p₂ i,
  nonempty := ⟨λ i, classical.choice (T i).nonempty⟩,
  vsub_vadd' := λ p₁ p₂, funext $ λ i, vsub_vadd (p₁ i) (p₂ i),
  vadd_vsub' := λ g p, funext $ λ i, vadd_vsub (g i) (p i) }

end pi

namespace equiv

variables {G : Type*} {P : Type*} [add_group G] [add_torsor G P]

include G

/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vadd_const (p : P) : G ≃ P :=
{ to_fun := λ v, v +ᵥ p,
  inv_fun := λ p', p' -ᵥ p,
  left_inv := λ v, vadd_vsub _ _,
  right_inv := λ p', vsub_vadd _ _ }

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const p) = λ v, v+ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const p).symm = λ p', p' -ᵥ p := rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub (p : P) : P ≃ G :=
{ to_fun := (-ᵥ) p,
  inv_fun := λ v, -v +ᵥ p,
  left_inv := λ p', by simp,
  right_inv := λ v, by simp [vsub_vadd_eq_vsub_sub] }

@[simp] lemma coe_const_vsub (p : P) : ⇑(const_vsub p) = (-ᵥ) p := rfl

@[simp] lemma coe_const_vsub_symm (p : P) : ⇑(const_vsub p).symm = λ v, -v +ᵥ p := rfl

variables (P)

/-- The permutation given by `p ↦ v +ᵥ p`. -/
def const_vadd (v : G) : equiv.perm P :=
{ to_fun := (+ᵥ) v,
  inv_fun := (+ᵥ) (-v),
  left_inv := λ p, by simp [vadd_vadd],
  right_inv := λ p, by simp [vadd_vadd] }

@[simp] lemma coe_const_vadd (v : G) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (G)

@[simp] lemma const_vadd_zero : const_vadd P (0:G) = 1 := ext $ zero_vadd G

variable {G}

@[simp] lemma const_vadd_add (v₁ v₂ : G) :
  const_vadd P (v₁ + v₂) = const_vadd P v₁ * const_vadd P v₂ :=
ext $ add_vadd v₁ v₂

/-- `equiv.const_vadd` as a homomorphism from `multiplicative G` to `equiv.perm P` -/
def const_vadd_hom : multiplicative G →* equiv.perm P :=
{ to_fun := λ v, const_vadd P v.to_add,
  map_one' := const_vadd_zero G P,
  map_mul' := const_vadd_add P }

variable {P}

open function

/-- Point reflection in `x` as a permutation. -/
def point_reflection (x : P) : perm P := (const_vsub x).trans (vadd_const x)

lemma point_reflection_apply (x y : P) : point_reflection x y = x -ᵥ y +ᵥ x := rfl

@[simp] lemma point_reflection_symm (x : P) : (point_reflection x).symm = point_reflection x :=
ext $ by simp [point_reflection]

@[simp] lemma point_reflection_self (x : P) : point_reflection x x = x := vsub_vadd _ _

lemma point_reflection_involutive (x : P) : involutive (point_reflection x : P → P) :=
λ y, (equiv.apply_eq_iff_eq_symm_apply _).2 $ by rw point_reflection_symm

/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
lemma point_reflection_fixed_iff_of_injective_bit0 {x y : P} (h : injective (bit0 : G → G)) :
  point_reflection x y = y ↔ y = x :=
by rw [point_reflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
  neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]

omit G

lemma injective_point_reflection_left_of_injective_bit0 {G P : Type*} [add_comm_group G]
  [add_torsor G P] (h : injective (bit0 : G → G)) (y : P) :
  injective (λ x : P, point_reflection x y) :=
λ x₁ x₂ (hy : point_reflection x₁ y = point_reflection x₂ y),
  by rwa [point_reflection_apply, point_reflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero,
    h.eq_iff, vsub_eq_zero_iff_eq] at hy

end equiv

lemma add_torsor.subsingleton_iff (G P : Type*) [add_group G] [add_torsor G P] :
  subsingleton G ↔ subsingleton P :=
begin
  inhabit P,
  exact (equiv.vadd_const default).subsingleton_congr,
end
