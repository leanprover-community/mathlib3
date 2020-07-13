/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov.
-/
import algebra.group.prod
import algebra.group.type_tags
import algebra.pi_instances
import data.equiv.basic

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
definition of group actions, via `to_additive`, when there is a use
for multiplicative torsors (currently mathlib only develops the theory
of group actions for multiplicative group actions).  The variable `G`
is an explicit rather than implicit argument to lemmas because
otherwise the elaborator sometimes has problems inferring appropriate
types and type class instances.

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
[nonempty : nonempty P]
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
  vsub_vadd' := sub_add_cancel,
  vadd_vsub' := add_sub_cancel }

/-- Simplify addition for a torsor for an `add_group G` over
itself. -/
@[simp] lemma vadd_eq_add (G : Type*) [add_group G] (g1 g2 : G) : g1 +ᵥ g2 = g1 + g2 :=
rfl

/-- Simplify subtraction for a torsor for an `add_group G` over
itself. -/
@[simp] lemma vsub_eq_sub (G : Type*) [add_group G] (g1 g2 : G) : g1 -ᵥ g2 = g1 - g2 :=
rfl

namespace add_action

section general

variables (G : Type*) {P : Type*} [add_monoid G] [A : add_action G P]
include A

/-- Adding the zero group element to a point gives the same point. -/
@[simp] lemma zero_vadd (p : P) : (0 : G) +ᵥ p = p :=
zero_vadd' p

/-- Adding two group elements to a point produces the same result as
adding their sum. -/
lemma vadd_assoc (g1 g2 : G) (p : P) : g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p :=
vadd_assoc' g1 g2 p

end general

section comm

variables (G : Type*) {P : Type*} [add_comm_monoid G] [A : add_action G P]
include A

/-- Adding two group elements to a point produces the same result in either
order. -/
lemma vadd_comm (p : P) (g1 g2 : G) : g1 +ᵥ (g2 +ᵥ p) = g2 +ᵥ (g1 +ᵥ p) :=
by rw [vadd_assoc, vadd_assoc, add_comm]

end comm

section group

variables {G : Type*} {P : Type*} [add_group G] [A : add_action G P]
include A

/-- If the same group element added to two points produces equal results,
those points are equal. -/
lemma vadd_left_cancel {p1 p2 : P} (g : G) (h : g +ᵥ p1 = g +ᵥ p2) : p1 = p2 :=
begin
  have h2 : -g +ᵥ (g +ᵥ p1) = -g +ᵥ (g +ᵥ p2), { rw h },
  rwa [vadd_assoc, vadd_assoc, add_left_neg, zero_vadd, zero_vadd] at h2
end

@[simp] lemma vadd_left_cancel_iff {p₁ p₂ : P} (g : G) :
  g +ᵥ p₁ = g +ᵥ p₂ ↔ p₁ = p₂ :=
⟨vadd_left_cancel g, λ h, h ▸ rfl⟩

end group

end add_action

namespace add_torsor

open add_action

section general

variables (G : Type*) {P : Type*} [add_group G] [T : add_torsor G P]
include T

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp] lemma vsub_vadd (p1 p2 : P) : (p1 -ᵥ p2 : G) +ᵥ p2 = p1 :=
vsub_vadd' p1 p2

/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp] lemma vadd_vsub (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
vadd_vsub' g p

variable {G}

/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
lemma vadd_right_cancel {g1 g2 : G} (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 :=
by rw [←vadd_vsub G g1, h, vadd_vsub]

@[simp] lemma vadd_right_cancel_iff {g1 g2 : G} (p : P) :  g1 +ᵥ p = g2 +ᵥ p ↔ g1 = g2 :=
⟨vadd_right_cancel p, λ h, h ▸ rfl⟩

/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
lemma vadd_vsub_assoc (g : G) (p1 p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) :=
begin
  apply vadd_right_cancel p2,
  rw [vsub_vadd, ←vadd_assoc, vsub_vadd]
end

variable (G)

/-- Subtracting a point from itself produces 0. -/
@[simp] lemma vsub_self (p : P) : p -ᵥ p = (0 : G) :=
by rw [←zero_add (p -ᵥ p : G), ←vadd_vsub_assoc, vadd_vsub]

/-- If subtracting two points produces 0, they are equal. -/
lemma eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : G)) : p1 = p2 :=
by rw [←vsub_vadd G p1 p2, h, zero_vadd]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp] lemma vsub_eq_zero_iff_eq {p1 p2 : P} : p1 -ᵥ p2 = (0 : G) ↔ p1 = p2 :=
iff.intro (eq_of_vsub_eq_zero G) (λ h, h ▸ vsub_self G _)

/-- Cancellation adding the results of two subtractions. -/
@[simp] lemma vsub_add_vsub_cancel (p1 p2 p3 : P) : (p1 -ᵥ p2 : G) + (p2 -ᵥ p3) = (p1 -ᵥ p3) :=
begin
  apply vadd_right_cancel p3,
  rw [←vadd_assoc, vsub_vadd, vsub_vadd, vsub_vadd]
end

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp] lemma neg_vsub_eq_vsub_rev (p1 p2 : P) : -(p1 -ᵥ p2) = (p2 -ᵥ p1 : G) :=
begin
  refine neg_eq_of_add_eq_zero (vadd_right_cancel p1 _),
  rw [vsub_add_vsub_cancel, vsub_self],
end

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
lemma vsub_vadd_eq_vsub_sub (p1 p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = (p1 -ᵥ p2) - g :=
by rw [←add_right_inj (p2 -ᵥ p1 : G), vsub_add_vsub_cancel, ←neg_vsub_eq_vsub_rev, vadd_vsub,
       ←add_sub_assoc, ←neg_vsub_eq_vsub_rev, neg_add_self, zero_sub]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_right (p1 p2 p3 : P) :
  (p1 -ᵥ p3 : G) - (p2 -ᵥ p3) = (p1 -ᵥ p2) :=
by rw [←vsub_vadd_eq_vsub_sub, vsub_vadd]

/-- The pairwise differences of a set of points. -/
def vsub_set (s : set P) : set G := {g | ∃ x ∈ s, ∃ y ∈ s, g = x -ᵥ y}

/-- `vsub_set` of an empty set. -/
@[simp] lemma vsub_set_empty : vsub_set G (∅ : set P) = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  rintros g ⟨p, hp, hg⟩,
  exact hp
end

/-- Each pairwise difference is in the `vsub_set`. -/
lemma vsub_mem_vsub_set {p1 p2 : P} {s : set P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  (p1 -ᵥ p2) ∈ vsub_set G s :=
⟨p1, hp1, p2, hp2, rfl⟩

/-- `vsub_set` is contained in `vsub_set` of a larger set. -/
lemma vsub_set_mono {s1 s2 : set P} (h : s1 ⊆ s2) : vsub_set G s1 ⊆ vsub_set G s2 :=
begin
  rintros v ⟨p1, hp1, p2, hp2, hv⟩,
  exact ⟨p1, set.mem_of_mem_of_subset hp1 h, p2, set.mem_of_mem_of_subset hp2 h, hv⟩
end

@[simp] lemma vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) :
  ((v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) : G) = v₁ - v₂ :=
by rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]

/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
lemma vsub_left_cancel {p1 p2 p : P} (h : (p1 -ᵥ p : G) = p2 -ᵥ p) : p1 = p2 :=
by rwa [←sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h

/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp] lemma vsub_left_cancel_iff {p1 p2 p : P} : (p1 -ᵥ p : G) = p2 -ᵥ p ↔ p1 = p2 :=
⟨vsub_left_cancel _, λ h, h ▸ rfl⟩

/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
lemma vsub_right_cancel {p1 p2 p : P} (h : (p -ᵥ p1 : G) = p -ᵥ p2) : p1 = p2 :=
begin
  have h2 : (p -ᵥ p2 : G) +ᵥ p1 = (p -ᵥ p1 : G) +ᵥ p1, { rw h },
  conv_rhs at h2 {
    rw [vsub_vadd, ←vsub_vadd G p p2],
  },
  rwa vadd_left_cancel_iff at h2
end

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp] lemma vsub_right_cancel_iff {p1 p2 p : P} : (p -ᵥ p1 : G) = p -ᵥ p2 ↔ p1 = p2 :=
⟨vsub_right_cancel _, λ h, h ▸ rfl⟩

end general

section comm

variables (G : Type*) {P : Type*} [add_comm_group G] [add_torsor G P]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp] lemma vsub_sub_vsub_cancel_left (p1 p2 p3 : P) :
  (p3 -ᵥ p2 : G) - (p3 -ᵥ p1) = (p1 -ᵥ p2) :=
by rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]

@[simp] lemma vadd_vsub_vadd_cancel_left (v : G) (p1 p2 : P) :
  ((v +ᵥ p1) -ᵥ (v +ᵥ p2) : G) = p1 -ᵥ p2 :=
by rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel']

end comm

end add_torsor

namespace prod

variables {G : Type*} {P : Type*} {G' : Type*} {P' : Type*} [add_group G] [add_group G']
  [add_torsor G P] [add_torsor G' P']

instance : add_torsor (G × G') (P × P') :=
{ vadd := λ v p, (v.1 +ᵥ p.1, v.2 +ᵥ p.2),
  zero_vadd' := λ p, by simp,
  vadd_assoc' := by simp [add_action.vadd_assoc],
  vsub := λ p₁ p₂, (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2),
  nonempty := @prod.nonempty _ _ (add_torsor.nonempty G) (add_torsor.nonempty G'),
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
{
  vadd := λ g p, λ i, g i +ᵥ p i,
  zero_vadd' := λ p, funext $ λ i, zero_vadd (fg i) (p i),
  vadd_assoc' := λ g₁ g₂ p, funext $ λ i, vadd_assoc (fg i) (g₁ i) (g₂ i) (p i),
  vsub := λ p₁ p₂, λ i, p₁ i -ᵥ p₂ i,
  nonempty := ⟨λ i, classical.choice (T i).nonempty⟩,
  vsub_vadd' := λ p₁ p₂, funext $ λ i, vsub_vadd (fg i) (p₁ i) (p₂ i),
  vadd_vsub' := λ g p, funext $ λ i, vadd_vsub (fg i) (g i) (p i),
}

/-- Addition in a product of `add_torsor`s. -/
@[simp] lemma vadd_apply [T : ∀ i, add_torsor (fg i) (fp i)] (x : Π i, fg i) (y : Π i, fp i)
  {i : I} : (x +ᵥ y) i = x i +ᵥ y i
:= rfl

end pi

namespace equiv

variables (G : Type*) {P : Type*} [add_group G] [add_torsor G P]

open add_action add_torsor

/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vadd_const (p : P) : G ≃ P :=
{ to_fun := λ v, v +ᵥ p,
  inv_fun := λ p', p' -ᵥ p,
  left_inv := λ v, vadd_vsub _ _ _,
  right_inv := λ p', vsub_vadd _ _ _ }

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const G p) = λ v, v+ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const G p).symm = λ p', p' -ᵥ p := rfl

variables {G} (P)

/-- The permutation given by `p ↦ v +ᵥ p`. -/
def const_vadd (v : G) : equiv.perm P :=
{ to_fun := (+ᵥ) v,
  inv_fun := (+ᵥ) (-v),
  left_inv := λ p, by simp [vadd_assoc],
  right_inv := λ p, by simp [vadd_assoc] }

@[simp] lemma coe_const_vadd (v : G) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (G)

@[simp] lemma const_vadd_zero : const_vadd P (0:G) = 1 := ext $ zero_vadd G

variable {G}

@[simp] lemma const_vadd_add (v₁ v₂ : G) :
  const_vadd P (v₁ + v₂) = const_vadd P v₁ * const_vadd P v₂ :=
ext $ λ p, (vadd_assoc G v₁ v₂ p).symm

/-- `equiv.const_vadd` as a homomorphism from `multiplicative G` to `equiv.perm P` -/
def const_vadd_hom : multiplicative G →* equiv.perm P :=
{ to_fun := λ v, const_vadd P v.to_add,
  map_one' := const_vadd_zero G P,
  map_mul' := const_vadd_add P }

end equiv
