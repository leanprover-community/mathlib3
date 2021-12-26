/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import algebra.star.basic
import group_theory.subgroup.basic

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

variables {R : Type*}

variables (R)
/-- The self-adjoint elements of a type with star, as a subtype. -/
def self_adjoints [has_star R] := {x : R // star x = x}
variables {R}

/-- An element `x` of a type with star is self-adjoint if `star x = x`. -/
abbreviation is_self_adjoint [has_star R] (x : R) : Prop := star x = x

namespace self_adjoints

instance [has_star R] : has_coe (self_adjoints R) R := ⟨subtype.val⟩

lemma is_self_adjoint [has_star R] (x : self_adjoints R) : is_self_adjoint (x : R) := x.prop

instance [has_star R] : has_star (self_adjoints R) := ⟨id⟩
instance [has_involutive_star R] : has_involutive_star (self_adjoints R) := ⟨λ _, rfl⟩

@[simp] lemma star_eq [has_star R] {x : self_adjoints R} : star x = x := rfl
@[simp] lemma star_coe_eq [has_star R] {x : self_adjoints R} : star (x : R) = x := x.prop

instance [add_monoid R] [star_add_monoid R] : add_monoid (self_adjoints R) :=
{ add := λ x y, ⟨x.1 + y.1, by rw [star_add, x.2, y.2]⟩,
  zero := ⟨0, star_zero _⟩,
  add_assoc := λ x y z, by { ext, exact add_assoc _ _ _ },
  zero_add := λ x, by simp only [zero_add, subtype.coe_eta, subtype.val_eq_coe],
  add_zero :=  λ x, by simp only [add_zero, subtype.coe_eta, subtype.val_eq_coe] }

@[simp] lemma coe_add [add_monoid R] [star_add_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x + y) = (x : R) + y := rfl

@[simp] lemma coe_zero [add_monoid R] [star_add_monoid R] :
  (coe : self_adjoints R → R) (0 : self_adjoints R) = (0 : R) := rfl

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (self_adjoints R) := ⟨λ x y, star_eq⟩

instance [add_group R] [star_add_monoid R] : add_group (self_adjoints R) :=
{ neg := λ x, ⟨-x, by simp only [star_coe_eq, star_neg]⟩,
  add_left_neg := λ x, by { ext, exact add_left_neg _ },
  ..self_adjoints.add_monoid }

@[simp] lemma coe_neg [add_group R] [star_add_monoid R] (x : self_adjoints R) :
  (coe : self_adjoints R → R) (-x) = -(x : R) := rfl

@[simp] lemma coe_sub [add_group R] [star_add_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x - y) = (x : R) - y :=
by { simp only [sub_eq_add_neg], refl }

instance [add_comm_monoid R] [star_add_monoid R] : add_comm_monoid (self_adjoints R) :=
{ add_comm := λ x y, by { ext, exact add_comm _ _ },
  ..self_adjoints.add_monoid }

instance [add_comm_group R] [star_add_monoid R] : add_comm_group (self_adjoints R) :=
{ ..self_adjoints.add_comm_monoid,
  ..self_adjoints.add_group }

instance [monoid R] [star_monoid R] : has_one (self_adjoints R) := ⟨⟨1, star_one _⟩⟩

@[simp] lemma coe_one [monoid R] [star_monoid R] :
  (coe : self_adjoints R → R) (1 : self_adjoints R) = (1 : R) := rfl

instance [comm_monoid R] [star_monoid R] : has_mul (self_adjoints R) :=
⟨λ x y, ⟨(x : R) * y, by simp only [star_mul', star_coe_eq]⟩⟩

@[simp] lemma coe_mul [comm_monoid R] [star_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x * y) = (x : R) * y := rfl

instance [comm_monoid R] [star_monoid R] : monoid (self_adjoints R) :=
{ mul_assoc := λ x y z, by { ext, exact mul_assoc _ _ _ },
  one_mul := λ x, by { ext, simp only [coe_mul, one_mul, coe_one] },
  mul_one := λ x, by { ext, simp only [mul_one, coe_mul, coe_one] },
  ..self_adjoints.has_one,
  ..self_adjoints.has_mul }

instance [comm_monoid R] [star_monoid R] : comm_monoid (self_adjoints R) :=
{ mul_comm := λ x y, by { ext, exact mul_comm _ _ },
  ..self_adjoints.monoid }

instance [division_ring R] [star_ring R] : has_inv (self_adjoints R) :=
⟨λ x, ⟨(x : R)⁻¹, by simp only [star_inv', star_coe_eq]⟩⟩

@[simp] lemma coe_inv [division_ring R] [star_ring R] (x : self_adjoints R) :
  (coe : self_adjoints R → R) (x⁻¹) = (x : R)⁻¹ := rfl

instance [comm_ring R] [star_ring R] : distrib (self_adjoints R) :=
{ left_distrib := λ x y z, by { ext, exact left_distrib _ _ _ },
  right_distrib := λ x y z, by { ext, exact right_distrib _ _ _ },
  ..show has_add (self_adjoints R), by apply_instance,
  ..show has_mul (self_adjoints R), by apply_instance }

instance [comm_ring R] [star_ring R] : comm_ring (self_adjoints R) :=
{ ..self_adjoints.add_comm_group,
  ..self_adjoints.comm_monoid,
  ..self_adjoints.distrib }

instance [field R] [star_ring R] : field (self_adjoints R) :=
{ inv :=  λ x, ⟨(x.val)⁻¹, by simp only [star_inv', star_coe_eq, subtype.val_eq_coe]⟩,
  exists_pair_ne := ⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩,
  mul_inv_cancel := λ x hx, by { ext, exact mul_inv_cancel (λ H, hx $ subtype.eq H) },
  inv_zero := by { ext, exact inv_zero },
  ..self_adjoints.comm_ring }

/-- Conjugation of a self-adjoint by an element of the original type: given `r : R` and
`x : self_adjoints R`, we define `r • x` as `r * x * star r`. -/
instance [monoid R] [star_monoid R] : has_scalar R (self_adjoints R) :=
⟨λ r x, ⟨r * x * star r, by simp only [mul_assoc, star_coe_eq, star_star, star_mul]⟩⟩

@[simp] lemma conj_eq_smul [monoid R] [star_monoid R] (r : R) (x : self_adjoints R) :
  (coe : self_adjoints R → R) (r • x) = r * x * star r := rfl

@[simp] lemma conj_eq_smul' [monoid R] [star_monoid R] (r : R) (x : self_adjoints R) :
  (coe : self_adjoints R → R) (star r • x) = star r * x * r :=
by simp only [conj_eq_smul, star_star]

@[simp] lemma mul_self_star_eq_smul_one [monoid R] [star_monoid R] (r : R) :
  (coe : self_adjoints R → R) (r • 1) = r * star r :=
by simp only [conj_eq_smul, mul_one, coe_one]

@[simp] lemma star_mul_self_eq_smul_one [monoid R] [star_monoid R] (r : R) :
  (coe : self_adjoints R → R) (star r • 1) = star r * r :=
by simp only [conj_eq_smul, mul_one, coe_one, star_star]

instance [monoid R] [star_monoid R] : mul_action R (self_adjoints R) :=
{ one_smul := λ x, by { ext, simp only [mul_one, one_mul, conj_eq_smul, star_one] },
  mul_smul := λ r s x, by { ext, simp only [mul_assoc, conj_eq_smul, star_mul] } }

instance [ring R] [star_ring R] : distrib_mul_action R (self_adjoints R) :=
{ smul_add := λ r x y, by { ext, simp only [mul_add, add_mul, conj_eq_smul, coe_add] },
  smul_zero := λ r, by { ext, simp only [coe_zero, zero_mul, conj_eq_smul, mul_zero] } }

instance [ring R] [star_ring R] : smul_with_zero R (self_adjoints R) :=
{ smul_zero := λ r, by { ext, simp only [smul_zero] },
  zero_smul := λ r,  by { ext, simp only [coe_zero, conj_eq_smul, star_zero, mul_zero] } }

end self_adjoints


namespace is_self_adjoint

/-- Construct a self-adjoint element from the assumption `is_self_adjoint x`.  -/
def to_self_adjoints [has_star R] {x : R} (h : is_self_adjoint x) : self_adjoints R := ⟨x, h⟩

lemma star_eq [has_star R] {x : R} (h : is_self_adjoint x) : star x = x := h
lemma star_eq_iff [has_star R] {x : R} : is_self_adjoint x ↔ star x = x := ⟨id, id⟩

section add_monoid

variables [add_monoid R] [star_add_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma zero : is_self_adjoint (0 : R) := star_zero R

lemma add : is_self_adjoint (x + y) :=
(hx.to_self_adjoints + hy.to_self_adjoints).is_self_adjoint

end add_monoid

section add_group

variables [add_group R] [star_add_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma neg : is_self_adjoint (-x) := (-hx.to_self_adjoints).is_self_adjoint

include hx hy
lemma sub : is_self_adjoint (x - y) := by rw [star_eq_iff, star_sub, star_eq hx, star_eq hy]

end add_group

section monoid

variables [monoid R] [star_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma one : is_self_adjoint (1 : R) := star_one R

include hx
lemma conjugate {z : R} : is_self_adjoint (z * x * star z) :=
by simp only [star_eq_iff, mul_assoc, hx.star_eq, star_star, star_mul]

lemma conjugate' {z : R} : is_self_adjoint (star z * x * z) :=
by simp only [star_eq_iff, mul_assoc, hx.star_eq, star_star, star_mul]

end monoid

end is_self_adjoint
