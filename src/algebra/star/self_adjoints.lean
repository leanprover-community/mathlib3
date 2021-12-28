/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.star.basic
import group_theory.subgroup.basic

/-!
# Self-adjoint elements of a star additive group

FIXME
-/

variables {R : Type*}

variables (R)
/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def self_adjoints [add_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | star x = x},
  zero_mem' := star_zero R,
  add_mem' := λ x y (hx : star x = x) (hy : star y = y),
                show star (x + y) = x + y, by simp only [star_add x y, hx, hy],
  neg_mem' := λ x (hx : star x = x), show star (-x) = -x, by simp only [hx, star_neg] }
variables {R}

namespace self_adjoints

section add_group
variables [add_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ self_adjoints R ↔ star x = x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

instance : has_star (self_adjoints R) := ⟨id⟩
instance : has_involutive_star (self_adjoints R) := ⟨λ _, rfl⟩

@[simp] lemma star_eq {x : self_adjoints R} : star x = x := rfl
@[simp] lemma star_coe_eq {x : self_adjoints R} : star (x : R) = x := x.prop

instance : star_add_monoid (self_adjoints R) := ⟨λ x y, star_eq⟩

end add_group

instance [add_comm_group R] [star_add_monoid R] : add_comm_group (self_adjoints R) :=
{ add_comm := add_comm,
  ..add_subgroup.to_add_group (self_adjoints R) }

section ring
variables [ring R] [star_ring R]

instance : has_one (self_adjoints R) := ⟨⟨1, by rw [mem_iff, star_one]⟩⟩

@[simp] lemma coe_one : (coe : self_adjoints R → R) (1 : self_adjoints R) = (1 : R) := rfl

lemma one_mem : (1 : R) ∈ self_adjoints R := by simp only [mem_iff, star_one]

lemma conjugate {x : R} (hx : x ∈ self_adjoints R) {z : R} : z * x * star z ∈ self_adjoints R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

lemma conjugate' {x : R} (hx : x ∈ self_adjoints R) {z : R} : star z * x * z ∈ self_adjoints R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

end ring

section comm_ring
variables [comm_ring R] [star_ring R]

instance : has_mul (self_adjoints R) :=
⟨λ x y, ⟨(x : R) * y, by simp only [mem_iff, star_mul', star_coe_eq]⟩⟩

@[simp] lemma coe_mul (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x * y) = (x : R) * y := rfl

instance : comm_ring (self_adjoints R) :=
{ mul_assoc := λ x y z, by { ext, exact mul_assoc _ _ _ },
  one_mul := λ x, by { ext, simp only [coe_mul, one_mul, coe_one] },
  mul_one := λ x, by { ext, simp only [mul_one, coe_mul, coe_one] },
  mul_comm := λ x y, by { ext, exact mul_comm _ _ },
  left_distrib := λ x y z, by { ext, exact left_distrib _ _ _ },
  right_distrib := λ x y z, by { ext, exact right_distrib _ _ _ },
  ..self_adjoints.add_comm_group,
  ..self_adjoints.has_one,
  ..self_adjoints.has_mul }

end comm_ring

section field

variables [field R] [star_ring R]

instance : field (self_adjoints R) :=
{ inv :=  λ x, ⟨(x.val)⁻¹, by simp only [mem_iff, star_inv', star_coe_eq, subtype.val_eq_coe]⟩,
  exists_pair_ne := ⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩,
  mul_inv_cancel := λ x hx, by { ext, exact mul_inv_cancel (λ H, hx $ subtype.eq H) },
  inv_zero := by { ext, exact inv_zero },
  ..self_adjoints.comm_ring }

@[simp] lemma coe_inv (x : self_adjoints R) : (coe : self_adjoints R → R) (x⁻¹) = (x : R)⁻¹ := rfl

end field

end self_adjoints
