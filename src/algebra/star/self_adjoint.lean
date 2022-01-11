/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.star.basic
import group_theory.subgroup.basic

/-!
# Self-adjoint elements of a star additive group

This file defines `self_adjoint R`, where `R` is a star additive monoid, as the additive subgroup
containing the elements that satisfy `star x = x`. This includes, for instance, Hermitian
operators on Hilbert spaces.

## TODO

* If `R` is a `star_module R₂ R`, put a module structure on `self_adjoint R`. This would naturally
  be a `module (self_adjoint R₂) (self_adjoint R)`, but doing this literally would be undesirable
  since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)` and not
  `module (self_adjoint ℂ) (self_adjoint R)`. One way of doing this would be to add the typeclass
  `[has_trivial_star R]`, of which `ℝ` would be an instance, and then add a
  `[module R (self_adjoint E)]` instance whenever we have `[module R E] [has_trivial_star E]`.
  Another one would be to define a `[star_invariant_scalars R E]` to express the fact that
  `star (x • v) = x • star v`.

* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/

variables (R : Type*)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def self_adjoint [add_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | star x = x},
  zero_mem' := star_zero R,
  add_mem' := λ x y (hx : star x = x) (hy : star y = y),
                show star (x + y) = x + y, by simp only [star_add x y, hx, hy],
  neg_mem' := λ x (hx : star x = x), show star (-x) = -x, by simp only [hx, star_neg] }
variables {R}

namespace self_adjoint

section add_group
variables [add_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ self_adjoint R ↔ star x = x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

@[simp, norm_cast] lemma star_coe_eq {x : self_adjoint R} : star (x : R) = x := x.prop

end add_group

instance [add_comm_group R] [star_add_monoid R] : add_comm_group (self_adjoint R) :=
{ add_comm := add_comm,
  ..add_subgroup.to_add_group (self_adjoint R) }

section ring
variables [ring R] [star_ring R]

instance : has_one (self_adjoint R) := ⟨⟨1, by rw [mem_iff, star_one]⟩⟩

@[simp, norm_cast] lemma coe_one : (coe : self_adjoint R → R) (1 : self_adjoint R) = (1 : R) := rfl

lemma one_mem : (1 : R) ∈ self_adjoint R := by simp only [mem_iff, star_one]

lemma bit0_mem {x : R} (hx : x ∈ self_adjoint R) : bit0 x ∈ self_adjoint R :=
by simp only [mem_iff, star_bit0, mem_iff.mp hx]

lemma bit1_mem {x : R} (hx : x ∈ self_adjoint R) : bit1 x ∈ self_adjoint R :=
by simp only [mem_iff, star_bit1, mem_iff.mp hx]

lemma conjugate {x : R} (hx : x ∈ self_adjoint R) (z : R) : z * x * star z ∈ self_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

lemma conjugate' {x : R} (hx : x ∈ self_adjoint R) (z : R) : star z * x * z ∈ self_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

end ring

section comm_ring
variables [comm_ring R] [star_ring R]

instance : has_mul (self_adjoint R) :=
⟨λ x y, ⟨(x : R) * y, by simp only [mem_iff, star_mul', star_coe_eq]⟩⟩

@[simp, norm_cast] lemma coe_mul (x y : self_adjoint R) :
  (coe : self_adjoint R → R) (x * y) = (x : R) * y := rfl

instance : comm_ring (self_adjoint R) :=
{ mul_assoc := λ x y z, by { ext, exact mul_assoc _ _ _ },
  one_mul := λ x, by { ext, simp only [coe_mul, one_mul, coe_one] },
  mul_one := λ x, by { ext, simp only [mul_one, coe_mul, coe_one] },
  mul_comm := λ x y, by { ext, exact mul_comm _ _ },
  left_distrib := λ x y z, by { ext, exact left_distrib _ _ _ },
  right_distrib := λ x y z, by { ext, exact right_distrib _ _ _ },
  ..self_adjoint.add_comm_group,
  ..self_adjoint.has_one,
  ..self_adjoint.has_mul }

end comm_ring

section field

variables [field R] [star_ring R]

instance : field (self_adjoint R) :=
{ inv :=  λ x, ⟨(x.val)⁻¹, by simp only [mem_iff, star_inv', star_coe_eq, subtype.val_eq_coe]⟩,
  exists_pair_ne := ⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩,
  mul_inv_cancel := λ x hx, by { ext, exact mul_inv_cancel (λ H, hx $ subtype.eq H) },
  inv_zero := by { ext, exact inv_zero },
  ..self_adjoint.comm_ring }

@[simp, norm_cast] lemma coe_inv (x : self_adjoint R) :
  (coe : self_adjoint R → R) (x⁻¹) = (x : R)⁻¹ := rfl

end field

end self_adjoint
