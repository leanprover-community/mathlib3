/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import algebra.star.basic
import group_theory.submonoid.operations

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid containing the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

## Tags

unitary
-/

/--
In a `star_monoid R`, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [monoid R] [star_monoid R] : submonoid R :=
{ carrier := {U | star U * U = 1 ∧ U * star U = 1},
  one_mem' := by simp only [mul_one, and_self, set.mem_set_of_eq, star_one],
  mul_mem' := λ U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩,
  begin
    refine ⟨_, _⟩,
    { calc star (U * B) * (U * B) = star B * star U * U * B     : by simp only [mul_assoc, star_mul]
                            ...   = star B * (star U * U) * B   : by rw [←mul_assoc]
                            ...   = 1                           : by rw [hA₁, mul_one, hB₁] },
    { calc U * B * star (U * B) = U * B * (star B * star U)     : by rw [star_mul]
                            ... = U * (B * star B) * star U     : by simp_rw [←mul_assoc]
                            ... = 1                             : by rw [hB₂, mul_one, hA₂] }
  end }

variables {R : Type*}

namespace unitary
variables [monoid R] [star_monoid R]

@[simp] lemma star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 := hU.1
@[simp] lemma mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 := hU.2

lemma star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp] lemma star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
⟨λ h, star_star U ▸ star_mem h, star_mem⟩

instance : has_star (unitary R) := ⟨λ U, ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast] lemma coe_star {U : unitary R} : ↑(star U) = (star U : R) := rfl

lemma coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 := star_mul_self_of_mem U.prop
lemma coe_mul_star_self (U : unitary R) :  (U : R) * star U = 1 := mul_star_self_of_mem U.prop

@[simp] lemma star_mul_self (U : unitary R) : star U * U = 1 := subtype.ext $ coe_star_mul_self U
@[simp] lemma mul_star_self (U : unitary R) : U * star U = 1 := subtype.ext $ coe_mul_star_self U


instance : group (unitary R) :=
{ inv := λ U, star U,
  mul_left_inv := star_mul_self,
  ..submonoid.to_monoid _ }

instance : has_involutive_star (unitary R) :=
⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

instance : star_monoid (unitary R) :=
⟨λ _ _, by { ext, simp only [coe_star, submonoid.coe_mul, star_mul] }⟩

instance : inhabited (unitary R) := ⟨1⟩

lemma star_eq_inv (U : unitary R) : star U = U⁻¹ := rfl

end unitary
