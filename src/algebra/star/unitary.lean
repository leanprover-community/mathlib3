/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import algebra.star.basic
import group_theory.submonoid.membership

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `matrix.unitary_group` for specializations to `unitary (matrix n n R)`.

## Tags

unitary
-/

/--
In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [monoid R] [star_semigroup R] : submonoid R :=
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

section monoid
variables [monoid R] [star_semigroup R]

lemma mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 := iff.rfl
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
{ inv := star,
  mul_left_inv := star_mul_self,
  ..submonoid.to_monoid _ }

instance : has_involutive_star (unitary R) :=
⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

instance : star_semigroup (unitary R) :=
⟨λ _ _, by { ext, simp only [coe_star, submonoid.coe_mul, star_mul] }⟩

instance : inhabited (unitary R) := ⟨1⟩

lemma star_eq_inv (U : unitary R) : star U = U⁻¹ := rfl

lemma star_eq_inv' : (star : unitary R → unitary R) = has_inv.inv := rfl

/-- The unitary elements embed into the units. -/
@[simps]
def to_units : unitary R →* Rˣ :=
{ to_fun := λ x, ⟨x, ↑(x⁻¹), coe_mul_star_self x, coe_star_mul_self x⟩,
  map_one' := units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

lemma to_units_injective : function.injective (to_units : unitary R → Rˣ) :=
λ x y h, subtype.ext $ units.ext_iff.mp h

end monoid

section comm_monoid
variables [comm_monoid R] [star_semigroup R]

instance : comm_group (unitary R) :=
{ ..unitary.group,
  ..submonoid.to_comm_monoid _ }

lemma mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
mem_iff.trans $ and_iff_left_of_imp $ λ h, mul_comm (star U) U ▸ h

lemma mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
mem_iff.trans $ and_iff_right_of_imp $ λ h, mul_comm U (star U) ▸ h

end comm_monoid

section group_with_zero
variables [group_with_zero R] [star_semigroup R]

@[norm_cast] lemma coe_inv (U : unitary R) : ↑(U⁻¹) = (U⁻¹ : R) :=
eq_inv_of_mul_eq_one_right $ coe_mul_star_self _

@[norm_cast] lemma coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) :=
by simp only [div_eq_mul_inv, coe_inv, submonoid.coe_mul]

@[norm_cast] lemma coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U ^ z : R) :=
begin
  induction z,
  { simp [submonoid_class.coe_pow], },
  { simp [coe_inv] },
end

end group_with_zero

section ring
variables [ring R] [star_ring R]

instance : has_neg (unitary R) :=
{ neg := λ U, ⟨-U, by { simp_rw [mem_iff, star_neg, neg_mul_neg], exact U.prop }⟩ }

@[norm_cast] lemma coe_neg (U : unitary R) : ↑(-U) = (-U : R) := rfl

instance : has_distrib_neg (unitary R) :=
subtype.coe_injective.has_distrib_neg _ coe_neg (unitary R).coe_mul

end ring

end unitary
