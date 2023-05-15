/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import algebra.ring.regular
import group_theory.submonoid.basic

/-!

# (Right) Ore sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines right Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

namespace ore_localization

section monoid

/-- A submonoid `S` of a monoid `R` is (right) Ore if common factors on the left can be turned
into common factors on the right, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `r * u = s * v`. -/
class ore_set {R : Type*} [monoid R] (S : submonoid R) :=
(ore_left_cancel : ∀ (r₁ r₂ : R) (s : S), ↑s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s')
(ore_num : R → S → R)
(ore_denom : R → S → S)
(ore_eq : ∀ (r : R) (s : S), r * ore_denom r s = s * ore_num r s)

variables {R : Type*} [monoid R] {S : submonoid R} [ore_set S]

/-- Common factors on the left can be turned into common factors on the right, a weak form of
cancellability. -/
lemma ore_left_cancel (r₁ r₂ : R) (s : S) (h : ↑s * r₁ = s * r₂) : ∃ s' : S, r₁ * s' = r₂ * s' :=
ore_set.ore_left_cancel r₁ r₂ s h

/-- The Ore numerator of a fraction. -/
def ore_num (r : R) (s : S) : R := ore_set.ore_num r s

/-- The Ore denominator of a fraction. -/
def ore_denom (r : R) (s : S) : S := ore_set.ore_denom r s

/-- The Ore condition of a fraction, expressed in terms of `ore_num` and `ore_denom`. -/
lemma ore_eq (r : R) (s : S) : r * (ore_denom r s) = s * (ore_num r s) := ore_set.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
def ore_condition (r : R) (s : S) : Σ' r' : R, Σ' s' : S, r * s' = s * r' :=
⟨ore_num r s, ore_denom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
instance ore_set_bot : ore_set (⊥ : submonoid R) :=
{ ore_left_cancel := λ _ _ s h,
    ⟨s, begin
          rcases s with ⟨s, hs⟩,
          rw submonoid.mem_bot at hs,
          subst hs,
          rw [set_like.coe_mk, one_mul, one_mul] at h,
          subst h
        end⟩,
  ore_num := λ r _, r,
  ore_denom := λ _ s, s,
  ore_eq := λ _ s, by { rcases s with ⟨s, hs⟩, rw submonoid.mem_bot at hs, simp [hs] } }

/-- Every submonoid of a commutative monoid is an Ore set. -/
@[priority 100]
instance ore_set_comm {R} [comm_monoid R] (S : submonoid R) : ore_set S :=
{ ore_left_cancel := λ m n s h, ⟨s, by rw [mul_comm n s, mul_comm m s, h]⟩,
  ore_num := λ r _, r,
  ore_denom := λ _ s, s,
  ore_eq := λ r s, by rw mul_comm }

end monoid

/-- Cancellability in monoids with zeros can act as a replacement for the `ore_left_cancel`
condition of an ore set. -/
def ore_set_of_cancel_monoid_with_zero
  {R : Type*} [cancel_monoid_with_zero R] {S : submonoid R}
  (ore_num : R → S → R) (ore_denom : R → S → S)
  (ore_eq : ∀ (r : R) (s : S), r * (ore_denom r s) = s * (ore_num r s)) :
  ore_set S :=
{ ore_left_cancel := λ r₁ r₂ s h, ⟨s, mul_eq_mul_right_iff.mpr (mul_eq_mul_left_iff.mp h)⟩,
  ore_num := ore_num,
  ore_denom := ore_denom,
  ore_eq := ore_eq }

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
def ore_set_of_no_zero_divisors
  {R : Type*} [ring R] [no_zero_divisors R] {S : submonoid R}
  (ore_num : R → S → R) (ore_denom : R → S → S)
  (ore_eq : ∀ (r : R) (s : S), r * (ore_denom r s) = s * (ore_num r s)) :
  ore_set S :=
begin
  letI : cancel_monoid_with_zero R := no_zero_divisors.to_cancel_monoid_with_zero,
  exact ore_set_of_cancel_monoid_with_zero ore_num ore_denom ore_eq
end

end ore_localization
