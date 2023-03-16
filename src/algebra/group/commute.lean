/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import algebra.group.semiconj

/-!
# Commuting pairs of elements in monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/

variables {G : Type*}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive add_commute "Two elements additively commute if `a + b = b + a`"]
def commute {S : Type*} [has_mul S] (a b : S) : Prop := semiconj_by a b b

namespace commute

section has_mul

variables {S : Type*} [has_mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected lemma eq {a b : S} (h : commute a b) : a * b = b * a := h

/-- Any element commutes with itself. -/
@[refl, simp, to_additive "Any element commutes with itself."]
protected lemma refl (a : S) : commute a a := eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected lemma symm {a b : S} (h : commute a b) : commute b a := eq.symm h

@[to_additive] protected theorem semiconj_by {a b : S} (h : commute a b) : semiconj_by a b b := h

@[to_additive]
protected theorem symm_iff {a b : S} : commute a b ↔ commute b a :=
⟨commute.symm, commute.symm⟩

@[to_additive] instance : is_refl S commute := ⟨commute.refl⟩

-- This instance is useful for `finset.noncomm_prod`
@[to_additive] instance on_is_refl {f : G → S} : is_refl G (λ a b, commute (f a) (f b)) :=
⟨λ _, commute.refl _⟩

end has_mul

section semigroup

variables {S : Type*} [semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
lemma mul_right (hab : commute a b) (hac : commute a c) : commute a (b * c) := hab.mul_right hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
lemma mul_left (hac : commute a c) (hbc : commute b c) : commute (a * b) c := hac.mul_left hbc

@[to_additive] protected lemma right_comm (h : commute b c) (a : S) :
  a * b * c = a * c * b :=
by simp only [mul_assoc, h.eq]

@[to_additive] protected lemma left_comm (h : commute a b) (c) :
  a * (b * c) = b * (a * c) :=
by simp only [← mul_assoc, h.eq]

end semigroup

@[to_additive]
protected theorem all {S : Type*} [comm_semigroup S] (a b : S) : commute a b := mul_comm a b

section mul_one_class

variables {M : Type*} [mul_one_class M]

@[simp, to_additive] theorem one_right (a : M) : commute a 1 := semiconj_by.one_right a
@[simp, to_additive] theorem one_left (a : M) : commute 1 a := semiconj_by.one_left a

end mul_one_class

section monoid

variables {M : Type*} [monoid M] {a b : M} {u u₁ u₂ : Mˣ}

@[simp, to_additive]
theorem pow_right (h : commute a b) (n : ℕ) : commute a (b ^ n) := h.pow_right n
@[simp, to_additive]
theorem pow_left (h : commute a b) (n : ℕ) : commute (a ^ n) b := (h.symm.pow_right n).symm
@[simp, to_additive]
theorem pow_pow (h : commute a b) (m n : ℕ) : commute (a ^ m) (b ^ n) :=
(h.pow_left m).pow_right n

@[simp, to_additive]
theorem self_pow (a : M) (n : ℕ) : commute a (a ^ n) := (commute.refl a).pow_right n
@[simp, to_additive]
theorem pow_self (a : M) (n : ℕ) : commute (a ^ n) a := (commute.refl a).pow_left n
@[simp, to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : commute (a ^ m) (a ^ n) :=
(commute.refl a).pow_pow m n

@[to_additive succ_nsmul'] theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
(pow_succ a n).trans (self_pow _ _)

@[to_additive] theorem units_inv_right : commute a u → commute a ↑u⁻¹ :=
semiconj_by.units_inv_right

@[simp, to_additive] theorem units_inv_right_iff :
  commute a ↑u⁻¹ ↔ commute a u :=
semiconj_by.units_inv_right_iff

@[to_additive] theorem units_inv_left : commute ↑u a → commute ↑u⁻¹ a :=
semiconj_by.units_inv_symm_left

@[simp, to_additive]
theorem units_inv_left_iff: commute ↑u⁻¹ a ↔ commute ↑u a :=
semiconj_by.units_inv_symm_left_iff

@[to_additive]
theorem units_coe : commute u₁ u₂ → commute (u₁ : M) u₂ := semiconj_by.units_coe
@[to_additive]
theorem units_of_coe : commute (u₁ : M) u₂ → commute u₁ u₂ := semiconj_by.units_of_coe
@[simp, to_additive]
theorem units_coe_iff : commute (u₁ : M) u₂ ↔ commute u₁ u₂ := semiconj_by.units_coe_iff

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the left summand is an
additive unit."]
def _root_.units.left_of_mul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : commute a b) : Mˣ :=
{ val := a,
  inv := b * ↑u⁻¹,
  val_inv := by rw [← mul_assoc, hu, u.mul_inv],
  inv_val := have commute a u, from hu ▸ (commute.refl _).mul_right hc,
    by rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv] }

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the right summand is
an additive unit."]
def _root_.units.right_of_mul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : commute a b) : Mˣ :=
u.left_of_mul b a (hc.eq ▸ hu) hc.symm

@[to_additive] lemma is_unit_mul_iff (h : commute a b) :
  is_unit (a * b) ↔ is_unit a ∧ is_unit b :=
⟨λ ⟨u, hu⟩, ⟨(u.left_of_mul a b hu.symm h).is_unit, (u.right_of_mul a b hu.symm h).is_unit⟩,
  λ H, H.1.mul H.2⟩

@[simp, to_additive] lemma _root_.is_unit_mul_self_iff :
  is_unit (a * a) ↔ is_unit a :=
(commute.refl a).is_unit_mul_iff.trans (and_self _)

end monoid

section division_monoid
variables [division_monoid G] {a b : G}

@[to_additive] lemma inv_inv : commute a b → commute a⁻¹ b⁻¹ := semiconj_by.inv_inv_symm
@[simp, to_additive]
lemma inv_inv_iff : commute a⁻¹ b⁻¹ ↔ commute a b := semiconj_by.inv_inv_symm_iff

end division_monoid

section group

variables [group G] {a b : G}

@[to_additive]
theorem inv_right : commute a b → commute a b⁻¹ := semiconj_by.inv_right
@[simp, to_additive]
theorem inv_right_iff : commute a b⁻¹ ↔ commute a b := semiconj_by.inv_right_iff

@[to_additive] theorem inv_left :  commute a b → commute a⁻¹ b := semiconj_by.inv_symm_left
@[simp, to_additive]
theorem inv_left_iff : commute a⁻¹ b ↔ commute a b := semiconj_by.inv_symm_left_iff

@[to_additive]
protected theorem inv_mul_cancel (h : commute a b) : a⁻¹ * b * a = b :=
by rw [h.inv_left.eq, inv_mul_cancel_right]

@[to_additive]
theorem inv_mul_cancel_assoc (h : commute a b) : a⁻¹ * (b * a) = b :=
by rw [← mul_assoc, h.inv_mul_cancel]

@[to_additive]
protected theorem mul_inv_cancel (h : commute a b) : a * b * a⁻¹ = b :=
by rw [h.eq, mul_inv_cancel_right]

@[to_additive]
theorem mul_inv_cancel_assoc (h : commute a b) : a * (b * a⁻¹) = b :=
by rw [← mul_assoc, h.mul_inv_cancel]

end group

end commute

section comm_group

variables [comm_group G] (a b : G)

@[simp, to_additive] lemma mul_inv_cancel_comm : a * b * a⁻¹ = b :=
(commute.all a b).mul_inv_cancel

@[simp, to_additive] lemma mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
(commute.all a b).mul_inv_cancel_assoc

@[simp, to_additive] lemma inv_mul_cancel_comm : a⁻¹ * b * a = b :=
(commute.all a b).inv_mul_cancel

@[simp, to_additive] lemma inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
(commute.all a b).inv_mul_cancel_assoc

end comm_group
