/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import algebra.group.semiconj

/-!
# Commuting pairs of elements in monoids

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

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive add_commute "Two elements additively commute if `a + b = b + a`"]
def commute {S : Type*} [has_mul S] (a b : S) : Prop := semiconj_by a b b

namespace commute

section has_mul

variables {S : Type*} [has_mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive] protected theorem eq {a b : S} (h : commute a b) : a * b = b * a := h

/-- Any element commutes with itself. -/
@[refl, simp, to_additive] protected theorem refl (a : S) : commute a a := eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive] protected theorem symm {a b : S} (h : commute a b) : commute b a :=
eq.symm h

@[to_additive] protected theorem semiconj_by {a b : S} (h : commute a b) : semiconj_by a b b := h

@[to_additive]
protected theorem symm_iff {a b : S} : commute a b ↔ commute b a :=
⟨commute.symm, commute.symm⟩

end has_mul

section semigroup

variables {S : Type*} [semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive] theorem mul_right (hab : commute a b) (hac : commute a c) :
  commute a (b * c) :=
hab.mul_right hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive] theorem mul_left (hac : commute a c) (hbc : commute b c) :
  commute (a * b) c :=
hac.mul_left hbc

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

variables {M : Type*} [monoid M]

@[to_additive] theorem units_inv_right {a : M} {u : units M} : commute a u → commute a ↑u⁻¹ :=
semiconj_by.units_inv_right

@[simp, to_additive] theorem units_inv_right_iff {a : M} {u : units M} :
  commute a ↑u⁻¹ ↔ commute a u :=
semiconj_by.units_inv_right_iff

@[to_additive] theorem units_inv_left {u : units M} {a : M} : commute ↑u a → commute ↑u⁻¹ a :=
semiconj_by.units_inv_symm_left

@[simp, to_additive]
theorem units_inv_left_iff {u : units M} {a : M}: commute ↑u⁻¹ a ↔ commute ↑u a :=
semiconj_by.units_inv_symm_left_iff

variables {u₁ u₂ : units M}

@[to_additive]
theorem units_coe : commute u₁ u₂ → commute (u₁ : M) u₂ := semiconj_by.units_coe
@[to_additive]
theorem units_of_coe : commute (u₁ : M) u₂ → commute u₁ u₂ := semiconj_by.units_of_coe
@[simp, to_additive]
theorem units_coe_iff : commute (u₁ : M) u₂ ↔ commute u₁ u₂ := semiconj_by.units_coe_iff

@[to_additive] lemma is_unit_mul_iff {a b : M} (h : commute a b) :
  is_unit (a * b) ↔ is_unit a ∧ is_unit b :=
begin
  refine ⟨_, λ H, H.1.mul H.2⟩,
  rintro ⟨u, hu⟩,
  have : b * ↑u⁻¹ * a = 1,
  { have : commute a u := hu.symm ▸ (commute.refl _).mul_right h,
    rw [← this.units_inv_right.right_comm, ← h.eq, ← hu, u.mul_inv] },
  split,
  { refine ⟨⟨a, b * ↑u⁻¹, _, this⟩, rfl⟩,
    rw [← mul_assoc, ← hu, u.mul_inv] },
  { rw mul_assoc at this,
    refine ⟨⟨b, ↑u⁻¹ * a, this, _⟩, rfl⟩,
    rw [mul_assoc, ← hu, u.inv_mul] }
end

@[simp, to_additive] lemma _root_.is_unit_mul_self_iff {a : M} :
  is_unit (a * a) ↔ is_unit a :=
(commute.refl a).is_unit_mul_iff.trans (and_self _)

end monoid

section group

variables {G : Type*} [group G] {a b : G}

@[to_additive]
theorem inv_right : commute a b → commute a b⁻¹ := semiconj_by.inv_right
@[simp, to_additive]
theorem inv_right_iff : commute a b⁻¹ ↔ commute a b := semiconj_by.inv_right_iff

@[to_additive] theorem inv_left :  commute a b → commute a⁻¹ b := semiconj_by.inv_symm_left
@[simp, to_additive]
theorem inv_left_iff : commute a⁻¹ b ↔ commute a b := semiconj_by.inv_symm_left_iff

@[to_additive]
theorem inv_inv : commute a b → commute a⁻¹ b⁻¹ := semiconj_by.inv_inv_symm
@[simp, to_additive]
theorem inv_inv_iff : commute a⁻¹ b⁻¹ ↔ commute a b := semiconj_by.inv_inv_symm_iff

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

variables {G : Type*} [comm_group G] (a b : G)

@[simp, to_additive] lemma mul_inv_cancel_comm : a * b * a⁻¹ = b :=
(commute.all a b).mul_inv_cancel

@[simp, to_additive] lemma mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
(commute.all a b).mul_inv_cancel_assoc

@[simp, to_additive] lemma inv_mul_cancel_comm : a⁻¹ * b * a = b :=
(commute.all a b).inv_mul_cancel

@[simp, to_additive] lemma inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
(commute.all a b).inv_mul_cancel_assoc

end comm_group
