/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import algebra.group.units

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `commute a b = semiconj_by a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

universes u v

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive add_semiconj_by "`x` is additive semiconjugate to `y` by `a` if `a + x = y + a`"]
def semiconj_by {M : Type u} [has_mul M] (a x y : M) : Prop := a * x = y * a

namespace semiconj_by

/-- Equality behind `semiconj_by a x y`; useful for rewriting. -/
@[to_additive]
protected lemma eq {S : Type u} [has_mul S] {a x y : S} (h : semiconj_by a x y) :
  a * x = y * a := h

section semigroup

variables {S : Type u} [semigroup S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[simp, to_additive] lemma mul_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x * x') (y * y') :=
by unfold semiconj_by; assoc_rw [h.eq, h'.eq]

/-- If both `a` and `b` semiconjugate `x` to `y`, then so does `a * b`. -/
@[to_additive]
lemma mul_left (ha : semiconj_by a y z) (hb : semiconj_by b x y) :
  semiconj_by (a * b) x z :=
by unfold semiconj_by; assoc_rw [hb.eq, ha.eq, mul_assoc]

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
semigroup is transitive."]
protected lemma transitive : transitive (λ a b : S, ∃ c, semiconj_by c a b) :=
λ a b c ⟨x, hx⟩ ⟨y, hy⟩, ⟨y * x, hy.mul_left hx⟩

end semigroup

section mul_one_class

variables {M : Type u} [mul_one_class M]

/-- Any element semiconjugates `1` to `1`. -/
@[simp, to_additive]
lemma one_right (a : M) : semiconj_by a 1 1 := by rw [semiconj_by, mul_one, one_mul]

/-- One semiconjugates any element to itself. -/
@[simp, to_additive]
lemma one_left (x : M) : semiconj_by 1 x x := eq.symm $ one_right x

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on ` mul_one_class` type) is reflexive. -/
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
monoid (or, more generally, on a `add_zero_class` type) is reflexive."]
protected lemma reflexive : reflexive (λ a b : M, ∃ c, semiconj_by c a b) :=
λ a, ⟨1, one_left a⟩

end mul_one_class

section monoid

variables {M : Type u} [monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive] lemma units_inv_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  semiconj_by a ↑x⁻¹ ↑y⁻¹ :=
calc a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ : by rw [units.inv_mul_cancel_left]
          ... = ↑y⁻¹ * a              : by rw [← h.eq, mul_assoc, units.mul_inv_cancel_right]

@[simp, to_additive] lemma units_inv_right_iff {a : M} {x y : units M} :
  semiconj_by a ↑x⁻¹ ↑y⁻¹ ↔ semiconj_by a x y :=
⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive] lemma units_inv_symm_left {a : units M} {x y : M} (h : semiconj_by ↑a x y) :
  semiconj_by ↑a⁻¹ y x :=
calc ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) : by rw [units.mul_inv_cancel_right]
          ... = x * ↑a⁻¹              : by rw [← h.eq, ← mul_assoc, units.inv_mul_cancel_left]

@[simp, to_additive] lemma units_inv_symm_left_iff {a : units M} {x y : M} :
  semiconj_by ↑a⁻¹ y x ↔ semiconj_by ↑a x y :=
⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive] theorem units_coe {a x y : units M} (h : semiconj_by a x y) :
  semiconj_by (a : M) x y :=
congr_arg units.val h

@[to_additive] theorem units_of_coe {a x y : units M} (h : semiconj_by (a : M) x y) :
  semiconj_by a x y :=
units.ext h

@[simp, to_additive] theorem units_coe_iff {a x y : units M} :
  semiconj_by (a : M) x y ↔ semiconj_by a x y :=
⟨units_of_coe, units_coe⟩

end monoid

section group

variables {G : Type u} [group G] {a x y : G}

@[simp, to_additive] lemma inv_right_iff : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
@units_inv_right_iff G _ a ⟨x, x⁻¹, mul_inv_self x, inv_mul_self x⟩
  ⟨y, y⁻¹, mul_inv_self y, inv_mul_self y⟩

@[to_additive] lemma inv_right : semiconj_by a x y → semiconj_by a x⁻¹ y⁻¹ :=
inv_right_iff.2

@[simp, to_additive] lemma inv_symm_left_iff : semiconj_by a⁻¹ y x ↔ semiconj_by a x y :=
@units_inv_symm_left_iff G _ ⟨a, a⁻¹, mul_inv_self a, inv_mul_self a⟩ _ _

@[to_additive] lemma inv_symm_left : semiconj_by a x y → semiconj_by a⁻¹ y x :=
inv_symm_left_iff.2

@[to_additive] lemma inv_inv_symm (h : semiconj_by a x y) : semiconj_by a⁻¹ y⁻¹ x⁻¹ :=
h.inv_right.inv_symm_left

-- this is not a simp lemma because it can be deduced from other simp lemmas
@[to_additive] lemma inv_inv_symm_iff : semiconj_by a⁻¹ y⁻¹ x⁻¹ ↔ semiconj_by a x y :=
inv_right_iff.trans inv_symm_left_iff

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive] lemma conj_mk (a x : G) : semiconj_by a x (a * x * a⁻¹) :=
by unfold semiconj_by; rw [mul_assoc, inv_mul_self, mul_one]

end group

end semiconj_by

@[simp, to_additive add_semiconj_by_iff_eq]
lemma semiconj_by_iff_eq {M : Type u} [cancel_comm_monoid M] {a x y : M} :
  semiconj_by a x y ↔ x = y :=
⟨λ h, mul_left_cancel (h.trans (mul_comm _ _)), λ h, by rw [h, semiconj_by, mul_comm] ⟩

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive]
lemma units.mk_semiconj_by {M : Type u} [monoid M] (u : units M) (x : M) :
  semiconj_by ↑u x (u * x * ↑u⁻¹) :=
by unfold semiconj_by; rw [units.inv_mul_cancel_right]
