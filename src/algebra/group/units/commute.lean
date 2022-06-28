/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import algebra.group.units
import algebra.group.commute

/-!
# Additional lemmas about `semiconj_by` and `commute` for `units` and other groups
-/

universes u

namespace semiconj_by

section monoid
variables {M : Type u} [monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive "If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it
semiconjugates `-x` to `-y`."]
lemma units_inv_right {a : M} {x y : Mˣ} (h : semiconj_by a x y) : semiconj_by a ↑x⁻¹ ↑y⁻¹ :=
calc a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ : by rw [units.inv_mul_cancel_left]
          ... = ↑y⁻¹ * a              : by rw [← h.eq, mul_assoc, units.mul_inv_cancel_right]

@[simp, to_additive] lemma units_inv_right_iff {a : M} {x y : Mˣ} :
  semiconj_by a ↑x⁻¹ ↑y⁻¹ ↔ semiconj_by a x y :=
⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive "If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to
`x`."]
lemma units_inv_symm_left {a : Mˣ} {x y : M} (h : semiconj_by ↑a x y) :
  semiconj_by ↑a⁻¹ y x :=
calc ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) : by rw [units.mul_inv_cancel_right]
          ... = x * ↑a⁻¹              : by rw [← h.eq, ← mul_assoc, units.inv_mul_cancel_left]

@[simp, to_additive] lemma units_inv_symm_left_iff {a : Mˣ} {x y : M} :
  semiconj_by ↑a⁻¹ y x ↔ semiconj_by ↑a x y :=
⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive] theorem units_coe {a x y : Mˣ} (h : semiconj_by a x y) :
  semiconj_by (a : M) x y :=
congr_arg units.val h

@[to_additive] theorem units_of_coe {a x y : Mˣ} (h : semiconj_by (a : M) x y) :
  semiconj_by a x y :=
units.ext h

@[simp, to_additive] theorem units_coe_iff {a x y : Mˣ} :
  semiconj_by (a : M) x y ↔ semiconj_by a x y :=
⟨units_of_coe, units_coe⟩

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
lemma _root_.units.mk_semiconj_by (u : Mˣ) (x : M) : semiconj_by ↑u x (u * x * ↑u⁻¹) :=
by unfold semiconj_by; rw [units.inv_mul_cancel_right]

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

end group

end semiconj_by

namespace commute

section monoid
variables {M : Type u} [monoid M] {a b : M} {u u₁ u₂ : Mˣ}

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

@[to_additive] lemma is_unit_mul_iff (h : commute a b) :
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

@[simp, to_additive] lemma _root_.is_unit_mul_self_iff :
  is_unit (a * a) ↔ is_unit a :=
(commute.refl a).is_unit_mul_iff.trans (and_self _)

end monoid

section group
variables {G : Type u} [group G] {a b : G}

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
variables {G : Type u} [comm_group G] (a b : G)

@[simp, to_additive] lemma mul_inv_cancel_comm : a * b * a⁻¹ = b :=
(commute.all a b).mul_inv_cancel

@[simp, to_additive] lemma mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
(commute.all a b).mul_inv_cancel_assoc

@[simp, to_additive] lemma inv_mul_cancel_comm : a⁻¹ * b * a = b :=
(commute.all a b).inv_mul_cancel

@[simp, to_additive] lemma inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
(commute.all a b).inv_mul_cancel_assoc

end comm_group
