/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Opposites.
-/
import data.opposite
import algebra.field

namespace opposite
universes u

variables (α : Type u)

instance [has_add α] : has_add (opposite α) :=
{ add := λ x y, op (unop x + unop y) }

instance [add_semigroup α] : add_semigroup (opposite α) :=
{ add_assoc := λ x y z, unop_inj $ add_assoc (unop x) (unop y) (unop z),
  .. opposite.has_add α }

instance [add_left_cancel_semigroup α] : add_left_cancel_semigroup (opposite α) :=
{ add_left_cancel := λ x y z H, unop_inj $ add_left_cancel $ op_inj H,
  .. opposite.add_semigroup α }

instance [add_right_cancel_semigroup α] : add_right_cancel_semigroup (opposite α) :=
{ add_right_cancel := λ x y z H, unop_inj $ add_right_cancel $ op_inj H,
  .. opposite.add_semigroup α }

instance [add_comm_semigroup α] : add_comm_semigroup (opposite α) :=
{ add_comm := λ x y, unop_inj $ add_comm (unop x) (unop y),
  .. opposite.add_semigroup α }

instance [has_zero α] : has_zero (opposite α) :=
{ zero := op 0 }

section
local attribute [reducible] opposite
@[simp] lemma unop_eq_zero_iff [has_zero α] (a : αᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵒᵖ) :=
iff.refl _

@[simp] lemma op_eq_zero_iff [has_zero α] (a : α) : op a = (0 : αᵒᵖ) ↔ a = (0 : α) :=
iff.refl _
end

instance [add_monoid α] : add_monoid (opposite α) :=
{ zero_add := λ x, unop_inj $ zero_add $ unop x,
  add_zero := λ x, unop_inj $ add_zero $ unop x,
  .. opposite.add_semigroup α, .. opposite.has_zero α }

instance [add_comm_monoid α] : add_comm_monoid (opposite α) :=
{ .. opposite.add_monoid α, .. opposite.add_comm_semigroup α }

instance [has_neg α] : has_neg (opposite α) :=
{ neg := λ x, op $ -(unop x) }

instance [add_group α] : add_group (opposite α) :=
{ add_left_neg := λ x, unop_inj $ add_left_neg $ unop x,
  .. opposite.add_monoid α, .. opposite.has_neg α }

instance [add_comm_group α] : add_comm_group (opposite α) :=
{ .. opposite.add_group α, .. opposite.add_comm_monoid α }

instance [has_mul α] : has_mul (opposite α) :=
{ mul := λ x y, op (unop y * unop x) }

instance [semigroup α] : semigroup (opposite α) :=
{ mul_assoc := λ x y z, unop_inj $ eq.symm $ mul_assoc (unop z) (unop y) (unop x),
  .. opposite.has_mul α }

instance [right_cancel_semigroup α] : left_cancel_semigroup (opposite α) :=
{ mul_left_cancel := λ x y z H, unop_inj $ mul_right_cancel $ op_inj H,
  .. opposite.semigroup α }

instance [left_cancel_semigroup α] : right_cancel_semigroup (opposite α) :=
{ mul_right_cancel := λ x y z H, unop_inj $ mul_left_cancel $ op_inj H,
  .. opposite.semigroup α }

instance [comm_semigroup α] : comm_semigroup (opposite α) :=
{ mul_comm := λ x y, unop_inj $ mul_comm (unop y) (unop x),
  .. opposite.semigroup α }

instance [has_one α] : has_one (opposite α) :=
{ one := op 1 }

section
local attribute [reducible] opposite
@[simp] lemma unop_eq_one_iff [has_one α] (a : αᵒᵖ) : a.unop = 1 ↔ a = 1 :=
iff.refl _

@[simp] lemma op_eq_one_iff [has_one α] (a : α) : op a = 1 ↔ a = 1 :=
iff.refl _
end

instance [monoid α] : monoid (opposite α) :=
{ one_mul := λ x, unop_inj $ mul_one $ unop x,
  mul_one := λ x, unop_inj $ one_mul $ unop x,
  .. opposite.semigroup α, .. opposite.has_one α }

instance [comm_monoid α] : comm_monoid (opposite α) :=
{ .. opposite.monoid α, .. opposite.comm_semigroup α }

instance [has_inv α] : has_inv (opposite α) :=
{ inv := λ x, op $ (unop x)⁻¹ }

instance [group α] : group (opposite α) :=
{ mul_left_inv := λ x, unop_inj $ mul_inv_self $ unop x,
  .. opposite.monoid α, .. opposite.has_inv α }

instance [comm_group α] : comm_group (opposite α) :=
{ .. opposite.group α, .. opposite.comm_monoid α }

instance [distrib α] : distrib (opposite α) :=
{ left_distrib := λ x y z, unop_inj $ add_mul (unop y) (unop z) (unop x),
  right_distrib := λ x y z, unop_inj $ mul_add (unop z) (unop x) (unop y),
  .. opposite.has_add α, .. opposite.has_mul α }

instance [semiring α] : semiring (opposite α) :=
{ zero_mul := λ x, unop_inj $ mul_zero $ unop x,
  mul_zero := λ x, unop_inj $ zero_mul $ unop x,
  .. opposite.add_comm_monoid α, .. opposite.monoid α, .. opposite.distrib α }

instance [ring α] : ring (opposite α) :=
{ .. opposite.add_comm_group α, .. opposite.monoid α, .. opposite.semiring α }

instance [comm_ring α] : comm_ring (opposite α) :=
{ .. opposite.ring α, .. opposite.comm_semigroup α }

instance [has_zero α] [has_one α] [nonzero α] : nonzero (opposite α) :=
{ zero_ne_one := λ h : op (0 : α) = op 1, zero_ne_one (op_inj h) }

instance [integral_domain α] : integral_domain (opposite α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y (H : op (_ * _) = op (0:α)),
    or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_inj H)
      (λ hy, or.inr $ unop_inj $ hy) (λ hx, or.inl $ unop_inj $ hx),
  .. opposite.comm_ring α, .. opposite.nonzero α }

instance [field α] : field (opposite α) :=
{ mul_inv_cancel := λ x hx, unop_inj $ inv_mul_cancel $ λ hx', hx $ unop_inj hx',
  inv_zero := unop_inj inv_zero,
  .. opposite.comm_ring α, .. opposite.nonzero α, .. opposite.has_inv α }

@[simp] lemma op_zero [has_zero α] : op (0 : α) = 0 := rfl
@[simp] lemma unop_zero [has_zero α] : unop (0 : αᵒᵖ) = 0 := rfl

@[simp] lemma op_one [has_one α] : op (1 : α) = 1 := rfl
@[simp] lemma unop_one [has_one α] : unop (1 : αᵒᵖ) = 1 := rfl

variable {α}

@[simp] lemma op_add [has_add α] (x y : α) : op (x + y) = op x + op y := rfl
@[simp] lemma unop_add [has_add α] (x y : αᵒᵖ) : unop (x + y) = unop x + unop y := rfl

@[simp] lemma op_neg [has_neg α] (x : α) : op (-x) = -op x := rfl
@[simp] lemma unop_neg [has_neg α] (x : αᵒᵖ) : unop (-x) = -unop x := rfl

@[simp] lemma op_mul [has_mul α] (x y : α) : op (x * y) = op y * op x := rfl
@[simp] lemma unop_mul [has_mul α] (x y : αᵒᵖ) : unop (x * y) = unop y * unop x := rfl

@[simp] lemma op_inv [has_inv α] (x : α) : op (x⁻¹) = (op x)⁻¹ := rfl
@[simp] lemma unop_inv [has_inv α] (x : αᵒᵖ) : unop (x⁻¹) = (unop x)⁻¹ := rfl

end opposite
