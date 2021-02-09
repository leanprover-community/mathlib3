/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.opposite
import algebra.field
import algebra.group.commute
import group_theory.group_action.defs
import data.equiv.mul_add

/-!
# Algebraic operations on `αᵒᵖ`

This file records several basic facts about the opposite of an algebraic structure, e.g. the
opposite of a ring is a ring (with multiplication `x * y = yx`). Use is made of the identity
functions `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`.
-/

namespace opposite
universes u

variables (α : Type u)

instance [has_add α] : has_add (opposite α) :=
{ add := λ x y, op (unop x + unop y) }

instance [has_sub α] : has_sub (opposite α) :=
{ sub := λ x y, op (unop x - unop y) }

instance [add_semigroup α] : add_semigroup (opposite α) :=
{ add_assoc := λ x y z, unop_injective $ add_assoc (unop x) (unop y) (unop z),
  .. opposite.has_add α }

instance [add_left_cancel_semigroup α] : add_left_cancel_semigroup (opposite α) :=
{ add_left_cancel := λ x y z H, unop_injective $ add_left_cancel $ op_injective H,
  .. opposite.add_semigroup α }

instance [add_right_cancel_semigroup α] : add_right_cancel_semigroup (opposite α) :=
{ add_right_cancel := λ x y z H, unop_injective $ add_right_cancel $ op_injective H,
  .. opposite.add_semigroup α }

instance [add_comm_semigroup α] : add_comm_semigroup (opposite α) :=
{ add_comm := λ x y, unop_injective $ add_comm (unop x) (unop y),
  .. opposite.add_semigroup α }

instance [has_zero α] : has_zero (opposite α) :=
{ zero := op 0 }

instance [nontrivial α] : nontrivial (opposite α) :=
let ⟨x, y, h⟩ := exists_pair_ne α in nontrivial_of_ne (op x) (op y) (op_injective.ne h)

section
local attribute [reducible] opposite
@[simp] lemma unop_eq_zero_iff [has_zero α] (a : αᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵒᵖ) :=
iff.refl _

@[simp] lemma op_eq_zero_iff [has_zero α] (a : α) : op a = (0 : αᵒᵖ) ↔ a = (0 : α) :=
iff.refl _
end

instance [add_monoid α] : add_monoid (opposite α) :=
{ zero_add := λ x, unop_injective $ zero_add $ unop x,
  add_zero := λ x, unop_injective $ add_zero $ unop x,
  .. opposite.add_semigroup α, .. opposite.has_zero α }

instance [add_comm_monoid α] : add_comm_monoid (opposite α) :=
{ .. opposite.add_monoid α, .. opposite.add_comm_semigroup α }

instance [has_neg α] : has_neg (opposite α) :=
{ neg := λ x, op $ -(unop x) }

instance [add_group α] : add_group (opposite α) :=
{ add_left_neg := λ x, unop_injective $ add_left_neg $ unop x,
  sub_eq_add_neg := λ x y, unop_injective $ sub_eq_add_neg (unop x) (unop y),
  .. opposite.add_monoid α, .. opposite.has_neg α, .. opposite.has_sub α }

instance [add_comm_group α] : add_comm_group (opposite α) :=
{ .. opposite.add_group α, .. opposite.add_comm_monoid α }

instance [has_mul α] : has_mul (opposite α) :=
{ mul := λ x y, op (unop y * unop x) }

instance [semigroup α] : semigroup (opposite α) :=
{ mul_assoc := λ x y z, unop_injective $ eq.symm $ mul_assoc (unop z) (unop y) (unop x),
  .. opposite.has_mul α }

instance [right_cancel_semigroup α] : left_cancel_semigroup (opposite α) :=
{ mul_left_cancel := λ x y z H, unop_injective $ mul_right_cancel $ op_injective H,
  .. opposite.semigroup α }

instance [left_cancel_semigroup α] : right_cancel_semigroup (opposite α) :=
{ mul_right_cancel := λ x y z H, unop_injective $ mul_left_cancel $ op_injective H,
  .. opposite.semigroup α }

instance [comm_semigroup α] : comm_semigroup (opposite α) :=
{ mul_comm := λ x y, unop_injective $ mul_comm (unop y) (unop x),
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
{ one_mul := λ x, unop_injective $ mul_one $ unop x,
  mul_one := λ x, unop_injective $ one_mul $ unop x,
  .. opposite.semigroup α, .. opposite.has_one α }

instance [comm_monoid α] : comm_monoid (opposite α) :=
{ .. opposite.monoid α, .. opposite.comm_semigroup α }

instance [has_inv α] : has_inv (opposite α) :=
{ inv := λ x, op $ (unop x)⁻¹ }

instance [group α] : group (opposite α) :=
{ mul_left_inv := λ x, unop_injective $ mul_inv_self $ unop x,
  .. opposite.monoid α, .. opposite.has_inv α }

instance [comm_group α] : comm_group (opposite α) :=
{ .. opposite.group α, .. opposite.comm_monoid α }

instance [distrib α] : distrib (opposite α) :=
{ left_distrib := λ x y z, unop_injective $ add_mul (unop y) (unop z) (unop x),
  right_distrib := λ x y z, unop_injective $ mul_add (unop z) (unop x) (unop y),
  .. opposite.has_add α, .. opposite.has_mul α }

instance [semiring α] : semiring (opposite α) :=
{ zero_mul := λ x, unop_injective $ mul_zero $ unop x,
  mul_zero := λ x, unop_injective $ zero_mul $ unop x,
  .. opposite.add_comm_monoid α, .. opposite.monoid α, .. opposite.distrib α }

instance [ring α] : ring (opposite α) :=
{ .. opposite.add_comm_group α, .. opposite.monoid α, .. opposite.semiring α }

instance [comm_ring α] : comm_ring (opposite α) :=
{ .. opposite.ring α, .. opposite.comm_semigroup α }

instance [has_zero α] [has_mul α] [no_zero_divisors α] : no_zero_divisors (opposite α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y (H : op (_ * _) = op (0:α)),
    or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_injective H)
      (λ hy, or.inr $ unop_injective $ hy) (λ hx, or.inl $ unop_injective $ hx), }

instance [integral_domain α] : integral_domain (opposite α) :=
{ .. opposite.no_zero_divisors α, .. opposite.comm_ring α, .. opposite.nontrivial α }

instance [field α] : field (opposite α) :=
{ mul_inv_cancel := λ x hx, unop_injective $ inv_mul_cancel $ λ hx', hx $ unop_injective hx',
  inv_zero := unop_injective inv_zero,
  .. opposite.comm_ring α, .. opposite.has_inv α, .. opposite.nontrivial α }

instance (R : Type*) [has_scalar R α] : has_scalar R (opposite α) :=
{ smul := λ c x, op (c • unop x) }

instance (R : Type*) [monoid R] [mul_action R α] : mul_action R (opposite α) :=
{ one_smul := λ x, unop_injective $ one_smul R (unop x),
  mul_smul := λ r₁ r₂ x, unop_injective $ mul_smul r₁ r₂ (unop x),
  ..opposite.has_scalar α R  }

instance (R : Type*) [monoid R] [add_monoid α] [distrib_mul_action R α] :
  distrib_mul_action R (opposite α) :=
{ smul_add := λ r x₁ x₂, unop_injective $ smul_add r (unop x₁) (unop x₂),
  smul_zero := λ r, unop_injective $ smul_zero r,
  ..opposite.mul_action α R }

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

@[simp] lemma op_sub [add_group α] (x y : α) : op (x - y) = op x - op y := rfl
@[simp] lemma unop_sub [add_group α] (x y : αᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[simp] lemma op_smul {R : Type*} [has_scalar R α] (c : R) (a : α) : op (c • a) = c • op a := rfl
@[simp] lemma unop_smul {R : Type*} [has_scalar R α] (c : R) (a : αᵒᵖ) :
  unop (c • a) = c • unop a := rfl

lemma semiconj_by.op [has_mul α] {a x y : α} (h : semiconj_by a x y) :
  semiconj_by (op a) (op y) (op x) :=
begin
  dunfold semiconj_by,
  rw [← op_mul, ← op_mul, h.eq]
end

lemma semiconj_by.unop [has_mul α] {a x y : αᵒᵖ} (h : semiconj_by a x y) :
  semiconj_by (unop a) (unop y) (unop x) :=
begin
  dunfold semiconj_by,
  rw [← unop_mul, ← unop_mul, h.eq]
end

@[simp] lemma semiconj_by_op [has_mul α] {a x y : α} :
  semiconj_by (op a) (op y) (op x) ↔ semiconj_by a x y :=
begin
  split,
  { intro h,
    rw [← unop_op a, ← unop_op x, ← unop_op y],
    exact semiconj_by.unop h },
  { intro h,
    exact semiconj_by.op h }
end

@[simp] lemma semiconj_by_unop [has_mul α] {a x y : αᵒᵖ} :
  semiconj_by (unop a) (unop y) (unop x) ↔ semiconj_by a x y :=
by conv_rhs { rw [← op_unop a, ← op_unop x, ← op_unop y, semiconj_by_op] }

lemma commute.op [has_mul α] {x y : α} (h : commute x y) : commute (op x) (op y) :=
begin
  dunfold commute at h ⊢,
  exact semiconj_by.op h
end

lemma commute.unop [has_mul α] {x y : αᵒᵖ} (h : commute x y) : commute (unop x) (unop y) :=
begin
  dunfold commute at h ⊢,
  exact semiconj_by.unop h
end

@[simp] lemma commute_op [has_mul α] {x y : α} :
  commute (op x) (op y) ↔ commute x y :=
begin
  dunfold commute,
  rw semiconj_by_op
end

@[simp] lemma commute_unop [has_mul α] {x y : αᵒᵖ} :
  commute (unop x) (unop y) ↔ commute x y :=
begin
  dunfold commute,
  rw semiconj_by_unop
end

/-- The function `op` is an additive equivalence. -/
def op_add_equiv [has_add α] : α ≃+ αᵒᵖ :=
{ map_add' := λ a b, rfl, .. equiv_to_opposite }

@[simp] lemma coe_op_add_equiv [has_add α] : (op_add_equiv : α → αᵒᵖ) = op := rfl
@[simp] lemma coe_op_add_equiv_symm [has_add α] :
  (op_add_equiv.symm : αᵒᵖ → α) = unop := rfl

@[simp] lemma op_add_equiv_to_equiv [has_add α] :
  (op_add_equiv : α ≃+ αᵒᵖ).to_equiv = equiv_to_opposite :=
rfl

end opposite

open opposite

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵒᵖ`. -/
def ring_hom.to_opposite {R S : Type*} [semiring R] [semiring S] (f : R →+* S)
  (hf : ∀ x y, commute (f x) (f y)) : R →+* Sᵒᵖ :=
{ map_one' := congr_arg op f.map_one,
  map_mul' := λ x y, by simp [(hf x y).eq],
  .. (opposite.op_add_equiv : S ≃+ Sᵒᵖ).to_add_monoid_hom.comp ↑f }

@[simp] lemma ring_hom.coe_to_opposite {R S : Type*} [semiring R] [semiring S] (f : R →+* S)
  (hf : ∀ x y, commute (f x) (f y)) : ⇑(f.to_opposite hf) = op ∘ f := rfl
