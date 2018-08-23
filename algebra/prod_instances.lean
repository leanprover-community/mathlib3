/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Prod instances for algebraic structures.
-/

import algebra.module

namespace prod
universes u v w
variables {α : Type u} {β : Type v}
variables (x y : α × β) (a a₁ a₂: α) (b b₁ b₂ : β)

instance has_zero [has_zero α] [has_zero β] : has_zero (α × β) := ⟨(0, 0)⟩
lemma zero_def [has_zero α] [has_zero β] : (0 : α × β) = (0, 0) := rfl

instance has_one [has_one α] [has_one β] : has_one (α × β) := ⟨(1, 1)⟩
lemma one_def [has_one α] [has_one β] : (1 : α × β) = (1, 1) := rfl

instance has_add [has_add α] [has_add β] : has_add (α × β) := ⟨λ x y, (x.1 + y.1, x.2 + y.2)⟩
lemma add_def [has_add α] [has_add β] : (x + y) = (x.1 + y.1, x.2 + y.2) := rfl
@[simp] lemma add_def' [has_add α] [has_add β] : (a₁, b₁) + (a₂, b₂) = (a₁ + a₂, b₁ + b₂) := rfl

instance has_mul [has_mul α] [has_mul β] : has_mul (α × β) := ⟨λ x y, (x.1 * y.1, x.2 * y.2)⟩
lemma mul_def [has_mul α] [has_mul β] : (x * y) = (x.1 * y.1, x.2 * y.2) := rfl
@[simp] lemma mul_def' [has_mul α] [has_mul β] : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

instance has_inv [has_inv α] [has_inv β] : has_inv (α × β) := ⟨λ x, (x.1⁻¹, x.2⁻¹)⟩
lemma inv_def [has_inv α] [has_inv β] : x⁻¹ = (x.1⁻¹, x.2⁻¹) := rfl
@[simp] lemma inv_def' [has_inv α] [has_inv β] : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

instance has_neg [has_neg α] [has_neg β] : has_neg (α × β) := ⟨λ x, (-x.1, -x.2)⟩
lemma neg_def [has_neg α] [has_neg β] : -x = (-x.1, -x.2) := rfl
@[simp] lemma neg_def' [has_neg α] [has_neg β] : -(a, b) = (-a, -b) := rfl

instance has_scalar {γ : Type w} [has_scalar γ α] [has_scalar γ β] : has_scalar γ (α × β) := ⟨λ s x, (s • x.1, s • x.2)⟩
lemma smul_def {γ : Type w} [has_scalar γ α] [has_scalar γ β] (s : γ) : s • x = (s • x.1, s • x.2) := rfl
@[simp] lemma smul_def' {γ : Type w} [has_scalar γ α] [has_scalar γ β] (s : γ) : s • (a, b) = (s • a, s • b) := rfl

instance semigroup [semigroup α] [semigroup β] : semigroup (α × β) :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..prod.has_mul }

instance comm_semigroup [comm_semigroup α] [comm_semigroup β] : comm_semigroup (α × β) :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..prod.semigroup }

instance monoid [monoid α] [monoid β] : monoid (α × β) :=
{ mul := (*),
  mul_one := by simp [one_def, mul_def],
  one_mul := by simp [one_def, mul_def],
  ..prod.semigroup,
  ..prod.has_one }

instance comm_monoid [comm_monoid α] [comm_monoid β] : comm_monoid (α × β) :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..prod.monoid }

instance group [group α] [group β] : group (α × β) :=
{ mul := (*),
  mul_left_inv := by simp [inv_def, one_def],
  ..prod.monoid,
  ..prod.has_inv }

instance comm_group [comm_group α] [comm_group β] : comm_group (α × β) :=
{ ..prod.comm_monoid,
  ..prod.group }

instance add_semigroup [add_semigroup α] [add_semigroup β] : add_semigroup (α × β) :=
{ add_assoc := by simp [add_def],
  ..prod.has_add }

instance add_comm_semigroup [add_comm_semigroup α] [add_comm_semigroup β] : add_comm_semigroup (α × β) :=
{ add_comm := by simp [add_def],
  ..prod.add_semigroup }

instance add_monoid [add_monoid α] [add_monoid β] : add_monoid (α × β) :=
{ add := (+),
  add_zero := by simp [zero_def, add_def],
  zero_add := by simp [zero_def, add_def],
  ..prod.add_semigroup,
  ..prod.has_zero }

instance add_comm_monoid [add_comm_monoid α] [add_comm_monoid β] : add_comm_monoid (α × β) :=
{ add_comm := by simp [add_def, add_comm],
  ..prod.add_monoid }

instance add_group [add_group α] [add_group β] : add_group (α × β) :=
{ add := (+),
  add_left_neg := by simp [neg_def, zero_def],
  ..prod.add_monoid,
  ..prod.has_neg }

instance add_comm_group [add_comm_group α] [add_comm_group β] : add_comm_group (α × β) :=
{ ..prod.add_comm_monoid,
  ..prod.add_group }

instance ring [ring α] [ring β] : ring (α × β) :=
{ mul := (*),
  add := (+),
  left_distrib := by simp [left_distrib, mul_def, add_def],
  right_distrib := by simp [right_distrib, mul_def, add_def],
  ..prod.add_comm_group,
  ..prod.monoid }

instance comm_ring [comm_ring α] [comm_ring β] : comm_ring (α × β) :=
{ ..prod.ring,
  ..prod.comm_monoid }

instance module {γ : Type w} [ring γ] [module γ α] [module γ β] : module γ (α × β) :=
{ add := (+),
  smul := (•),
  smul_add := by simp [smul_add, add_def, smul_def],
  add_smul := by simp [add_smul, add_def, smul_def],
  mul_smul := by simp [mul_smul, smul_def, mul_def],
  one_smul := by simp [smul_def, one_def],
  ..prod.add_comm_group }

instance vector_space {γ : Type w} [field γ] [vector_space γ α] [vector_space γ β] :
  vector_space γ (α × β) :=
{ ..prod.module }

instance left_cancel_semigroup [left_cancel_semigroup α] [left_cancel_semigroup β] : left_cancel_semigroup (α × β) :=
{ mul_left_cancel := λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h, prod.ext (mul_left_cancel (prod.mk.inj h).1)
                                                      (mul_left_cancel (prod.mk.inj h).2),
  ..prod.semigroup }

instance add_left_cancel_semigroup [add_left_cancel_semigroup α] [add_left_cancel_semigroup β] :
  add_left_cancel_semigroup (α × β) :=
{ add_left_cancel := λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h, prod.ext (add_left_cancel (prod.mk.inj h).1)
                                                      (add_left_cancel (prod.mk.inj h).2),
  ..prod.add_semigroup }

instance right_cancel_semigroup [right_cancel_semigroup α] [right_cancel_semigroup β] :
  right_cancel_semigroup (α × β) :=
{ mul_right_cancel := λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h, prod.ext (mul_right_cancel (prod.mk.inj h).1)
                                                       (mul_right_cancel (prod.mk.inj h).2),
  ..prod.semigroup }

instance add_right_cancel_semigroup [add_right_cancel_semigroup α] [add_right_cancel_semigroup β] :
  add_right_cancel_semigroup (α × β) :=
{ add_right_cancel := λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h, prod.ext (add_right_cancel (prod.mk.inj h).1)
                                                       (add_right_cancel (prod.mk.inj h).2),
  ..prod.add_semigroup }

end prod
