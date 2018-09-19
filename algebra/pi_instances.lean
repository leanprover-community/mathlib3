/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

Pi instances for algebraic structures.
-/

import algebra.module order.basic tactic.pi_instances

namespace pi
universes u v
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equiped with instances
variables (x y : Π i, f i) (i : I)

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) := ⟨λ i, 0⟩
@[simp] lemma zero_apply [∀ i, has_zero $ f i] : (0 : Π i, f i) i = 0 := rfl

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ i, 1⟩
@[simp] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) := ⟨λ x y, λ i, x i + y i⟩
@[simp] lemma add_apply [∀ i, has_add $ f i] : (x + y) i = x i + y i := rfl

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ x y, λ i, x i * y i⟩
@[simp] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ x, λ i, (x i)⁻¹⟩
@[simp] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) := ⟨λ x, λ i, -(x i)⟩
@[simp] lemma neg_apply [∀ i, has_neg $ f i] : (-x) i = -x i := rfl

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) := ⟨λ s x, λ i, s • (x i)⟩
@[simp] lemma smul_apply {α : Type*} [∀ i, has_scalar α $ f i] (s : α) : (s • x) i = s • x i := rfl

instance semigroup          [∀ i, semigroup          $ f i] : semigroup          (Π i : I, f i) := by pi_instance
instance comm_semigroup     [∀ i, comm_semigroup     $ f i] : comm_semigroup     (Π i : I, f i) := by pi_instance
instance monoid             [∀ i, monoid             $ f i] : monoid             (Π i : I, f i) := by pi_instance
instance comm_monoid        [∀ i, comm_monoid        $ f i] : comm_monoid        (Π i : I, f i) := by pi_instance
instance group              [∀ i, group              $ f i] : group              (Π i : I, f i) := by pi_instance
instance comm_group         [∀ i, comm_group         $ f i] : comm_group         (Π i : I, f i) := by pi_instance
instance add_semigroup      [∀ i, add_semigroup      $ f i] : add_semigroup      (Π i : I, f i) := by pi_instance
instance add_comm_semigroup [∀ i, add_comm_semigroup $ f i] : add_comm_semigroup (Π i : I, f i) := by pi_instance
instance add_monoid         [∀ i, add_monoid         $ f i] : add_monoid         (Π i : I, f i) := by pi_instance
instance add_comm_monoid    [∀ i, add_comm_monoid    $ f i] : add_comm_monoid    (Π i : I, f i) := by pi_instance
instance add_group          [∀ i, add_group          $ f i] : add_group          (Π i : I, f i) := by pi_instance
instance add_comm_group     [∀ i, add_comm_group     $ f i] : add_comm_group     (Π i : I, f i) := by pi_instance
instance ring               [∀ i, ring               $ f i] : ring               (Π i : I, f i) := by pi_instance
instance comm_ring          [∀ i, comm_ring          $ f i] : comm_ring          (Π i : I, f i) := by pi_instance
instance module {α} {r : ring α} [∀ i, module α $ f i] : module α        (Π i : I, f i) := by pi_instance

instance vector_space (α) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..pi.module }

instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] : left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_left_cancel_semigroup [∀ i, add_left_cancel_semigroup $ f i] : add_left_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] : right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance add_right_cancel_semigroup [∀ i, add_right_cancel_semigroup $ f i] : add_right_cancel_semigroup (Π i : I, f i) :=
by pi_instance

instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] : ordered_cancel_comm_monoid (Π i : I, f i) :=
by pi_instance

end pi
