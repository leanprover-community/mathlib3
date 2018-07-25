/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

Pi instances for algebraic structures.
-/

import algebra.module order.basic

namespace tactic

open interactive interactive.types lean.parser
open functor has_seq list nat tactic.interactive

meta def derive_field : tactic unit :=
do b ← target >>= is_prop,
   if b then do
     field ← get_current_field,
     intros >> funext,
     applyc field
   else do
     field ← get_current_field,
     xs ← intros <* intro1,
     applyc field,
     xs.mmap' apply

/-- `pi_instance [inst1,inst2]` constructs an instance of `my_class (Π i : I, f i)`
    where we know `Π i, my_class (f i)` and where all non-propositional fields are
    filled in by `inst1` and `inst2`
 -/
meta def pi_instance : tactic unit :=
refine_struct ``( { .. } ) ; try derive_field

run_cmd add_interactive [`pi_instance]

end tactic

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

instance semigroup       [∀ i, semigroup       $ f i] : semigroup       (Π i : I, f i) := by pi_instance
instance comm_semigroup  [∀ i, comm_semigroup  $ f i] : comm_semigroup  (Π i : I, f i) := by pi_instance
instance monoid          [∀ i, monoid          $ f i] : monoid          (Π i : I, f i) := by pi_instance
instance comm_monoid     [∀ i, comm_monoid     $ f i] : comm_monoid     (Π i : I, f i) := by pi_instance
instance add_comm_monoid [∀ i, add_comm_monoid $ f i] : add_comm_monoid (Π i : I, f i) := by pi_instance
instance group           [∀ i, group           $ f i] : group           (Π i : I, f i) := by pi_instance
instance add_semigroup   [∀ i, add_semigroup   $ f i] : add_semigroup   (Π i : I, f i) := by pi_instance
instance add_group       [∀ i, add_group       $ f i] : add_group       (Π i : I, f i) := by pi_instance
instance add_comm_group  [∀ i, add_comm_group  $ f i] : add_comm_group  (Π i : I, f i) := by pi_instance
instance ring            [∀ i, ring            $ f i] : ring            (Π i : I, f i) := by pi_instance
instance comm_ring       [∀ i, comm_ring       $ f i] : comm_ring       (Π i : I, f i) := by pi_instance
instance module {α} [ring α] [∀ i, module α    $ f i] : module α        (Π i : I, f i) := by pi_instance

instance vector_space (α) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..pi.module }

instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] : left_cancel_semigroup (Π i : I, f i) :=
{ mul_left_cancel := λ a b c h, funext $ λ i, mul_left_cancel (congr_fun h i),
  ..pi.semigroup }

instance add_left_cancel_semigroup [∀ i, add_left_cancel_semigroup $ f i] : add_left_cancel_semigroup (Π i : I, f i) :=
{ add_left_cancel := λ a b c h, funext $ λ i, add_left_cancel (congr_fun h i),
  ..pi.add_semigroup }

instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] : right_cancel_semigroup (Π i : I, f i) :=
{ mul_right_cancel := λ a b c h, funext $ λ i, mul_right_cancel (congr_fun h i:_),
  ..pi.semigroup }

instance add_right_cancel_semigroup [∀ i, add_right_cancel_semigroup $ f i] : add_right_cancel_semigroup (Π i : I, f i) :=
{ add_right_cancel := λ a b c h, funext $ λ i, add_right_cancel (congr_fun h i:_),
  ..pi.add_semigroup }

instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] : ordered_cancel_comm_monoid (Π i : I, f i) :=
{ add_le_add_left := λ a b h c i, add_le_add_left' (h i),
  le_of_add_le_add_left := λ a b c h i, le_of_add_le_add_left (h i),
  ..pi.add_comm_monoid, ..pi.partial_order,
  ..pi.add_left_cancel_semigroup, ..pi.add_right_cancel_semigroup }

end pi
