/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.majorize
import analysis.convex.jensen

/-!
# Karamata's inequality
-/

variables {ι α β : Type*} [fintype ι] [linear_ordered_add_comm_group α] [preorder β]

def schur_convex (f : (ι → α) → β) : Prop := ∀ ⦃a b⦄, a ≺ᵐ b → f a ≤ f b

def schur_concave (f : (ι → α) → β) : Prop := ∀ ⦃a b⦄, a ≺ᵐ b → f b ≤ f a
