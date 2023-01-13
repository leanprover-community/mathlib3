/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import algebra.ring.defs
import algebra.group.order_synonym

/-!
# Ring structure on the order type synonyms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Transfer algebraic instances from `α` to `αᵒᵈ` and `lex α`.
-/

variables {α : Type*}

/-! ### Order dual -/

instance [h : distrib α] : distrib αᵒᵈ := h
instance [has_mul α] [has_add α] [h : left_distrib_class α] : left_distrib_class αᵒᵈ := h
instance [has_mul α] [has_add α] [h : right_distrib_class α] : right_distrib_class αᵒᵈ := h
instance [h : non_unital_non_assoc_semiring α] : non_unital_non_assoc_semiring αᵒᵈ := h
instance [h : non_unital_semiring α] : non_unital_semiring αᵒᵈ := h
instance [h : non_assoc_semiring α] : non_assoc_semiring αᵒᵈ := h
instance [h : semiring α] : semiring αᵒᵈ := h
instance [h : non_unital_comm_semiring α] : non_unital_comm_semiring αᵒᵈ := h
instance [h : comm_semiring α] : comm_semiring αᵒᵈ := h
instance [has_mul α] [h : has_distrib_neg α] : has_distrib_neg αᵒᵈ := h
instance [h : non_unital_non_assoc_ring α] : non_unital_non_assoc_ring αᵒᵈ := h
instance [h : non_unital_ring α] : non_unital_ring αᵒᵈ := h
instance [h : non_assoc_ring α] : non_assoc_ring αᵒᵈ := h
instance [h : ring α] : ring αᵒᵈ := h
instance [h : non_unital_comm_ring α] : non_unital_comm_ring αᵒᵈ := h
instance [h : comm_ring α] : comm_ring αᵒᵈ := h
instance [ring α] [h : is_domain α] : is_domain αᵒᵈ := h

/-! ### Lexicographical order -/

instance [h : distrib α] : distrib (lex α) := h
instance [has_mul α] [has_add α] [h : left_distrib_class α] : left_distrib_class (lex α) := h
instance [has_mul α] [has_add α] [h : right_distrib_class α] : right_distrib_class (lex α) := h
instance [h : non_unital_non_assoc_semiring α] : non_unital_non_assoc_semiring (lex α) := h
instance [h : non_unital_semiring α] : non_unital_semiring (lex α) := h
instance [h : non_assoc_semiring α] : non_assoc_semiring (lex α) := h
instance [h : semiring α] : semiring (lex α) := h
instance [h : non_unital_comm_semiring α] : non_unital_comm_semiring (lex α) := h
instance [h : comm_semiring α] : comm_semiring (lex α) := h
instance [has_mul α] [h : has_distrib_neg α] : has_distrib_neg (lex α) := h
instance [h : non_unital_non_assoc_ring α] : non_unital_non_assoc_ring (lex α) := h
instance [h : non_unital_ring α] : non_unital_ring (lex α) := h
instance [h : non_assoc_ring α] : non_assoc_ring (lex α) := h
instance [h : ring α] : ring (lex α) := h
instance [h : non_unital_comm_ring α] : non_unital_comm_ring (lex α) := h
instance [h : comm_ring α] : comm_ring (lex α) := h
instance [ring α] [h : is_domain α] : is_domain (lex α) := h
