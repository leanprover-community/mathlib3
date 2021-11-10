/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Eric Wieser
-/
import algebra.opposites
import group_theory.group_action.defs
import group_theory.group_action.prod

/-!
# Symmetric group actions

This file defines a class of group actions which are invariant unter taking the `opposite` of
the (semi)group.

-/

open opposite

class is_symmetric_smul (R M : Type*) [has_scalar R M] [has_scalar Rᵒᵖ M] :=
(op_smul_eq_smul : ∀ (r : R) (m : M), m <• r = r • m)

open is_symmetric_smul (op_smul_eq_smul)

lemma unop_smul_eq_smul {R M : Type*} [has_scalar R M] [has_scalar Rᵒᵖ M]
  [is_symmetric_smul R M] (r : Rᵒᵖ) (m : M) : unop r • m = r • m :=
by { conv_rhs { rw[←op_unop r] }, rw [op_smul_eq_smul] }

instance comm_semigroup.is_symmetric_smul {R} [comm_semigroup R] : is_symmetric_smul R R :=
⟨λ r m, mul_comm _ _⟩

instance prod.is_symmetric_smul {R α β}
  [has_scalar R α] [has_scalar R β] [has_scalar Rᵒᵖ α] [has_scalar Rᵒᵖ β]
  [is_symmetric_smul R α] [is_symmetric_smul R β] : is_symmetric_smul R (α × β) :=
⟨λ r m, prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩

instance (R M) [has_scalar R M] [has_scalar Rᵒᵖ M] [is_symmetric_smul R M] :
  is_symmetric_smul R Mᵒᵖ := ⟨λ r m, unop_injective (op_smul_eq_smul r m.unop : _)⟩

lemma op_smul_eq_op_smul_op (R M) [has_scalar R M] [has_scalar Rᵒᵖ M] [is_symmetric_smul R M]
  (r : R) (m : M) : op (r • m) = op r • op m :=
(op_smul_eq_smul r (op m)).symm

instance is_scalar_tower.is_symmetric_smul {R α} [monoid R] [mul_action R α] [has_scalar Rᵒᵖ α]
  [is_scalar_tower Rᵒᵖ R α] : is_symmetric_smul R α :=
⟨λ r a, by rw [←one_smul R a, ←smul_assoc, one_smul, op_smul_eq_mul, one_mul]⟩

instance mul_action.of_is_symmetric_smul {R α} [comm_monoid R] [mul_action R α] [has_scalar Rᵒᵖ α]
  [is_symmetric_smul R α] : mul_action Rᵒᵖ α :=
⟨λ a, by rw [←op_one, op_smul_eq_smul (1 : R) a, one_smul],
 λ r s a, by rw [mul_comm, ←op_unop (s * r), op_smul_eq_smul, unop_mul, mul_smul,
                 unop_smul_eq_smul, unop_smul_eq_smul]⟩
