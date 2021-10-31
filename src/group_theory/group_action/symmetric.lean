/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
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

class is_symmetric_smul (R M : Type*) [has_scalar R M] [has_scalar (opposite R) M] :=
(op_smul_eq_smul : ∀ (r : R) (m : M), m <• r = r • m)

open is_symmetric_smul (op_smul_eq_smul)

instance comm_semigroup.is_symmetric_smul {R} [comm_semigroup R] : is_symmetric_smul R R :=
⟨λ r m, mul_comm _ _⟩

instance prod.is_symmetric_smul {R α β}
  [has_scalar R α] [has_scalar R β] [has_scalar Rᵒᵖ α] [has_scalar Rᵒᵖ β]
  [is_symmetric_smul R α] [is_symmetric_smul R β] : is_symmetric_smul R (α × β) :=
⟨λ r m, prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩
