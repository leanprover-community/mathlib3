/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Eric Wieser
-/
import algebra.opposites
import group_theory.group_action.defs
import group_theory.group_action.prod
import algebra.direct_sum.basic

/-!
# Symmetric group actions

This file defines instance of group actions which are invariant unter taking the `opposite` of
the operating type/(semi)group/monoid.

It uses `is_central_scalar` which states that for a
pair of types `R` and `M`, the actions of `R` and its opposite `Rᵐᵒᵖ` on `M` coincide.

We provide the alternate version of its constructor, `unop_smul_eq_smul` about general
instance of `Rᵐᵒᵖ` and several instances for closure properties.

## Tags

group action
-/
--open opposite

universe u

open mul_opposite

instance punit.is_central_scalar {R} [has_scalar R punit.{u+1}] [has_scalar Rᵐᵒᵖ punit.{u+1}] :
  is_central_scalar R punit.{u+1} := ⟨λ _ _, by simp⟩

section direct_sum
open_locale direct_sum
open dfinsupp mul_opposite is_central_scalar

variables {R : Type*} [semiring R]
  {ι : Type*} [decidable_eq ι] {β : ι → Type*}
  [Π (i : ι), add_comm_monoid (β i)]
  [Π (i : ι), distrib_mul_action R (β i)] [Π (i : ι), distrib_mul_action Rᵐᵒᵖ (β i)]
  [Π (i : ι), is_central_scalar R (β i)]

end direct_sum

instance units_mul_opposite.has_scalar
  {R M} [monoid R][has_scalar Rᵐᵒᵖ M] : has_scalar (units R)ᵐᵒᵖ M :=
⟨λ ur m, m <• (unop ur).val⟩

instance units.is_central_scalar {R M} [monoid R] [has_scalar R M] [has_scalar Rᵐᵒᵖ M]
  [is_central_scalar R M] : is_central_scalar (units R) M :=
⟨λ ur m, by { change m <• ur.val = ur.val • _, apply op_smul_eq_smul }⟩

lemma op_smul_eq_op_smul_op (R M) [has_scalar R M] [has_scalar Rᵐᵒᵖ M] [is_central_scalar R M]
  (r : R) (m : M) : op (r • m) = op r • op m :=
(op_smul_eq_smul r (op m)).symm

instance is_scalar_tower.is_central_scalar {R α} [monoid R] [mul_action R α] [has_scalar Rᵐᵒᵖ α]
  [is_scalar_tower Rᵐᵒᵖ R α] : is_central_scalar R α :=
⟨λ r a, by rw [←one_smul R a, ←smul_assoc, one_smul, op_smul_eq_mul, one_mul]⟩

instance mul_action.of_is_central_scalar {R α} [comm_monoid R] [mul_action R α] [has_scalar Rᵐᵒᵖ α]
  [is_central_scalar R α] : mul_action Rᵐᵒᵖ α :=
⟨λ a, by rw [←op_one, op_smul_eq_smul (1 : R) a, one_smul],
 λ r s a, by rw [mul_comm, ←op_unop (s * r), op_smul_eq_smul, unop_mul, mul_smul,
                 unop_smul_eq_smul, unop_smul_eq_smul]⟩

-- TODO there might be a more general version of this
instance smul_comm_class.of_is_central_scalar {R α} [has_scalar R α] [has_scalar Rᵐᵒᵖ α]
  [is_central_scalar R α] [smul_comm_class R R α] : smul_comm_class Rᵐᵒᵖ R α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r' (r • a), ←unop_smul_eq_smul r' a, smul_comm]⟩

instance smul_comm_class.of_is_central_scalar' {R α} [has_scalar R α] [has_scalar Rᵐᵒᵖ α]
  [is_central_scalar R α] [smul_comm_class R R α] : smul_comm_class R Rᵐᵒᵖ α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r (r' • a), ←unop_smul_eq_smul r a, smul_comm]⟩

/-- These are definitions (not instances) in order to easily make (local) instances of symmetric
actions where the right action is derived from the left action. -/

def op_scalar_of_scalar (R α) [has_scalar R α] : has_scalar Rᵐᵒᵖ α := ⟨λ r' a, unop r' • a⟩

def is_central_op_scalar_of_scalar (R α) [has_scalar R α] :
  @is_central_scalar R α _ (op_scalar_of_scalar R α) :=
{ op_smul_eq_smul := λ r a, rfl }
