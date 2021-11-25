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

This file defines a class of group actions which are invariant unter taking the `opposite` of
the operating type/(semi)group/monoid.

The main definition is the one of the typeclass `is_symmetric_smul` which states that for a
pair of types `R` and `M`, the actions of `R` and its opposite `Rᵐᵒᵖ` on `M` coincide.

We then provide the alternate version of its constructor, `unop_smul_eq_smul` about general
instance of `Rᵐᵒᵖ` and several instances for closure properties.

## Tags

group action
-/
--open opposite

universe u

class is_symmetric_smul (R M : Type*) [has_scalar R M] [has_scalar Rᵐᵒᵖ M] :=
(op_smul_eq_smul : ∀ (r : R) (m : M), m <• r = r • m)

open mul_opposite is_symmetric_smul (op_smul_eq_smul)

lemma unop_smul_eq_smul {R M : Type*} [has_scalar R M] [has_scalar Rᵐᵒᵖ M]
  [is_symmetric_smul R M] (r : Rᵐᵒᵖ) (m : M) : (unop r) • m = r • m :=
by { conv_rhs { rw[←op_unop r] }, rw [op_smul_eq_smul] }

instance comm_semigroup.is_symmetric_smul {R} [comm_semigroup R] : is_symmetric_smul R R :=
⟨λ r m, mul_comm _ _⟩

instance punit.is_symmetric_smul {R} [has_scalar R punit.{u+1}] [has_scalar Rᵐᵒᵖ punit.{u+1}] :
  is_symmetric_smul R punit.{u+1} := ⟨λ _ _, by simp⟩

instance prod.is_symmetric_smul {R α β}
  [has_scalar R α] [has_scalar R β] [has_scalar Rᵐᵒᵖ α] [has_scalar Rᵐᵒᵖ β]
  [is_symmetric_smul R α] [is_symmetric_smul R β] : is_symmetric_smul R (α × β) :=
⟨λ r m, prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩

section direct_sum
open_locale direct_sum
open dfinsupp mul_opposite is_symmetric_smul

variables {R : Type*} [semiring R]
  {ι : Type*} [decidable_eq ι] {β : ι → Type*}
  [Π (i : ι), add_comm_monoid (β i)]
  [Π (i : ι), distrib_mul_action R (β i)] [Π (i : ι), distrib_mul_action Rᵐᵒᵖ (β i)]
  [Π (i : ι), is_symmetric_smul R (β i)]

--TODO why isn't this found
instance : has_scalar R (direct_sum ι β) := dfinsupp.has_scalar
instance direct_sum.has_rscalar : has_scalar Rᵐᵒᵖ (direct_sum ι β) := dfinsupp.has_scalar

instance dfinsupp.is_symmetric_smul :
  is_symmetric_smul R (direct_sum ι β) :=
⟨λ r m, by { induction m using direct_sum.induction_on with ι b x y ihx ihy,
  { ext, simp only [coe_zero, coe_smul, smul_zero] },
  { ext, simp only [coe_smul, pi.smul_apply, op_smul_eq_smul] },
  { ext, simp only [smul_add, pi.add_apply, coe_smul,
     pi.smul_apply, coe_add, ihx, ihy, op_smul_eq_smul] } } ⟩

end direct_sum


instance (R M) [has_scalar R M] [has_scalar Rᵐᵒᵖ M] [is_symmetric_smul R M] :
  is_symmetric_smul R Mᵐᵒᵖ := ⟨λ r m, unop_injective (op_smul_eq_smul r m.unop : _)⟩

lemma op_smul_eq_op_smul_op (R M) [has_scalar R M] [has_scalar Rᵐᵒᵖ M] [is_symmetric_smul R M]
  (r : R) (m : M) : op (r • m) = op r • op m :=
(op_smul_eq_smul r (op m)).symm

instance is_scalar_tower.is_symmetric_smul {R α} [monoid R] [mul_action R α] [has_scalar Rᵐᵒᵖ α]
  [is_scalar_tower Rᵐᵒᵖ R α] : is_symmetric_smul R α :=
⟨λ r a, by rw [←one_smul R a, ←smul_assoc, one_smul, op_smul_eq_mul, one_mul]⟩

instance mul_action.of_is_symmetric_smul {R α} [comm_monoid R] [mul_action R α] [has_scalar Rᵐᵒᵖ α]
  [is_symmetric_smul R α] : mul_action Rᵐᵒᵖ α :=
⟨λ a, by rw [←op_one, op_smul_eq_smul (1 : R) a, one_smul],
 λ r s a, by rw [mul_comm, ←op_unop (s * r), op_smul_eq_smul, unop_mul, mul_smul,
                 unop_smul_eq_smul, unop_smul_eq_smul]⟩

-- TODO there might be a more general version of this
instance smul_comm_class.of_is_symmetric_smul {R α} [has_scalar R α] [has_scalar Rᵐᵒᵖ α]
  [is_symmetric_smul R α] [smul_comm_class R R α] : smul_comm_class Rᵐᵒᵖ R α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r' (r • a), ←unop_smul_eq_smul r' a, smul_comm]⟩

instance smul_comm_class.of_is_symmetric_smul' {R α} [has_scalar R α] [has_scalar Rᵐᵒᵖ α]
  [is_symmetric_smul R α] [smul_comm_class R R α] : smul_comm_class R Rᵐᵒᵖ α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r (r' • a), ←unop_smul_eq_smul r a, smul_comm]⟩

/-- These are definitions (not instances) in order to easily make (local) instances of symmetric
actions where the right action is derived from the left action. -/

def op_scalar_of_scalar (R α) [has_scalar R α] : has_scalar Rᵐᵒᵖ α := ⟨λ r' a, unop r' • a⟩

def is_symmetric_op_scalar_of_scalar (R α) [has_scalar R α] :
  @is_symmetric_smul R α _ (op_scalar_of_scalar R α) :=
{ op_smul_eq_smul := λ r a, rfl }
