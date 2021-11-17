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
pair of types `R` and `M`, the actions of `R` and its opposite `Rᵒᵖ` on `M` coincide.

We then provide the alternate version of its constructor, `unop_smul_eq_smul` about general
instance of `Rᵒᵖ` and several instances for closure properties.

## Tags

group action
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

section direct_sum
open_locale direct_sum
open dfinsupp opposite is_symmetric_smul

variables {R : Type*} [ring R]
  {ι : Type*} [decidable_eq ι] {β : ι → Type*}
  [Π (i : ι), add_comm_monoid (β i)]
  [Π (i : ι), distrib_mul_action R (β i)] [Π (i : ι), distrib_mul_action Rᵒᵖ (β i)]
  [Π (i : ι), is_symmetric_smul R (β i)]

--TODO why doesn't this exist yet?
instance : has_scalar R (direct_sum ι β) := dfinsupp.has_scalar
instance direct_sum.has_rscalar : has_scalar Rᵒᵖ (direct_sum ι β) := dfinsupp.has_scalar

instance dfinsupp.is_symmetric_smul :
  is_symmetric_smul R (direct_sum ι β) :=
⟨λ r m, by { induction m using direct_sum.induction_on with ι b x y ihx ihy,
  { ext, simp only [coe_zero, coe_smul, smul_zero] },
  { ext, simp only [coe_smul, pi.smul_apply, op_smul_eq_smul] },
  { ext, simp only [smul_add, pi.add_apply, coe_smul,
     pi.smul_apply, coe_add, ihx, ihy, op_smul_eq_smul] } } ⟩

end direct_sum

instance (R M) [has_scalar R M] [has_scalar Rᵒᵖ M] [is_symmetric_smul R M] :
  is_symmetric_smul R Mᵒᵖ := ⟨λ r m, unop_injective (op_smul_eq_smul r m.unop : _)⟩

lemma op_smul_eq_op_smul_op (R M) [has_scalar R M] [has_scalar Rᵒᵖ M] [is_symmetric_smul R M]
  (r : R) (m : M) : op (r • m) = op r • op m :=
(op_smul_eq_smul r (op m)).symm

instance is_scalar_tower.is_symmetric_smul {R α} [monoid R] [mul_action R α] [has_scalar Rᵒᵖ α]
  [is_scalar_tower Rᵒᵖ R α] : is_symmetric_smul R α :=
⟨λ r a, by rw [←one_smul R a, ←smul_assoc, one_smul, op_smul_eq_mul, one_mul]⟩

--This causes loops :(
/-instance is_symmetric_smul.is_scalar_tower {R α} [comm_monoid R] [mul_action R α] [has_scalar Rᵒᵖ α]
  [is_symmetric_smul R α] : is_scalar_tower Rᵒᵖ R α :=
⟨λ r' r a, by { rw [←unop_smul_eq_smul r' (r • a), smul_smul],
                change (_ * _) • _ = _, rw [mul_comm] } ⟩-/

instance mul_action.of_is_symmetric_smul {R α} [comm_monoid R] [mul_action R α] [has_scalar Rᵒᵖ α]
  [is_symmetric_smul R α] : mul_action Rᵒᵖ α :=
⟨λ a, by rw [←op_one, op_smul_eq_smul (1 : R) a, one_smul],
 λ r s a, by rw [mul_comm, ←op_unop (s * r), op_smul_eq_smul, unop_mul, mul_smul,
                 unop_smul_eq_smul, unop_smul_eq_smul]⟩

-- TODO there might be a more general version of this
instance smul_comm_class.of_is_symmetric_smul {R α} [has_scalar R α] [has_scalar Rᵒᵖ α]
  [is_symmetric_smul R α] [smul_comm_class R R α] : smul_comm_class Rᵒᵖ R α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r' (r • a), ←unop_smul_eq_smul r' a, smul_comm]⟩

instance smul_comm_class.of_is_symmetric_smul' {R α} [has_scalar R α] [has_scalar Rᵒᵖ α]
  [is_symmetric_smul R α] [smul_comm_class R R α] : smul_comm_class R Rᵒᵖ α :=
⟨λ r' r a, by rw [←unop_smul_eq_smul r (r' • a), ←unop_smul_eq_smul r a, smul_comm]⟩
