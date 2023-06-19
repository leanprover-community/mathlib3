/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.exponential

/-! # The exponential map from selfadjoint to unitary

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
In this file, we establish various propreties related to the map `λ a, exp ℂ A (I • a)` between the
subtypes `self_adjoint A` and `unitary A`.

## TODO

* Show that any exponential unitary is path-connected in `unitary A` to `1 : unitary A`.
* Prove any unitary whose distance to `1 : unitary A` is less than `1` can be expressed as an
  exponential unitary.
* A unitary is in the path component of `1` if and only if it is a finite product of exponential
  unitaries.
-/

section star

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [has_continuous_star A] [complete_space A]
[star_module ℂ A]

open complex

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
noncomputable def self_adjoint.exp_unitary (a : self_adjoint A) : unitary A :=
⟨exp ℂ (I • a), exp_mem_unitary_of_mem_skew_adjoint _ (a.prop.smul_mem_skew_adjoint conj_I)⟩

open self_adjoint

lemma commute.exp_unitary_add {a b : self_adjoint A} (h : commute (a : A) (b : A)) :
  exp_unitary (a + b) = exp_unitary a * exp_unitary b :=
begin
  ext,
  have hcomm : commute (I • (a : A)) (I • (b : A)),
  calc _ = _ : by simp only [h.eq, algebra.smul_mul_assoc, algebra.mul_smul_comm],
  simpa only [exp_unitary_coe, add_subgroup.coe_add, smul_add] using exp_add_of_commute hcomm,
end

lemma commute.exp_unitary {a b : self_adjoint A} (h : commute (a : A) (b : A)) :
  commute (exp_unitary a) (exp_unitary b) :=
calc (exp_unitary a) * (exp_unitary b) = (exp_unitary b) * (exp_unitary a)
  : by rw [←h.exp_unitary_add, ←h.symm.exp_unitary_add, add_comm]

end star
