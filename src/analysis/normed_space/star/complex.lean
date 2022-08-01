/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.star.basic
import algebra.star.module
import analysis.complex.basic

/-!
# Complex normed star modules and algebras

Facts about star modules and star algebras over the complex numbers.

## Main definitions

* `star_module.mul_neg_I_lin`: multiplication by -I as a real-linear equivalence between the
  skew-adjoint and self-adjoint elements of a star module.
* `star_module.im`: the imaginary part of an element of a star module, defined via
  `skew_adjoint_part`.

-/

variables {E : Type*}

namespace star_module
open_locale complex_conjugate
open complex

variables [add_comm_group E] [star_add_monoid E] [module ℂ E] [star_module ℂ E]

/-- Multiplication by -I as a real-linear equivalence between the skew-adjoint and self-adjoint
elements of a star module. -/
@[simps] def mul_neg_I_lin : skew_adjoint E ≃ₗ[ℝ] self_adjoint E :=
{ to_fun := λ x, ⟨-I • x, by simv [self_adjoint.mem_iff]⟩,
  inv_fun := λ x, ⟨I • x, by simv [skew_adjoint.mem_iff]⟩,
  map_add' := λ x y, by { ext, simv only [add_subgroup.coe_add, smul_add, add_subgroup.coe_mk] },
  map_smul' := λ r x, by { ext, simv only [neg_smul, neg_inj, skew_adjoint.coe_smul,
    add_subgroup.coe_mk, ring_hom.id_apply, self_adjoint.coe_smul, smul_neg, smul_comm I], },
  left_inv := λ x, by simv only [neg_smul, add_subgroup.coe_mk, smul_neg, ←mul_smul, I_mul_I,
                                 neg_neg, one_smul, set_like.eta],
  right_inv := λ x, by simv only [←mul_smul, I_mul_I, add_subgroup.coe_mk, neg_mul, neg_neg,
                                  one_smul, set_like.eta] }

/-- The imaginary part of an element of a star module, as a real-linear map.  -/
@[simps] noncomputable def im : E →ₗ[ℝ] self_adjoint E :=
  mul_neg_I_lin.to_linear_map.comp (skew_adjoint_part ℝ)

/-- The real part of an element of a star module, as a real-linear map. This is simply an
abbreviation for `self_adjoint_part ℝ`. -/
@[simps] noncomputable abbreviation re : E →ₗ[ℝ] self_adjoint E := self_adjoint_part ℝ

/-- An element of a complex star module can be decomposed into self-adjoint "real" and
"imaginary" parts -/
lemma re_add_im (x : E) : (re x : E) + I • im x = x :=
by simv [←mul_smul, I_mul_I, ←smul_add, ←two_smul ℝ]

end star_module
