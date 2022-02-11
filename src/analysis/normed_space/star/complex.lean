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

* `star_module.re`: the real part of an element of a star module, defined as `⅟2 • (x + star x)`
* `star_module.im`: the imaginary part of an element of a star module, defined as
  `(-I * ⅟2) • (x - star x)`. The corresponding real part is defined in a more
  general setting in `algebra/star/module`.

-/

variables {𝕜 : Type*} {E : Type*}

namespace star_module
open_locale complex_conjugate
open is_R_or_C

variables [is_R_or_C 𝕜] [add_comm_group E] [star_add_monoid E] [module 𝕜 E] [star_module 𝕜 E]
  [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [star_module ℝ E]

variables (𝕜)
/-- The imaginary part of an element of a star module, as a real-linear map. -/
@[simps] noncomputable def im : E →ₗ[ℝ] self_adjoint E :=
{ to_fun := λ x, ⟨(-(I : 𝕜) * ⅟ 2) • (x - star x),
    begin
      have : x - star x = -(star x - x) := by simp,
      simp only [self_adjoint.mem_iff, neg_mul, neg_smul, star_neg, star_smul, star_inv_of (2 : ℝ),
                 map_mul, map_one, star_sub, star_star, neg_neg, star_def, conj_I, map_bit0,
                 complex.conj_inv],
      rw [←neg_smul, this, neg_smul_neg],
    end⟩,
  map_add' := λ x y, by { ext, simp [add_sub_comm], },
  map_smul' := λ r x,
    begin
      ext,
      simp only [neg_mul, neg_smul, star_smul, is_R_or_C.star_def,
                 is_R_or_C.conj_to_real, ring_hom.id_apply, subtype.val_eq_coe,
                 self_adjoint.coe_smul, add_subgroup.coe_mk, smul_neg, neg_inj, ←smul_sub,
                 smul_comm r],
    end }

/-- An element of a complex star module can be decomposed into self-adjoint "real" and "imaginary"
parts -/
lemma eq_re_add_im (x : E) : x = re ℝ x + (I : 𝕜) • im 𝕜 x :=
by simp only [smul_smul, ← mul_assoc, neg_smul, smul_neg, I_mul_I, one_mul, neg_neg, smul_sub,
  ← add_smul, add_add_sub_cancel, re_apply_coe, smul_add, im_apply_coe, neg_mul,
  inv_eq_one_div, add_halves', one_smul]

end star_module
