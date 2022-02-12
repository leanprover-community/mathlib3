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

variables {E : Type*}

namespace star_module
open_locale complex_conjugate
open complex

variables [add_comm_group E] [star_add_monoid E] [module ℂ E] [star_module ℂ E]

/-- The imaginary part of an element of a star module, as a real-linear map. Note: the real part
is defined in `algebra/star/module`. -/
@[simps] noncomputable def im : E →ₗ[ℝ] self_adjoint E :=
{ to_fun := λ x, ⟨(-(I : ℂ) * ⅟ 2) • (x - star x),
    begin
      have h₁ : conj (⅟ 2 : ℂ) = ⅟ 2,
      { rw [←star_def, star_inv_of (2 : ℂ), inv_of_eq_inv, star_bit0, star_one, ←inv_of_eq_inv] },
      have h₂ : x - star x = -(star x - x) := by simp,
      simp only [self_adjoint.mem_iff, neg_mul, neg_smul, star_neg, star_smul, star_inv_of (2 : ℝ),
                 map_mul, map_one, star_sub, star_star, neg_neg, star_def, conj_I, map_bit0,
                 complex.conj_inv, h₁],
      rw [←neg_smul, h₂, neg_smul_neg],
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

/-- An element of a complex star module can be decomposed into self-adjoint "real" and
"imaginary" parts -/
lemma eq_re_add_im (x : E) : x = re ℝ x + I • im x :=
begin
  have h₁ : I * (-I * (2⁻¹ : ℂ)) = 2⁻¹,
  { simp_rw [←mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul], },
  have h₂ : (2⁻¹ : ℂ) = algebra_map ℝ ℂ (2⁻¹ : ℝ),
  { simp only [is_R_or_C.algebra_map_eq_of_real, of_real_inv, of_real_bit0, of_real_one] },
  simp_rw [re_apply_coe, im_apply_coe, inv_of_eq_inv, smul_smul, h₁, ←algebra_map_smul ℂ (2⁻¹ : ℝ),
           h₂, ←smul_add, algebra_map_smul, add_add_sub_cancel, inv_eq_one_div, smul_add, ←add_smul,
           add_halves', one_smul],
end

end star_module
