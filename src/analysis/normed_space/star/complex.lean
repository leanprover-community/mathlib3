/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.star.basic
import algebra.star.self_adjoint
import analysis.complex.basic

/-!
# Complex normed star modules and algebras

Facts about star modules and star algebras over the complex numbers.

## Main definitions

* `star_ring.re`: the real part of an element of a star ring, defined as `2⁻¹ • (x + star x)`
* `star_ring.im`: the imaginary part of an element of a star ring, defined as
  `(-I * 2⁻¹) • (x - star x)`.

-/

variables {E : Type*}

namespace star_ring
open_locale complex_conjugate
open complex

variables [semi_normed_ring E] [star_add_monoid E] [module ℂ E] [star_module ℂ E]

/-- The real part of an element of star algebra, as a real-linear map. -/
@[simps] noncomputable def re : E →ₗ[ℝ] self_adjoint E :=
{ to_fun := λ x, ⟨(2⁻¹ : ℂ) • (x + star x), by simp only [self_adjoint.mem_iff, star_smul, add_comm,
                                        star_add_monoid.star_add, star_inv', star_bit0,
                                        star_one, star_star]⟩,
  map_add' := λ x y, by { refine subtype.ext_val _, simp, abel },
  map_smul' := λ r x,
    begin
      refine subtype.ext_val _,
      simp only [star_smul, is_R_or_C.star_def, is_R_or_C.conj_to_real, smul_add, ring_hom.id_apply,
                 subtype.val_eq_coe, self_adjoint.coe_smul, add_subgroup.coe_mk],
      rw [smul_comm],
      refine congr_arg _ _,
      rw [smul_comm]
    end }

/-- The imaginary part of an element of star algebra, as a real-linear map. -/
@[simps] noncomputable def im : E →ₗ[ℝ] self_adjoint E :=
{ to_fun := λ x, ⟨(-I * 2⁻¹) • (x - star x),
    begin
      have : x - star x = -(star x - x) := by simp,
      simp only [self_adjoint.mem_iff, neg_mul_eq_neg_mul_symm, neg_smul, star_neg, star_smul,
                 map_mul, map_one, star_sub, star_star, neg_neg, star_def, conj_I, map_bit0,
                 complex.conj_inv],
      rw [←neg_smul, this, neg_smul_neg],
    end⟩,
  map_add' := λ x y,
    begin
      refine subtype.ext_val _,
      simp only [neg_mul_eq_neg_mul_symm, neg_smul, star_add_monoid.star_add, subtype.val_eq_coe,
                 add_subgroup.coe_add, add_subgroup.coe_mk],
      conv { to_rhs, rw [←neg_smul, ←neg_smul] },
      rw [←neg_smul, ←smul_add],
      refine congr_arg _ _,
      abel
    end,
  map_smul' := λ r x,
    begin
      refine subtype.ext_val _,
      simp only [neg_mul_eq_neg_mul_symm, neg_smul, star_smul, is_R_or_C.star_def,
                 is_R_or_C.conj_to_real, ring_hom.id_apply, subtype.val_eq_coe,
                 self_adjoint.coe_smul, add_subgroup.coe_mk, smul_neg, neg_inj, ←smul_sub],
      rw [smul_comm],
    end
}

/-- An element of a complex star module can be decomposed into self-adjoint "real" and "imaginary"
parts -/
lemma eq_re_add_im (x : E) : x = re x + I • im x :=
begin
  simp only [smul_smul, ←mul_assoc, neg_smul, smul_neg, I_mul_I, one_mul, neg_neg, smul_sub,
             ←add_smul, add_add_sub_cancel, re_apply_coe, smul_add, im_apply_coe,
            neg_mul_eq_neg_mul_symm],
  field_simp
end

end star_ring
