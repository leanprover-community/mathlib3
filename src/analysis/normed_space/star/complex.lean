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

-/

variables {𝕜 : Type*} {E : Type*} {F : Type*} [is_R_or_C 𝕜]

namespace star_ring
open_locale complex_conjugate
open complex

variables [semi_normed_ring E] [star_add_monoid E] [module ℂ E] [star_module ℂ E]

/-- The real part of an element of star algebra. -/
@[simps] noncomputable def re (x : E) : self_adjoint E :=
⟨(2⁻¹ : ℂ) • (x + star x), by simp only [self_adjoint.mem_iff, star_smul, add_comm,
                                        star_add_monoid.star_add, star_inv', star_bit0,
                                        star_one, star_star]⟩

/-- The imaginary part of an element of star algebra. -/
@[simps] noncomputable def im (x : E) : self_adjoint E :=
⟨(-I * 2⁻¹ : ℂ) • (x - star x),
  begin
    have : x - star x = -(star x - x) := by simp,
    simp only [self_adjoint.mem_iff, neg_mul_eq_neg_mul_symm, neg_smul, star_neg, star_smul,
              map_mul, map_one, star_sub, star_star, neg_neg, complex.star_def, conj_I,
              complex.conj_inv, map_bit0],
    rw [←neg_smul, this, neg_smul_neg],
  end⟩

/-- An element of a complex star module can be decomposed into self-adjoint "real" and "imaginary"
parts -/
lemma eq_re_add_im (x : E) : x = re x + (I : ℂ) • im x :=
begin
  simp only [smul_smul, ←mul_assoc, re_coe, smul_add, im_coe, neg_mul_eq_neg_mul_symm,
            neg_smul, smul_neg, I_mul_I, one_mul, neg_neg, smul_sub, ←add_smul, add_add_sub_cancel],
  field_simp
end

end star_ring
