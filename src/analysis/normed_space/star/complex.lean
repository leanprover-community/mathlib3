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

variables [semi_normed_ring E] [star_add_monoid E]

section is_R_or_C
variables {𝕜 : Type*} [is_R_or_C 𝕜] [module ℝ E] [module 𝕜 E] [is_scalar_tower ℝ 𝕜 E]
  [star_module 𝕜 E]

include 𝕜
instance star_module.is_R_or_C_to_real : star_module ℝ E :=
⟨λ r a, by { have h₁ : r • a = (r : 𝕜) • a := sorry,
             have h₂ : (star r : 𝕜) • star a = star r • star a := sorry,
             simp only [h₁, star_smul, star_def, conj_of_real, h₂] }⟩
omit 𝕜

--instance star_module.scalar_tower {S : Type*} {R : Type*} {A : Type*} [comm_semiring S] [semiring R] [has_star S] [star_monoid R] [has_star A]
--  [algebra S R] [mul_action R A] [has_scalar S A] [is_scalar_tower S R A] [star_module S R]
--  [star_module R A] : star_module S A :=
--⟨λ s a, by { nth_rewrite_lhs 0 [show a = (1 : R) • a, from (one_smul _ _).symm],
--             rw [←smul_assoc, star_smul, star_smul, star_one, smul_assoc, one_smul] }⟩

--instance : module ℝ (self_adjoint E) :=

end is_R_or_C

section complex
variables [module ℂ E] [star_module ℂ E]

set_option trace.class_instances true
noncomputable example : module ℝ (self_adjoint E) := self_adjoint.module
set_option trace.class_instances false


/-- The real part of an element of star algebra. -/
@[simps] noncomputable def re (x : E) : self_adjoint E :=
⟨(2⁻¹ : ℂ) • (x + star x), by simp only [self_adjoint.mem_iff, star_smul, add_comm,
                                        star_add_monoid.star_add, star_inv', star_bit0,
                                        star_one, star_star]⟩

/-- The imaginary part of an element of star algebra. -/
@[simps] noncomputable def im (x : E) : self_adjoint E :=
⟨(-I * 2⁻¹) • (x - star x),
  begin
    have : x - star x = -(star x - x) := by simp,
    simp only [self_adjoint.mem_iff, neg_mul_eq_neg_mul_symm, neg_smul, star_neg, star_smul,
               map_mul, map_one, star_sub, star_star, neg_neg, star_def, conj_I, map_bit0,
               complex.conj_inv],
    rw [←neg_smul, this, neg_smul_neg],
  end⟩

/-- An element of a complex star module can be decomposed into self-adjoint "real" and "imaginary"
parts -/
lemma eq_re_add_im (x : E) : x = re x + I • im x :=
begin
  simp only [smul_smul, ←mul_assoc, neg_smul, smul_neg, I_mul_I, one_mul, neg_neg, smul_sub,
            ←add_smul, add_add_sub_cancel, re_coe, smul_add, im_coe, neg_mul_eq_neg_mul_symm,
            complex.I_mul_I],
  field_simp
end

end complex

end star_ring
