/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import data.complex.is_R_or_C
import analysis.normed_space.star

/-!
# Star modules over `is_R_or_C` fields

FIXME

## Main definitions

None.

## Main theorems

## Notes

-/

noncomputable theory
open is_R_or_C
open_locale complex_conjugate

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [star_add_monoid E] [star_module 𝕜 E]

namespace self_adjoints

instance : has_scalar ℝ (self_adjoints E) :=
⟨λ r x, ⟨(r : 𝕜) • (x : E), by { simp only [star_coe_eq, star_smul],
                            show (conj (r : 𝕜)) • (x : E) = (r : 𝕜) • x, by rw [conj_of_real r] }⟩⟩

include 𝕜
@[simp] lemma coe_smul (r : ℝ) (x : self_adjoints E) :
  (coe : self_adjoints E → E) (r • x) = (r : 𝕜) • (x : E) := rfl

instance : mul_action ℝ (self_adjoints E) :=
{ one_smul := λ x, by { ext, simp only [one_smul, coe_smul, of_real_one] },
  mul_smul := λ r s x, by { ext, simp only [mul_smul, of_real_mul, coe_smul] },
  ..show has_scalar ℝ (self_adjoints E), by apply_instance }

instance : distrib_mul_action ℝ (self_adjoints E) :=
{ smul_add := λ r x y, by { ext, simp only [smul_add, coe_smul, coe_add] },
  smul_zero := λ r, by { ext, simp only [coe_zero, coe_smul, smul_zero] } }

instance : module ℝ (self_adjoints E) :=
{ add_smul := λ r s x, by { ext, simp only [add_smul, of_real_add, coe_smul, coe_add] },
  zero_smul := λ x, by { ext, simp only [of_real_zero, coe_zero, coe_smul, zero_smul] } }

instance : normed_space ℝ (self_adjoints E) :=
⟨λ r x, le_of_eq $ by simp only [coe_smul, norm_coe, norm_smul, norm_of_real]⟩

instance : star_module ℝ (self_adjoints E) :=
⟨λ r x, by simp only [star, id.def]⟩

omit 𝕜

end self_adjoints
