/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import data.complex.basic
import algebra.algebra.basic

/-!
# Complex number as a vector space over `ℝ`

This file contains three instances:
* `ℂ` is an `ℝ` algebra;
* any complex vector space is a real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines three linear maps:

* `complex.linear_map.re`;
* `complex.linear_map.im`;
* `complex.linear_map.of_real`.

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as `ℝ`-linear maps.
-/
noncomputable theory

namespace complex

instance algebra_over_reals : algebra ℝ ℂ := (complex.of_real).to_algebra

@[simp] lemma smul_coe {x : ℝ} {z : ℂ} : x • z = x * z := rfl

instance : ordered_algebra ℝ ℂ :=
{ smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, rfl⟩ := lt_def.mp h₁,
    refine lt_def.mpr ⟨x * y, _, _⟩,
    exact mul_pos h₂ l,
    ext; simp [mul_add],
  end,
  lt_of_smul_lt_smul_of_nonneg := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, e⟩ := lt_def.mp h₁,
    by_cases h : x = 0,
    { subst h, simp at h₁, exfalso, exact lt_irrefl 0 h₁, },
    { replace h₂ : 0 < x := lt_of_le_of_ne h₂ (by { symmetry, exact h }),
      refine lt_def.mpr ⟨y / x, div_pos l h₂, _⟩,
      replace e := congr_arg (λ z, (x⁻¹ : ℂ) * z) e,
      simp only [mul_add, ←mul_assoc, h, one_mul, of_real_eq_zero, smul_coe, ne.def,
        not_false_iff, inv_mul_cancel] at e,
      convert e,
      simp only [div_eq_iff_mul_eq, h, of_real_eq_zero, of_real_div, ne.def, not_false_iff],
      norm_cast,
      simp [mul_comm _ y, mul_assoc, h],
    },
  end }

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
semimodule.restrict_scalars' ℝ ℂ E
attribute [instance, priority 900] module.complex_to_real

instance (E : Type*) [add_comm_group E] [module ℝ E]
  (F : Type*) [add_comm_group F] [module ℂ F] : module ℂ (E →ₗ[ℝ] F) :=
linear_map.module_extend_scalars _ _ _ _

namespace complex

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def linear_map.re : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := by simp,
  map_smul' := λc x, by { change ((c : ℂ) * x).re = c * x.re, simp } }

@[simp] lemma linear_map.coe_re : ⇑linear_map.re = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def linear_map.im : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := by simp,
  map_smul' := λc x, by { change ((c : ℂ) * x).im = c * x.im, simp } }

@[simp] lemma linear_map.coe_im : ⇑linear_map.im = im := rfl

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_map.of_real : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := coe,
  map_add' := by simp,
  map_smul' := λc x, by simp }

@[simp] lemma linear_map.coe_of_real : ⇑linear_map.of_real = coe := rfl

end complex
