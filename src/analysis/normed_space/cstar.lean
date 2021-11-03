/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.basic

/-!
# C⋆-rings and C⋆-algebras

A C⋆-ring is a normed star-ring that verifies the condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.
If a C⋆-ring is also a star algebra, then it is a C⋆-algebra.

To get a C⋆-algebra, use
`{𝕜 : Type*} [normed_field 𝕜] [star_ring 𝕜] [cstar_ring E] [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

* Bundle star as an isometry

-/

local postfix `⋆`:1000 := star

class cstar_ring (E : Type*) extends normed_ring E, star_ring E :=
(norm_star_mul_self : ∀ {x : E}, ∥x⋆ * x∥ = ∥x∥ * ∥x∥)

namespace cstar_ring

variables {𝕜 : Type*} {E : Type*}
variables [normed_field 𝕜] [star_ring 𝕜] [cstar_ring E]

-- move this
lemma eq_zero_of_star_eq_zero {x : E} (h : x⋆ = 0) : x = 0 :=
by { rw [←star_zero] at h, simpa only [star_star] using (congr_arg star h) }

@[simp] lemma norm_star {x : E} : ∥x⋆∥ = ∥x∥ :=
begin
  by_cases htriv : x = 0,
  { simp only [htriv, star_zero] },
  { change x ≠ 0 at htriv,
    have hnt : 0 < ∥x∥ := norm_pos_iff.mpr htriv,
    have hnt_star : 0 < ∥x⋆∥ := norm_pos_iff.mpr (λ H, htriv (eq_zero_of_star_eq_zero H)),
    have h₁ := calc
      ∥x∥ * ∥x∥ = ∥x⋆ * x∥        : norm_star_mul_self.symm
            ... ≤ ∥x⋆∥ * ∥x∥      : norm_mul_le _ _,
    have h₂ := calc
      ∥x⋆∥ * ∥x⋆∥ = ∥x * x⋆∥      : by rw [←norm_star_mul_self, star_star]
             ... ≤ ∥x∥ * ∥x⋆∥     : norm_mul_le _ _,
    exact le_antisymm (le_of_mul_le_mul_right h₂ hnt_star) (le_of_mul_le_mul_right h₁ hnt) },
end

lemma norm_self_mul_star {x : E} : ∥x * x⋆∥ = ∥x∥ * ∥x∥ :=
by { nth_rewrite 0 [←star_star x], simp only [norm_star_mul_self, norm_star] }

end cstar_ring
