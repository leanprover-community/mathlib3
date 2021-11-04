/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.linear_isometry

/-!
# Normed star rings and algebras

A normed star ring is a star ring endowed with a norm such that the star operation is isometric.

A C⋆-ring is a normed star ring that verifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.
If a C⋆-ring is also a star algebra, then it is a C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [cstar_ring E] [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

-/

local postfix `⋆`:1000 := star

/-- A normed star ring is a star ring endowed with a norm such that `star` is isometric. -/
class normed_star_ring (E : Type*) [normed_ring E] [star_ring E] :=
(norm_star : ∀ {x : E}, ∥x⋆∥ = ∥x∥)

export normed_star_ring (norm_star)
attribute [simp] norm_star

/-- A C*-ring is a normed star ring that satifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2`
for every `x`. -/
class cstar_ring (E : Type*) extends normed_ring E, star_ring E :=
(norm_star_mul_self : ∀ {x : E}, ∥x⋆ * x∥ = ∥x∥ * ∥x∥)

variables {𝕜 E : Type*}

open cstar_ring

/-- In a C*-ring, star preserves the norm. -/
instance cstar_ring.to_normed_star_ring {E : Type*} [cstar_ring E] : normed_star_ring E :=
⟨begin
  intro x,
  by_cases htriv : x = 0,
  { simp only [htriv, star_zero] },
  { change x ≠ 0 at htriv,
    have hnt : 0 < ∥x∥ := norm_pos_iff.mpr htriv,
    have hnt_star : 0 < ∥x⋆∥ :=
      norm_pos_iff.mpr ((add_equiv.map_ne_zero_iff star_add_equiv).mpr htriv),
    have h₁ := calc
      ∥x∥ * ∥x∥ = ∥x⋆ * x∥        : norm_star_mul_self.symm
            ... ≤ ∥x⋆∥ * ∥x∥      : norm_mul_le _ _,
    have h₂ := calc
      ∥x⋆∥ * ∥x⋆∥ = ∥x * x⋆∥      : by rw [←norm_star_mul_self, star_star]
             ... ≤ ∥x∥ * ∥x⋆∥     : norm_mul_le _ _,
    exact le_antisymm (le_of_mul_le_mul_right h₂ hnt_star) (le_of_mul_le_mul_right h₁ hnt) },
end⟩

lemma cstar_ring.norm_self_mul_star [cstar_ring E] {x : E} : ∥x * x⋆∥ = ∥x∥ * ∥x∥ :=
by { nth_rewrite 0 [←star_star x], simp only [norm_star_mul_self, norm_star] }

/-- `star` bundled as a linear isometric equivalence -/
noncomputable def starₗᵢ [comm_semiring 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E]
  [normed_star_ring E] [module 𝕜 E] [star_module 𝕜 E] : E ≃ₗᵢ⋆[𝕜] E :=
linear_isometry_equiv.of_surjective
{ to_fun := star,
  map_add' := star_add,
  map_smul' := star_smul,
  norm_map' := λ x, norm_star }
(λ x, ⟨x⋆, star_star x⟩)
