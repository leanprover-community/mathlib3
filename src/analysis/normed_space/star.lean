/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed.group.hom
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry

/-!
# Normed star rings and algebras

A normed star monoid is a `star_add_monoid` endowed with a norm such that the star operation is
isometric.

A C⋆-ring is a normed star monoid that is also a ring and that verifies the stronger
condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `∥x⋆ * x∥ = ∥x∥^2` is equivalent to `∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/

open_locale topological_space

local postfix `⋆`:std.prec.max_plus := star

/-- A normed star ring is a star ring endowed with a norm such that `star` is isometric. -/
class normed_star_monoid (E : Type*) [normed_group E] [star_add_monoid E] :=
(norm_star : ∀ {x : E}, ∥x⋆∥ = ∥x∥)

export normed_star_monoid (norm_star)
attribute [simp] norm_star

/-- A C*-ring is a normed star ring that satifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2`
for every `x`. -/
class cstar_ring (E : Type*) [normed_ring E] [star_ring E] :=
(norm_star_mul_self : ∀ {x : E}, ∥x⋆ * x∥ = ∥x∥ * ∥x∥)

noncomputable instance : cstar_ring ℝ :=
{ norm_star_mul_self := λ x, by simp only [star, id.def, normed_field.norm_mul] }

variables {𝕜 E α : Type*}

section normed_star_monoid
variables [normed_group E] [star_add_monoid E] [normed_star_monoid E]

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def star_normed_group_hom : normed_group_hom E E :=
{ bound' := ⟨1, λ v, le_trans (norm_star.le) (one_mul _).symm.le⟩,
  .. star_add_equiv }

/-- The `star` map in a normed star group is an isometry -/
lemma star_isometry : isometry (star : E → E) :=
star_add_equiv.to_add_monoid_hom.isometry_of_norm (λ _, norm_star)

lemma continuous_star : continuous (star : E → E) := star_isometry.continuous

lemma continuous_on_star {s : set E} : continuous_on star s := continuous_star.continuous_on

lemma continuous_at_star {x : E} : continuous_at star x := continuous_star.continuous_at

lemma continuous_within_at_star {s : set E} {x : E} : continuous_within_at star s x :=
continuous_star.continuous_within_at

lemma tendsto_star (x : E) : filter.tendsto star (𝓝 x) (𝓝 x⋆) := continuous_star.tendsto x

lemma filter.tendsto.star {f : α → E} {l : filter α} {y : E} (h : filter.tendsto f l (𝓝 y)) :
  filter.tendsto (λ x, (f x)⋆) l (𝓝 y⋆) :=
(continuous_star.tendsto y).comp h

variables [topological_space α]

lemma continuous.star {f : α → E} (hf : continuous f) : continuous (λ y, star (f y)) :=
continuous_star.comp hf

lemma continuous_at.star {f : α → E} {x : α} (hf : continuous_at f x) :
  continuous_at (λ x, (f x)⋆) x :=
continuous_at_star.comp hf

lemma continuous_on.star {f : α → E} {s : set α} (hf : continuous_on f s) :
  continuous_on (λ x, (f x)⋆) s :=
continuous_star.comp_continuous_on hf

lemma continuous_within_at.star {f : α → E} {s : set α} {x : α}
  (hf : continuous_within_at f s x) : continuous_within_at (λ x, (f x)⋆) s x := hf.star

end normed_star_monoid

instance ring_hom_isometric.star_ring_aut [normed_comm_ring E] [star_ring E]
   [normed_star_monoid E] : ring_hom_isometric (star_ring_aut E : E →+* E) :=
⟨λ _, norm_star⟩

namespace cstar_ring
variables [normed_ring E] [star_ring E] [cstar_ring E]

/-- In a C*-ring, star preserves the norm. -/
@[priority 100] -- see Note [lower instance priority]
instance to_normed_star_monoid : normed_star_monoid E :=
⟨begin
  intro x,
  by_cases htriv : x = 0,
  { simp only [htriv, star_zero] },
  { have hnt : 0 < ∥x∥ := norm_pos_iff.mpr htriv,
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

lemma norm_self_mul_star {x : E} : ∥x * x⋆∥ = ∥x∥ * ∥x∥ :=
by { nth_rewrite 0 [←star_star x], simp only [norm_star_mul_self, norm_star] }

lemma norm_star_mul_self' {x : E} : ∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥ :=
by rw [norm_star_mul_self, norm_star]

@[simp] lemma norm_one [nontrivial E] : ∥(1 : E)∥ = 1 :=
begin
  cases mul_eq_mul_right_iff.mp
    (calc 1 * ∥(1 : E)∥ = ∥(1 : E)∥              : one_mul _
                   ...  = ∥(1 : E)⋆ * 1∥         : by rw [mul_one, star_one]
                   ...  = ∥(1 : E)∥ * ∥(1 : E)∥  : norm_star_mul_self) with h,
  { exact h.symm },
  { exfalso,
    exact one_ne_zero (norm_eq_zero.mp h) }
end

end cstar_ring

section starₗᵢ

variables [comm_semiring 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [normed_star_monoid E]
variables [module 𝕜 E] [star_module 𝕜 E]

variables (𝕜)
/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
{ map_smul' := star_smul,
  norm_map' := λ x, norm_star,
  .. star_add_equiv }

variables {𝕜}

@[simp] lemma coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star := rfl

lemma starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x := rfl

end starₗᵢ
