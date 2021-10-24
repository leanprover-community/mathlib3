/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.inner_product_space.projection
import analysis.normed_space.dual

/-!
# The Fréchet-Riesz representation theorem

We consider inner product spaces, with base field over `ℝ` (the corresponding results for `ℂ`
will require the definition of conjugate-linear maps). We define `to_dual_map`, a linear isometric
embedding of `E` into its dual, which maps an element `x` of the space to `λ y, ⟪x, y⟫`. We also
define `to_dual'` as the function taking taking a vector to its dual for a base field `𝕜`
with `[is_R_or_C 𝕜]`; this is a function and not a linear map.

Finally, under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to
`to_dual`, a linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual'`.  This is the Fréchet-Riesz representation theorem: every element of the
dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable theory
open_locale classical
universes u v

namespace inner_product_space
open is_R_or_C continuous_linear_map

section is_R_or_C

variables (𝕜 : Type*)
variables {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := star_ring_aut

/--
Given some `x` in an inner product space, we can define its dual as the continuous linear map
`λ y, ⟪x, y⟫`. Consider using `to_dual` or `to_dual_map` instead in the real case.
-/
def to_dual' : E →+ normed_space.dual 𝕜 E :=
{ to_fun := λ x, linear_map.mk_continuous
  { to_fun := λ y, ⟪x, y⟫,
    map_add' := λ _ _, inner_add_right,
    map_smul' := λ _ _, inner_smul_right }
  ∥x∥
  (λ y, by { rw [is_R_or_C.norm_eq_abs], exact abs_inner_le_norm _ _ }),
  map_zero' := by { ext z, simp },
  map_add' := λ x y, by { ext z, simp [inner_add_left] } }

@[simp] lemma to_dual'_apply {x y : E} : to_dual' 𝕜 x y = ⟪x, y⟫ := rfl

/-- In an inner product space, the norm of the dual of a vector `x` is `∥x∥` -/
@[simp] lemma norm_to_dual'_apply (x : E) : ∥to_dual' 𝕜 x∥ = ∥x∥ :=
begin
  refine le_antisymm _ _,
  { exact linear_map.mk_continuous_norm_le _ (norm_nonneg _) _ },
  { cases eq_or_lt_of_le (norm_nonneg x) with h h,
    { have : x = 0 := norm_eq_zero.mp (eq.symm h),
      simp [this] },
    { refine (mul_le_mul_right h).mp _,
      calc ∥x∥ * ∥x∥ = ∥x∥ ^ 2 : by ring
      ... = re ⟪x, x⟫ : norm_sq_eq_inner _
      ... ≤ abs ⟪x, x⟫ : re_le_abs _
      ... = ∥to_dual' 𝕜 x x∥ : by simp [norm_eq_abs]
      ... ≤ ∥to_dual' 𝕜 x∥ * ∥x∥ : le_op_norm (to_dual' 𝕜 x) x } }
end

variables (E)

lemma to_dual'_isometry : isometry (@to_dual' 𝕜 E _ _) :=
add_monoid_hom.isometry_of_norm _ (norm_to_dual'_apply 𝕜)

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual'` is surjective.
-/
lemma to_dual'_surjective [complete_space E] : function.surjective (@to_dual' 𝕜 E _ _) :=
begin
  intros ℓ,
  set Y := ker ℓ with hY,
  by_cases htriv : Y = ⊤,
  { have hℓ : ℓ = 0,
    { have h' := linear_map.ker_eq_top.mp htriv,
      rw [←coe_zero] at h',
      apply coe_injective,
      exact h' },
    exact ⟨0, by simp [hℓ]⟩ },
  { have Ycomplete := is_complete_ker ℓ,
    rw [← submodule.orthogonal_eq_bot_iff Ycomplete, ←hY] at htriv,
    change Yᗮ ≠ ⊥ at htriv,
    rw [submodule.ne_bot_iff] at htriv,
    obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv,
    refine ⟨((ℓ z)† / ⟪z, z⟫) • z, _⟩,
    ext x,
    have h₁ : (ℓ z) • x - (ℓ x) • z ∈ Y,
    { rw [mem_ker, map_sub, map_smul, map_smul, algebra.id.smul_eq_mul, algebra.id.smul_eq_mul,
          mul_comm],
      exact sub_self (ℓ x * ℓ z) },
    have h₂ : (ℓ z) * ⟪z, x⟫ = (ℓ x) * ⟪z, z⟫,
    { have h₃ := calc
        0    = ⟪z, (ℓ z) • x - (ℓ x) • z⟫       : by { rw [(Y.mem_orthogonal' z).mp hz], exact h₁ }
         ... = ⟪z, (ℓ z) • x⟫ - ⟪z, (ℓ x) • z⟫  : by rw [inner_sub_right]
         ... = (ℓ z) * ⟪z, x⟫ - (ℓ x) * ⟪z, z⟫  : by simp [inner_smul_right],
      exact sub_eq_zero.mp (eq.symm h₃) },
    have h₄ := calc
      ⟪((ℓ z)† / ⟪z, z⟫) • z, x⟫ = (ℓ z) / ⟪z, z⟫ * ⟪z, x⟫
            : by simp [inner_smul_left, ring_equiv.map_div, conj_conj]
                            ... = (ℓ z) * ⟪z, x⟫ / ⟪z, z⟫
            : by rw [←div_mul_eq_mul_div]
                            ... = (ℓ x) * ⟪z, z⟫ / ⟪z, z⟫
            : by rw [h₂]
                            ... = ℓ x
            : begin
                have : ⟪z, z⟫ ≠ 0,
                { change z = 0 → false at z_ne_0,
                  rwa ←inner_self_eq_zero at z_ne_0 },
                field_simp [this]
              end,
    exact h₄ }
end

end is_R_or_C

section real

variables (F : Type*) [inner_product_space ℝ F]

/-- In a real inner product space `F`, the function that takes a vector `x` in `F` to its dual
`λ y, ⟪x, y⟫` is an isometric linear embedding. If the space is complete (i.e. is a Hilbert space),
consider using `to_dual` instead. -/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)
def to_dual_map : F →ₗᵢ[ℝ] (normed_space.dual ℝ F) :=
{ to_fun := to_dual' ℝ,
  map_add' := λ x y, by { ext, simp [inner_add_left] },
  map_smul' := λ c x, by { ext, simp [inner_smul_left] },
  norm_map' := norm_to_dual'_apply ℝ }

variables {F}

@[simp] lemma to_dual_map_apply {x y : F} : to_dual_map F x y = ⟪x, y⟫_ℝ := rfl

variables (F) [complete_space F]

/--
Fréchet-Riesz representation: If `F` is a Hilbert space, the function that takes a vector in `F` to
its dual is an isometric linear equivalence.  -/
def to_dual : F ≃ₗᵢ[ℝ] (normed_space.dual ℝ F) :=
linear_isometry_equiv.of_surjective (to_dual_map F) (to_dual'_surjective ℝ F)

variables {F}

@[simp] lemma to_dual_apply {x y : F} : to_dual F x y = ⟪x, y⟫_ℝ := rfl

end real

end inner_product_space
