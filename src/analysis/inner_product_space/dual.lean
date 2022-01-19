/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.inner_product_space.projection
import analysis.normed_space.dual

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

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

variables (𝕜 : Type*)
variables (E : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := star_ring_aut

/--
An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/
def to_dual_map : E →ₗᵢ⋆[𝕜] normed_space.dual 𝕜 E :=
{ to_fun := λ x, linear_map.mk_continuous
    { to_fun := λ y, ⟪x, y⟫,
      map_add' := λ _ _, inner_add_right,
      map_smul' := λ _ _, inner_smul_right }
    ∥x∥
    (λ y, by { rw [is_R_or_C.norm_eq_abs], exact abs_inner_le_norm _ _ }),
  map_add' := λ x y, by { ext z, simp [inner_add_left] },
  map_smul' := λ c y, by { ext z, simp [inner_smul_left] },
  norm_map' := λ x, begin
    refine le_antisymm _ _,
    { exact linear_map.mk_continuous_norm_le _ (norm_nonneg _) _ },
    { cases eq_or_lt_of_le (norm_nonneg x) with h h,
      { have : x = 0 := norm_eq_zero.mp (eq.symm h),
        simp [this] },
      { refine (mul_le_mul_right h).mp _,
        calc ∥x∥ * ∥x∥ = ∥x∥ ^ 2 : by ring
        ... = re ⟪x, x⟫ : norm_sq_eq_inner _
        ... ≤ abs ⟪x, x⟫ : re_le_abs _
        ... = ∥linear_map.mk_continuous _ _ _ x∥ : by simp [norm_eq_abs]
        ... ≤ ∥linear_map.mk_continuous _ _ _∥ * ∥x∥ : le_op_norm _ x } }
  end }

variables {E}

@[simp] lemma to_dual_map_apply {x y : E} : to_dual_map 𝕜 E x y = ⟪x, y⟫ := rfl

variables (E) [complete_space E]

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
-/
def to_dual : E ≃ₗᵢ⋆[𝕜] normed_space.dual 𝕜 E :=
linear_isometry_equiv.of_surjective (to_dual_map 𝕜 E)
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

variables {E}

@[simp] lemma to_dual_apply {x y : E} : to_dual 𝕜 E x y = ⟪x, y⟫ := rfl

end inner_product_space
