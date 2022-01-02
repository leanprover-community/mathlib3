/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.inner_product_space.projection
import analysis.normed_space.dual
import analysis.normed_space.star

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
open_locale classical complex_conjugate
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
{ norm_map' := λ _, innerSL_apply_norm,
 ..innerSL }

variables {E}

@[simp] lemma to_dual_map_apply {x y : E} : to_dual_map 𝕜 E x y = ⟪x, y⟫ := rfl

lemma innerSL_norm [nontrivial E] : ∥(innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜)∥ = 1 :=
show ∥(to_dual_map 𝕜 E).to_continuous_linear_map∥ = 1,
  from linear_isometry.norm_to_continuous_linear_map _

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
  { rw [← submodule.orthogonal_eq_bot_iff] at htriv,
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

@[simp] lemma to_dual_symm_apply {x : E} {y : normed_space.dual 𝕜 E} :
  ⟪(to_dual 𝕜 E).symm y, x⟫ = y x :=
begin
  rw ← to_dual_apply,
  simp only [linear_isometry_equiv.apply_symm_apply],
end

variable (𝕜)
include 𝕜
lemma ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
begin
  apply (to_dual 𝕜 E).map_eq_iff.mp,
  ext v,
  rw [to_dual_apply, to_dual_apply, ←inner_conj_sym],
  nth_rewrite_rhs 0 [←inner_conj_sym],
  exact congr_arg conj (h v)
end

lemma ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
begin
  refine ext_inner_left 𝕜 (λ v, _),
  rw [←inner_conj_sym],
  nth_rewrite_rhs 0 [←inner_conj_sym],
  exact congr_arg conj (h v)
end
omit 𝕜
variable {𝕜}

end inner_product_space
