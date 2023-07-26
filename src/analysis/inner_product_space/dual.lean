/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.inner_product_space.projection
import analysis.normed_space.dual
import analysis.normed_space.star.basic

/-!
# The Fréchet-Riesz representation theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `inner_product_space.continuous_linear_map_of_bilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `to_dual`.


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
variables (E : Type*) [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := star_ring_end _

/--
An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/
def to_dual_map : E →ₗᵢ⋆[𝕜] normed_space.dual 𝕜 E :=
{ norm_map' := innerSL_apply_norm _,
 ..innerSL 𝕜 }

variables {E}

@[simp] lemma to_dual_map_apply {x y : E} : to_dual_map 𝕜 E x y = ⟪x, y⟫ := rfl

lemma innerSL_norm [nontrivial E] : ‖(innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜)‖ = 1 :=
show ‖(to_dual_map 𝕜 E).to_continuous_linear_map‖ = 1,
  from linear_isometry.norm_to_continuous_linear_map _

variable {𝕜}

lemma ext_inner_left_basis {ι : Type*} {x y : E} (b : basis ι 𝕜 E)
  (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y :=
begin
  apply (to_dual_map 𝕜 E).map_eq_iff.mp,
  refine (function.injective.eq_iff continuous_linear_map.coe_injective).mp (basis.ext b _),
  intro i,
  simp only [to_dual_map_apply, continuous_linear_map.coe_coe],
  rw [←inner_conj_symm],
  nth_rewrite_rhs 0 [←inner_conj_symm],
  exact congr_arg conj (h i)
end

lemma ext_inner_right_basis {ι : Type*} {x y : E} (b : basis ι 𝕜 E)
  (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y :=
begin
  refine ext_inner_left_basis b (λ i, _),
  rw [←inner_conj_symm],
  nth_rewrite_rhs 0 [←inner_conj_symm],
  exact congr_arg conj (h i)
end


variables (𝕜) (E) [complete_space E]

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
-/
def to_dual : E ≃ₗᵢ⋆[𝕜] normed_space.dual 𝕜 E :=
linear_isometry_equiv.of_surjective (to_dual_map 𝕜 E)
begin
  intros ℓ,
  set Y := linear_map.ker ℓ with hY,
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
    { rw [linear_map.mem_ker, map_sub, continuous_linear_map.map_smul,
          continuous_linear_map.map_smul, algebra.id.smul_eq_mul, algebra.id.smul_eq_mul, mul_comm],
      exact sub_self (ℓ x * ℓ z) },
    have h₂ : (ℓ z) * ⟪z, x⟫ = (ℓ x) * ⟪z, z⟫,
    { have h₃ := calc
        0    = ⟪z, (ℓ z) • x - (ℓ x) • z⟫       : by { rw [(Y.mem_orthogonal' z).mp hz], exact h₁ }
         ... = ⟪z, (ℓ z) • x⟫ - ⟪z, (ℓ x) • z⟫  : by rw [inner_sub_right]
         ... = (ℓ z) * ⟪z, x⟫ - (ℓ x) * ⟪z, z⟫  : by simp [inner_smul_right],
      exact sub_eq_zero.mp (eq.symm h₃) },
    have h₄ := calc
      ⟪((ℓ z)† / ⟪z, z⟫) • z, x⟫ = (ℓ z) / ⟪z, z⟫ * ⟪z, x⟫
            : by simp [inner_smul_left, conj_conj]
                            ... = (ℓ z) * ⟪z, x⟫ / ⟪z, z⟫
            : by rw [←div_mul_eq_mul_div]
                            ... = (ℓ x) * ⟪z, z⟫ / ⟪z, z⟫
            : by rw [h₂]
                            ... = ℓ x
            : by field_simp [inner_self_ne_zero.2 z_ne_0],
    exact h₄ }
end

variables {𝕜} {E}

@[simp] lemma to_dual_apply {x y : E} : to_dual 𝕜 E x y = ⟪x, y⟫ := rfl

@[simp] lemma to_dual_symm_apply {x : E} {y : normed_space.dual 𝕜 E} :
  ⟪(to_dual 𝕜 E).symm y, x⟫ = y x :=
begin
  rw ← to_dual_apply,
  simp only [linear_isometry_equiv.apply_symm_apply],
end

variables {E 𝕜}

/--
Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] normed_space.dual 𝕜 E`
and dualizing the result using `to_dual`.
-/
def continuous_linear_map_of_bilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
comp (to_dual 𝕜 E).symm.to_continuous_linear_equiv.to_continuous_linear_map B

local postfix `♯`:1025 := continuous_linear_map_of_bilin

variables (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

@[simp]
lemma continuous_linear_map_of_bilin_apply (v w : E) : ⟪(B♯ v), w⟫ = B v w :=
by simp [continuous_linear_map_of_bilin]

lemma unique_continuous_linear_map_of_bilin {v f : E}
  (is_lax_milgram : (∀ w, ⟪f, w⟫ = B v w)) :
  f = B♯ v :=
begin
  refine ext_inner_right 𝕜 _,
  intro w,
  rw continuous_linear_map_of_bilin_apply,
  exact is_lax_milgram w,
end

end inner_product_space
