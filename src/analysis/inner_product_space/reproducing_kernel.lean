/-
Copyright (c) 2022 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import analysis.inner_product_space.projection
import analysis.inner_product_space.positive

/-!
# Reproducing Kernel Hilbert Space

A Hilbert space `H` is called a reproducing kernel Hilbert space (RKHS) if it is a vector subspace
of `X → V` where `V` is a Hilbert space, and the evaluation map `H → V` at each `X` is continuous.

## Main definitions

* `rkhs 𝕜 X V H` - `H` is a RKHS, where `𝕜` is the scalar field, `X` is the domain, `V` is the
  Hilbert space.
* `rkhs.kernel` - the kernel of a RKHS, as a continuous linear map `V →L[𝕜] V`
* `rkhs.eval'` - For `V = 𝕜`, by the Riesz representation theorem, the evaluation map can be
  represented as the inner product with a point in `H`, which we call the `eval'`
* `rkhs.scalar_kernel` - For `V = 𝕜`, we can represent the kernel of `H` as an inner product with a
  point in `H`, which we call the `scalar_kernel`
* `rkhs.eval'_span` - The span of the `eval'`s as a subspace of `H`.

## Main statements

* `rkhs.eval'_span_topological_closure_eq_top` - the topological closude of the span of the
  `eval's` is the whole space `H`.
* `rkhs.tendsto_nhds_apply` - Convergence in `H` implies pointwise convergence.

## Notes

Due to the statement of the Riesz representation theorem in mathlib, the order of `x` and `y` in
the definition of the `scalar_kernel` and the representation of it as an inner product of
`eval'`s is reversed. I opted to keep the statement simpler, but this leaves the order
reversed.

## Tags

Reproducing kernel Hilbert space, RKHS
-/

noncomputable theory

open_locale inner_product topological_space
open inner_product_space filter

variables (𝕜 : Type*) [is_R_or_C 𝕜]
variables (X : Type*)
variables (V : Type*) [inner_product_space 𝕜 V]

/--
A reproducing kernel Hilbert space (RKHS) is a vector subspace of `X → V` where evaluation at a
point is continuous.
-/
class rkhs (H : Type*) [inner_product_space 𝕜 H] extends fun_like H X (λ _, V) :=
(add_apply' : ∀ {f g : H} {x : X}, (f + g) x = f x + g x)
(smul_apply' : ∀ {c : 𝕜} {f : H} {x : X}, (c • f) x = c • f x)
(continuous_eval' : ∀ (x : X), continuous (λ (f : H), f x))

attribute [nolint dangerous_instance] rkhs.to_fun_like

namespace rkhs

variables {𝕜 X V}
variables {H : Type*} [inner_product_space 𝕜 H] [hHrkhs : rkhs 𝕜 X V H]

include hHrkhs

@[simp]
lemma add_apply (f g : H) (x : X) : (f + g) x = f x + g x := rkhs.add_apply'

@[simp]
lemma smul_apply (c : 𝕜) (f : H) (x : X) : (c • f) x = c • f x := rkhs.smul_apply'

@[simp]
lemma zero_apply (x : X) : (0 : H) x = 0 := by rw [←zero_smul 𝕜 (0 : H), smul_apply, zero_smul]

section defs

variables (𝕜 V H)

/--
The embedding of an element `f : H` of an RKHS into `X → V`
-/
def to_pi : H →ₗ[𝕜] (X → V) :=
{ to_fun := λ f, f,
  map_add' := λ f g, funext $ add_apply f g,
  map_smul' := λ c f, funext $ smul_apply c f }

/--
Evaluation at a point `x` as a bundled continuous linear map `H →L[𝕜] V`
-/
def eval (x : X) : H →L[𝕜] V :=
{ to_fun := λ f, f x,
  map_add' := λ f g, add_apply f g x,
  map_smul' := λ c f, smul_apply c f x,
  cont := continuous_eval' x }

end defs

@[simp]
lemma to_pi_apply (f : H) (x : X) : to_pi 𝕜 V H f x = f x := rfl

@[simp]
lemma eval_apply (f : H) (x : X) : eval 𝕜 V H x f = f x := rfl

lemma to_pi_inj : function.injective (to_pi 𝕜 V H : H → (X → V)) :=
λ f g h, fun_like.coe_injective $ funext $ congr_fun h

section complete_space

variables (𝕜 V H) [complete_space V] [complete_space H]

/--
The kernel of an RKHS, as a continuous linear function `V →L[𝕜] V`
-/
def kernel (x y : X) : V →L[𝕜] V := (eval 𝕜 V H x).comp $ (eval 𝕜 V H y)†

variables {𝕜 V H}

lemma kernel_def (x y : X) : kernel 𝕜 V H x y = (eval 𝕜 V H x).comp ((eval 𝕜 V H y)†) := rfl

end complete_space

/-!
## Scalar functionals

In this section, we focus on the case `V = 𝕜`.
-/

section scalar

omit hHrkhs

section defs

variables (𝕜 X)
variables (H₁ : Type*) [inner_product_space 𝕜 H₁] [complete_space H₁] [hH₁rkhs : rkhs 𝕜 X 𝕜 H₁]

include hH₁rkhs

/--
Evaluation at a point `x`, represented as a point `eval' x` in the RKHS `H₁` by the Riesz
representation theorem.
-/
def eval' (x : X) : H₁ := (to_dual 𝕜 H₁).symm (eval 𝕜 𝕜 H₁ x)

/--
The kernel of an RKHS, represented as a scalar value.
-/
def scalar_kernel (x y : X) : 𝕜 := (to_dual 𝕜 𝕜).symm (kernel 𝕜 𝕜 H₁ x y)

/--
The span of all points of the form `eval' x` as a subspace of `H₁`.
-/
def eval'_span : submodule 𝕜 H₁ := submodule.span 𝕜 $ set.range (eval' 𝕜 X H₁)

end defs

variables {H₁ : Type*} [inner_product_space 𝕜 H₁] [complete_space H₁] [hH₁rkhs : rkhs 𝕜 X 𝕜 H₁]
include hH₁rkhs

lemma eval'_def (x : X) : eval' 𝕜 X H₁ x = (to_dual 𝕜 H₁).symm (eval 𝕜 𝕜 H₁ x) := rfl

lemma inner_eval' (f : H₁) (x : X) : inner (eval' 𝕜 X H₁ x) f = f x :=
by rw [eval'_def, to_dual_symm_apply, eval_apply]

lemma eval'_eq_eval_adjoint (x : X) : eval' 𝕜 X H₁ x = (eval 𝕜 𝕜 H₁ x)† 1 :=
begin
  apply (to_dual 𝕜 H₁).injective,
  ext f,
  simp [continuous_linear_map.adjoint_apply, eval'_def],
end

lemma scalar_kernel_def (x y : X) :
  scalar_kernel 𝕜 X H₁ x y = (to_dual 𝕜 𝕜).symm (kernel 𝕜 𝕜 H₁ x y) := rfl

lemma scalar_kernel_eq_inner (x y : X) :
  scalar_kernel 𝕜 X H₁ x y = inner (eval' 𝕜 X H₁ y) (eval' 𝕜 X H₁ x) :=
begin
  apply (to_dual 𝕜 𝕜).injective,
  rw [scalar_kernel_def, linear_isometry_equiv.apply_symm_apply, kernel_def],
  ext,
  rw [continuous_linear_map.comp_apply, ←eval'_eq_eval_adjoint],
  simp only [eval_apply, to_dual_apply, is_R_or_C.inner_apply, inner_conj_sym, mul_one],
  rw inner_eval',
end

lemma kernel_conj_symm {x y : X} :
  scalar_kernel 𝕜 X H₁ x y = star_ring_end 𝕜 (scalar_kernel 𝕜 X H₁ y x) :=
by rw [scalar_kernel_eq_inner, scalar_kernel_eq_inner, inner_conj_sym]

lemma norm_eval'_eq_kernel {x : X} :
  ∥ eval' 𝕜 X H₁ x ∥^2 = is_R_or_C.re (scalar_kernel 𝕜 X H₁ x x) :=
by rw [←inner_self_eq_norm_sq, scalar_kernel_eq_inner]

lemma norm_eval_eq_kernel {x : X} :
  ∥ eval 𝕜 𝕜 H₁ x ∥^2 = is_R_or_C.re (scalar_kernel 𝕜 X H₁ x x) :=
by rw [←norm_eval'_eq_kernel, eval', linear_isometry_equiv.norm_map]

/--
The span of the `eval'`s is dense in H
-/
lemma eval'_span_topological_closure_eq_top :
  (eval'_span 𝕜 X H₁).topological_closure = ⊤ :=
begin
  rw [submodule.topological_closure_eq_top_iff, submodule.eq_bot_iff],
  intros f hf,
  apply fun_like.coe_injective,
  funext x,
  specialize hf (eval' 𝕜 X H₁ x) _,
  rw [eval'_span],
  apply submodule.subset_span,
  use x,
  rw inner_eval' at hf,
  rw [hf, zero_apply],
end

/--
If `f n` tendsto `F` in `H`, then `f n` tendsto `F` pointwise.
-/
lemma tendsto_nhds_apply (f : ℕ → H₁) (F : H₁) (hf : tendsto f at_top (𝓝 F))
  (x : X) : tendsto (λ n, f n x) at_top (𝓝 (F x)) :=
begin
  -- two cases, depending on whether `f x = 0` for all `f` in `H`.
  by_cases hker : eval' 𝕜 X H₁ x = 0,
  { convert tendsto_const_nhds,
    funext n,
    rw [←inner_eval', ←inner_eval', hker, inner_zero_left, inner_zero_left] },
  { rw [metric.tendsto_nhds] at ⊢ hf,
    intros ε hε,
    let ε' := ε / ∥ eval' 𝕜 X H₁ x ∥,
    have hε' : 0 < ε',
    { apply div_pos hε,
      rw norm_pos_iff,
      exact hker },
    specialize hf ε' hε',
    rw filter.eventually_at_top at ⊢ hf,
    rcases hf with ⟨N, hN⟩,
    use N,
    intros n hn,
    specialize hN n hn,
    rw [dist_eq_norm, ←inner_eval', ←inner_eval', ←inner_sub_right],
    refine lt_of_le_of_lt (norm_inner_le_norm _ _) _,
    rw dist_eq_norm at hN,
    rw [mul_comm, ←lt_div_iff],
    { exact hN },
    { rw norm_pos_iff,
      exact hker } }
end

end scalar

end rkhs
