/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.normed_space.operator_norm
import analysis.convex.cone
import linear_algebra.dimension

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces.

## TODO

Prove some corollaries

-/

section basic
variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions. -/
theorem exists_extension_norm_eq (p : subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (λ x, ∥f∥ * ∥x∥)
    (λ c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (λ x y, _) (λ x, le_trans (le_abs_self _) (f.le_op_norm _))
    with ⟨g, g_eq, g_le⟩,
  set g' := g.mk_continuous (∥f∥)
    (λ x, abs_le.2 ⟨neg_le.1 $ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩),
  { refine ⟨g', g_eq, _⟩,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (λ x, _),
      dsimp at g_eq,
      rw ← g_eq,
      apply g'.le_op_norm } },
  { simp only [← mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

end basic

section span
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

noncomputable theory
open_locale classical

/-- Temporary (this probably exists elsewhere).  Given an element `x` of a normed
    space `E` over `𝕜`, the natural map from `𝕜` to scalar multiples of `x`.-/
def span_map (x : E) : 𝕜 →ₗ[𝕜] E :=
{ to_fun := λ (c : 𝕜), c • x,
  add    := λ a b, add_smul a b x,
  smul   := λ a b, mul_smul a b x }

/-- Temporary (this probably exists elsewhere).  The span of an element `x` of
    a normed space `E`.-/
def span (x : E) : subspace 𝕜 E := (span_map 𝕜 x).range

lemma mem_span_self (x : E) : x ∈ span 𝕜 x :=
begin
  apply linear_map.mem_range.mpr,
  use 1, exact one_smul 𝕜 x,
end

/-- Temporary (this probably exists elsewhere).  Given a nonzero element `x` of
    a normed space `E` over `𝕜`, the natural map from `𝕜` to the span of `x`,
    with invertibility check to consider it as an isomorphism.-/
def span_equiv (x : E) (h : x ≠ 0) : 𝕜 ≃ₗ[𝕜] (span 𝕜 x) :=
linear_equiv.of_injective (span_map 𝕜 x)
begin
  ext c, split,
  { intros hc, simp, intros, simp at hc, by_contra hc',
    have : x = 0,
      calc x = c⁻¹ • (c • x) : by rw [← mul_smul, inv_mul_cancel hc', one_smul]
      ... = c⁻¹ • ((span_map 𝕜 x) c) : rfl
      ... = 0 : by rw [hc, smul_zero],
    tauto },
  { simp, intros h, rw h, simp }
end

lemma span_equiv_eval (x : E) (h : x ≠ 0) : (span_equiv 𝕜 x h).to_fun
  = span_equiv 𝕜 x h := rfl

/-- Temporary (this probably exists elsewhere).  Given a nonzero element `x` of
    a normed space `E` over `𝕜`, the natural map from the span of `x` to `𝕜`.-/
abbreviation coord (x : E) (h : x ≠ 0) : (span 𝕜 x) ≃ₗ[𝕜] 𝕜 :=
(span_equiv 𝕜 x h).symm

lemma coord_self (x : E) (h : x ≠ 0) : (coord 𝕜 x h) ⟨x, mem_span_self 𝕜 x⟩ = 1 :=
begin
  have : (⟨x, mem_span_self 𝕜 x⟩ : span 𝕜 x) = (span_equiv 𝕜 x h) 1,
    apply submodule.coe_eq_coe.mp,
    calc x = 1 • x : (one_smul 𝕜 _).symm
    ... = ↑((span_equiv 𝕜 x h) 1) : rfl,
  rw this, simp,
end

lemma coord_isometry (x : E) (h : x ≠ 0) (y : span 𝕜 x) :
  ∥x∥ * ∥coord 𝕜 x h y∥ = ∥y∥ :=
begin
  calc ∥x∥ * ∥coord 𝕜 x h y∥ = ∥(coord 𝕜 x h y) • x∥ : _
  ... = ∥span_equiv 𝕜 x h (coord 𝕜 x h y)∥ : _
  ... = ∥y∥ : _,
  rw [mul_comm, ← norm_smul], refl, simp,
end

lemma coord_lipschitz (x : E) (h : x ≠ 0) (y : span 𝕜 x) :
  ∥coord 𝕜 x h y∥ ≤ ∥x∥⁻¹ * ∥y∥ :=
begin
  have hx : ∥x∥ ≠ 0 := mt norm_eq_zero.mp h,
  have hx' : 0 < ∥x∥ := norm_pos_iff.mpr h,
  refine (mul_le_mul_left hx').mp _, rw ← mul_assoc, rw mul_inv_cancel hx,
  simp, exact le_of_eq (coord_isometry 𝕜 x h y),
end

/-- Temporary (this probably exists elsewhere).  Given a nonzero element `x` of
    a normed space `E` over `𝕜`, the natural map from the span of `x` to `𝕜`,
    with boundedness check to consider it as a continuous linear map. -/
def coord_bdd (x : E) (h : x ≠ 0) : span 𝕜 x →L[𝕜] 𝕜 :=
linear_map.mk_continuous
(coord 𝕜 x h)
∥x∥⁻¹
(coord_lipschitz 𝕜 x h)

lemma coord_norm (x : E) (h : x ≠ 0) : ∥coord_bdd 𝕜 x h∥ = ∥x∥⁻¹ :=
begin
  have hx : ∥x∥ ≠ 0 := mt norm_eq_zero.mp h,
  have hx' : 0 < ∥x∥ := norm_pos_iff.mpr h,
  refine le_antisymm_iff.mpr ⟨_, _⟩,
  { have h1 : 0 ≤ ∥x∥⁻¹ := le_of_lt (inv_pos.mpr hx'),
    apply continuous_linear_map.op_norm_le_bound (coord_bdd 𝕜 x h) h1,
    apply coord_lipschitz 𝕜 x h },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    intros c h, simp at h, cases h,
    refine (mul_le_mul_right hx').mp _, rw inv_mul_cancel hx,
    calc 1 = ∥(1:𝕜)∥ : by simp
    ... = ∥coord 𝕜 x h ⟨x, mem_span_self 𝕜 x⟩∥ : _
    ... ≤ c * ∥x∥ : _,
    rw coord_self 𝕜 x h, exact h_right ⟨x, mem_span_self 𝕜 x⟩ }
end

end span

section dual_vector
variables {E : Type*} [normed_group E] [normed_space ℝ E]

open_locale classical

lemma coord_self' (x : E) (h : x ≠ 0) : (∥x∥ • (coord_bdd ℝ x h)) ⟨x, mem_span_self ℝ x⟩ = ∥x∥ :=
begin
  calc (∥x∥ • (coord_bdd ℝ x h)) ⟨x, mem_span_self ℝ x⟩
      = ∥x∥ • (coord ℝ x h) ⟨x, mem_span_self ℝ x⟩ : rfl
  ... = ∥x∥ • 1 : by rw coord_self ℝ x h
  ... = ∥x∥ : mul_one _,
end

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥∥x∥ • coord_bdd ℝ x h∥ = 1 :=
begin
  have hx : ∥x∥ ≠ 0 := mt norm_eq_zero.mp h,
  calc ∥∥x∥ • coord_bdd ℝ x h∥ = ∥x∥ * ∥coord_bdd ℝ x h∥ : _
  ... = ∥x∥ * ∥x∥⁻¹ : _
  ... = 1 : _,
  rw norm_smul, simp, rw coord_norm, rw mul_inv_cancel hx,
end

-- First phrasing, requiring `x ≠ 0`.
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ d : E →L[ℝ] ℝ, ∥d∥ = 1 ∧ d x = ∥x∥ :=
begin
  cases exists_extension_norm_eq (span ℝ x) (coord_bdd ℝ x h) with g hg,
  use ∥x∥ • g, split,
  { rw ← (coord_norm' x h), rw norm_smul, rw norm_smul, rw ← hg.2 },
  { calc (∥x∥ • g) x = ∥x∥ • (g x) : rfl
    ... = ∥x∥ • coord_bdd ℝ x h (⟨x, mem_span_self ℝ x⟩ : span ℝ x) : _
    ... = (∥x∥ • coord_bdd ℝ x h) ⟨x, mem_span_self ℝ x⟩ : rfl
    ... = ∥x∥ : by rw coord_self',
    rw ← hg.1, simp }
end

/- Second phrasing, requiring only that `E` be nontrivial, and choosing g of norm 1
   arbitrarily when `x = 0`. -/
theorem exists_dual_vector' (h : vector_space.dim ℝ E > 0) (x : E) : ∃ g : E →L[ℝ] ℝ,
  ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  cases dec_em (x = 0) with hx hx,
  { have h' : vector_space.dim ℝ (⊤ : subspace ℝ E) > 0 := by {simp, exact h},
    cases exists_mem_ne_zero_of_dim_pos h' with y hy,
    cases exists_dual_vector y hy.right with g hg, use g, refine ⟨hg.left, _⟩, rw hx, simp },
  { exact exists_dual_vector x hx }
end

end dual_vector
