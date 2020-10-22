/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.extend
import analysis.convex.cone

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we introduce a typeclass
`has_exists_extension_norm_eq` for a field, requiring that a strong version of the
Hahn-Banach theorem holds over this field, and provide instances for `ℝ` and `ℂ`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/

universes u v

/--
A field where the Hahn-Banach theorem for continuous linear functions holds. This allows stating
theorems that depend on it uniformly over such fields.

In particular, this is satisfied by `ℝ` and `ℂ`.
-/
class has_exists_extension_norm_eq (𝕜 : Type v) [nondiscrete_normed_field 𝕜] : Prop :=
(exists_extension_norm_eq :
  ∀ (E : Type u)
  [normed_group E] [normed_space 𝕜 E]
  (p : subspace 𝕜 E)
  (f : p →L[𝕜] 𝕜),
  ∃ g : E →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥)

/--
The norm of `x` as an element of `𝕜` (a normed algebra over `ℝ`). This is needed in particular to
state equalities of the form `g x = norm' 𝕜 x` when `g` is a linear function.

For the concrete cases of `ℝ` and `ℂ`, this is just `∥x∥` and `↑∥x∥`, respectively.
-/
noncomputable def norm' (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  {E : Type*} [normed_group E] (x : E) : 𝕜 :=
algebra_map ℝ 𝕜 ∥x∥

lemma norm'_def (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  {E : Type*} [normed_group E] (x : E) :
  norm' 𝕜 x = (algebra_map ℝ 𝕜 ∥x∥) := rfl

lemma norm_norm'
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  (A : Type*) [normed_group A]
  (x : A) : ∥norm' 𝕜 x∥ = ∥x∥ :=
by rw [norm'_def, norm_algebra_map_eq, norm_norm]

section real
variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
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

instance real_has_exists_extension_norm_eq : has_exists_extension_norm_eq ℝ :=
⟨by { intros, apply exists_extension_norm_eq }⟩

end real

section complex
variables {F : Type*} [normed_group F] [normed_space ℂ F]

-- Inlining the following two definitions causes a type mismatch between
-- subspace ℝ (semimodule.restrict_scalars ℝ ℂ F) and subspace ℂ F.
/-- Restrict a `ℂ`-subspace to an `ℝ`-subspace. -/
noncomputable def restrict_scalars (p : subspace ℂ F) : subspace ℝ F := p.restrict_scalars ℝ

private lemma apply_real (p : subspace ℂ F) (f' : p →L[ℝ] ℝ) :
  ∃ g : F →L[ℝ] ℝ, (∀ x : restrict_scalars p, g x = f' x) ∧ ∥g∥ = ∥f'∥ :=
  exists_extension_norm_eq (p.restrict_scalars ℝ) f'

open complex

/-- Hahn-Banach theorem for continuous linear functions over `ℂ`. -/
theorem complex.exists_extension_norm_eq (p : subspace ℂ F) (f : p →L[ℂ] ℂ) :
  ∃ g : F →L[ℂ] ℂ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := continuous_linear_map.re.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = (f x).re := λ x, rfl,

  -- Use the real version to get a norm-preserving extension of `fr`, which we'll call `g: F →L[ℝ] ℝ`.
  rcases apply_real p fr with ⟨g, ⟨hextends, hnormeq⟩⟩,

  -- Now `g` can be extended to the `F →L[ℂ] ℂ` we need.
  use g.extend_to_ℂ,

  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_ℂ x = f x,
  { intros,
    change (⟨g x, -g ((I • x) : p)⟩ : ℂ) = f x,
    ext; dsimp only; rw [hextends, fr_apply],
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, mul_re, I_re, I_im],
    ring },

  refine ⟨h, _⟩,

  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  { calc ∥g.extend_to_ℂ∥
        ≤ ∥g∥ : g.extend_to_ℂ.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥continuous_linear_map.re∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [complex.continuous_linear_map.re_norm, one_mul] },

  { exact f.op_norm_le_bound g.extend_to_ℂ.op_norm_nonneg (λ x, h x ▸ g.extend_to_ℂ.le_op_norm x) },
end

instance complex_has_exists_extension_norm_eq : has_exists_extension_norm_eq ℂ :=
⟨by { intros, apply complex.exists_extension_norm_eq }⟩

end complex

section dual_vector
variables {𝕜 : Type v} [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
variables {E : Type u} [normed_group E] [normed_space 𝕜 E]

open continuous_linear_equiv
open_locale classical

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥norm' 𝕜 x • coord 𝕜 x h∥ = 1 :=
by rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

variables [has_exists_extension_norm_eq.{u} 𝕜]
open submodule

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  let p : submodule 𝕜 E := span 𝕜 {x},
  let f := norm' 𝕜 x • coord 𝕜 x h,
  obtain ⟨g, hg⟩ := has_exists_extension_norm_eq.exists_extension_norm_eq E p f,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, mem_span_singleton_self x⟩ : span 𝕜 {x}) : by rw coe_mk
    ... = (norm' 𝕜 x • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : span 𝕜 {x}) : by rw ← hg.1
    ... = norm' 𝕜 x : by simp [coord_self] }
end

/-- Variant of the above theorem, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  by_cases hx : x = 0,
  { obtain ⟨y, hy⟩ := exists_ne (0 : E),
    obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = norm' 𝕜 y := exists_dual_vector y hy,
    refine ⟨g, hg.left, _⟩,
    rw [norm'_def, hx, norm_zero, ring_hom.map_zero, continuous_linear_map.map_zero] },
  { exact exists_dual_vector x hx }
end

end dual_vector
