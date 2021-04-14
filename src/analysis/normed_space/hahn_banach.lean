/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.extend
import analysis.convex.cone
import data.complex.is_R_or_C

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `is_R_or_C 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/

universes u v

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

namespace real
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

end real

section is_R_or_C
open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [normed_group F] [normed_space 𝕜 F]

/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq (p : subspace 𝕜 F) (f : p →L[𝕜] 𝕜) :
  ∃ g : F →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  letI : module ℝ F := restrict_scalars.semimodule ℝ 𝕜 F,
  letI : is_scalar_tower ℝ 𝕜 F := restrict_scalars.is_scalar_tower _ _ _,
  letI : normed_space ℝ F := normed_space.restrict_scalars _ 𝕜 _,
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F →L[ℝ] ℝ`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩,
  -- Now `g` can be extended to the `F →L[𝕜] 𝕜` we need.
  use g.extend_to_𝕜,
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_𝕜_apply, ←submodule.coe_smul, hextends, hextends],
    have : (fr x : 𝕜) - I * ↑(fr (I • x)) = (re (f x) : 𝕜) - (I : 𝕜) * (re (f ((I : 𝕜) • x))),
      by refl,
    rw this,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm,
        of_real_neg, mul_re, mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_neg_eq_neg_mul_symm, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul] } },
  refine ⟨h, _⟩,
  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  { calc ∥g.extend_to_𝕜∥
        ≤ ∥g∥ : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥re_clm∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [re_clm_norm, one_mul] },
  { exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, h x ▸ g.extend_to_𝕜.le_op_norm x) },
end

end is_R_or_C

section dual_vector
variables {𝕜 : Type v} [is_R_or_C 𝕜]
variables {E : Type u} [normed_group E] [normed_space 𝕜 E]

open continuous_linear_equiv submodule
open_locale classical

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥norm' 𝕜 x • coord 𝕜 x h∥ = 1 :=
by rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  let p : submodule 𝕜 E := 𝕜 ∙ x,
  let f := norm' 𝕜 x • coord 𝕜 x h,
  obtain ⟨g, hg⟩ := exists_extension_norm_eq p f,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw coe_mk
    ... = (norm' 𝕜 x • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw ← hg.1
    ... = norm' 𝕜 x : by simp }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
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

section separating

noncomputable theory
variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma mem_sep_true {α : Type*} (s : set α) : {a ∈ s | true} = s :=
by { ext; simp }

lemma mem_sep_false {α : Type*} (s : set α) : {a ∈ s | false} = ∅ :=
by { ext; simp }

lemma le_of_lt_add {α : Type*} [linear_ordered_add_comm_group α] {x y : α}
  (hz : ∀ z, 0 < z → x < y + z) : x ≤ y :=
begin
  by_contra h,
  push_neg at h,
  have : 0 < x - y,
  { rwa sub_pos },
  simpa using hz (x - y) ‹_›,
end

lemma real.zero_le_Inf (S : set ℝ) (hS : ∀ x ∈ S, (0:ℝ) ≤ x) : 0 ≤ Inf S :=
begin
  rcases S.eq_empty_or_nonempty with (rfl | hS₂),
  { simp [real.Inf_empty] },
  { apply real.lb_le_Inf S hS₂ hS }
end

@[simp]
lemma Inf_Ioi (x : ℝ) : Inf (set.Ioi x) = x :=
begin
  apply le_antisymm,
  { apply le_of_lt_add,
    intros z hz,
    rw real.Inf_lt,
    { exact ⟨x + z/2, lt_add_of_pos_right x (half_pos hz), add_lt_add_left (half_lt_self hz) x⟩ },
    { exact ⟨x+1, lt_add_of_pos_right x (show (0:ℝ) < 1, by norm_num)⟩ },
    { exact ⟨x, λ y, le_of_lt⟩ } },
  { rw real.le_Inf,
    { exact λ y, le_of_lt },
    { exact ⟨x+1, lt_add_of_pos_right x (show (0:ℝ) < 1, by norm_num)⟩ },
    { exact ⟨x, λ y, le_of_lt⟩ } }
end

lemma of_Inf_le (S : set ℝ) (hS : ∀ (x ∈ S) y, x ≤ y → y ∈ S) (hS₂ : S.nonempty) (hS₃ : bdd_below S)
  {x y : ℝ} (hx : Inf S ≤ x)
  (hy : x < y) :
  y ∈ S :=
begin
  have : Inf S < y := lt_of_le_of_lt hx hy,
  rw real.Inf_lt _ hS₂ at this,
end


def gauge (K : set E) (x : E) : ℝ :=
Inf {y ∈ set.Ioi 0 | y⁻¹ • x ∈ K}

@[simp]
lemma gauge_zero {K : set E} : gauge K 0 = 0 :=
begin
  rw gauge,
  by_cases (0:E) ∈ K,
  { simp [h, mem_sep_true] },
  { simp [h, mem_sep_false, real.Inf_empty] }
end

lemma zero_le_gauge {K : set E} (x : E) : 0 ≤ gauge K x :=
real.zero_le_Inf _ (λ x hx, le_of_lt hx.1)

lemma gauge_le_one_eq {K : set E} (hK : convex K) :
  {x | gauge K x ≤ 1} = ⋂ (θ ∈ set.Ioi (1:ℝ)), θ • K :=
begin
  ext,
  simp only [set.mem_Ioi, set.mem_Inter, set.mem_set_of_eq],
  split,
  { intros h θ hθ,

  }
end

lemma gauge_le_one_of_mem {K : set E} (x : E) (hx : x ∈ K) : gauge K x ≤ 1 :=
real.Inf_le _ ⟨0, λ y hy, le_of_lt hy.1⟩ ⟨by norm_num, by simpa⟩

lemma Inf_smul (K : set ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
  θ * Inf K = Inf (θ • K) :=
begin
  cases K.eq_empty_or_nonempty,
  { subst h,
    simp [real.Inf_empty] },
  by_cases h₁ : bdd_below K,
  { have : monotone (λ x, (θ:ℝ) * x),
    { exact monotone_mul_left_of_nonneg hθ },
    have z := map_cInf_of_continuous_at_of_monotone (continuous_mul_left θ).continuous_at
                  (monotone_mul_left_of_nonneg hθ) ‹_› ‹_›,
    dsimp at z,
    rw [z, ←set.image_smul],
    refl },
  { rw [real.Inf_of_not_bdd_below h₁, mul_zero],
    rcases eq_or_lt_of_le hθ with (rfl | hθ),
    { rw zero_smul_set h,
      have : (0 : set ℝ) = {0},
      { ext, simp },
      rw this,
      simp only [cInf_singleton] },
    { rw real.Inf_of_not_bdd_below,
      rintro ⟨t, ht⟩,
      apply h₁,
      refine ⟨t / θ, λ z hz, _⟩,
      rw div_le_iff hθ,
      apply ht,
      rw mul_comm,
      exact ⟨_, hz, smul_eq_mul _⟩ } },
end

lemma gauge_neg {K : set E} (balanced : ∀ x ∈ K, -x ∈ K) (x : E) :
  gauge K (-x) = gauge K x :=
begin
  have : ∀ x, -x ∈ K ↔ x ∈ K := λ x, ⟨λ h, by simpa using balanced _ h, balanced x⟩,
  change Inf _ = Inf _,
  simp_rw [smul_neg, this],
end

lemma gauge_mul_nonneg {K : set E}
  {θ : ℝ} (hθ : 0 ≤ θ) (x : E) :
gauge K (θ • x) = θ * gauge K x :=
begin
  rcases eq_or_lt_of_le hθ with (rfl | hθ'),
  { simp },
  change Inf _ = _ * Inf _,
  rw Inf_smul _ ‹0 ≤ θ›,
  congr' 1,
  ext β,
  simp only [set.mem_smul_set, set.mem_sep_eq, smul_eq_mul, set.mem_Ioi],
  split,
  { rintro ⟨hβ₁, hβ₂⟩,
    refine ⟨β * θ⁻¹, ⟨mul_pos ‹0 < β› (inv_pos.2 ‹0 < θ›), _⟩, _⟩,
    rwa [mul_inv', inv_inv', mul_smul],
    rw [mul_left_comm, mul_inv_cancel (ne_of_gt ‹0 < θ›), mul_one] },
  { rintro ⟨β, ⟨_, _⟩, rfl⟩,
    refine ⟨mul_pos ‹0 < θ› ‹0 < β›, _⟩,
    rwa [mul_inv_rev', ←mul_smul, mul_assoc, inv_mul_cancel (ne_of_gt ‹0 < θ›), mul_one] }
end

lemma gauge_homogeneous {K : set E} (balanced : ∀ x ∈ K, -x ∈ K)
  (θ : ℝ) (x : E) :
  gauge K (θ • x) = abs θ * gauge K x :=
begin
  rw ←gauge_mul_nonneg (abs_nonneg θ),
  cases le_total 0 θ,
  { rw abs_of_nonneg h },
  { rw [abs_of_nonpos h, neg_smul, gauge_neg balanced] }
end

#check set.mem_bInter


-- lemma convex_iff_div:
--   convex s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄,
--     0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ s :=

example {a b : ℝ} : a⁻¹ / b * a = b⁻¹ :=
begin
  rw mul_comm_div',
  rw ←mul_div_assoc,
  rw inv_mul_cancel,


end

lemma gauge_subadditive {K : set E} (hK : convex K)
  (absorbing : ∀ x, ∃ (θ : ℝ), 0 < θ ∧ θ • x ∈ K) (x y : E) :
  gauge K (x + y) ≤ gauge K x + gauge K y :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := absorbing x,
  obtain ⟨b, hb₁, hb₂⟩ := absorbing y,
  have : a⁻¹ ≤ gauge K x,
  { have := gauge_le_one_of_mem _ ha₂,
    rw gauge_mul_nonneg (le_of_lt ha₁) at this,
    sorry
  },
  have : gauge K ((a⁻¹ + b⁻¹)⁻¹ • (x + y)) ≤ 1,
  { apply gauge_le_one_of_mem,
    rw convex_iff_div at hK,
    have := hK ha₂ hb₂
              (inv_nonneg.2 (le_of_lt ha₁))
              (inv_nonneg.2 (le_of_lt hb₁))
              (add_pos (inv_pos.2 ‹0 < a›) (inv_pos.2 ‹0 < b›)),
    rw [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ←mul_div_assoc, ←mul_div_assoc,
      inv_mul_cancel (ne_of_gt ha₁), inv_mul_cancel (ne_of_gt hb₁)] at this,
    simpa using this },
  rw gauge_mul_nonneg at this,
  rw inv_mul_le_iff at this,
  rw mul_one at this,
  apply le_trans this,


end

theorem geometric_hahn_banach_open {A B : set E}
  (hA₁ : A.nonempty) (hA₂ : convex A) (hA₃ : is_open A)
  (hB₁ : B.nonempty) (hB₂ : convex B)
  (disj : disjoint A B) :
∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s ≤ f b) :=
sorry

theorem geometric_hahn_banach_open_open {A B : set E}
  (hA₁ : A.nonempty) (hA₂ : convex A) (hA₃ : is_open A)
  (hB₁ : B.nonempty) (hB₂ : convex B) (hB₃ : is_open B)
  (disj : disjoint A B) :
∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s < f b) :=
sorry

theorem geometric_hahn_banach_closed_closed_compact {A B : set E}
  (hA₁ : A.nonempty) (hA₂ : convex A) (hA₃ : is_closed A) (hA₄ : is_compact A)
  (hB₁ : B.nonempty) (hB₂ : convex B) (hA₃ : is_closed B)
  (disj : disjoint A B) :
∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
sorry

#where

end separating
