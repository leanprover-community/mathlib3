/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/

import analysis.inner_product_space.projection

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gram_schmidt_process` : Gram-Schmidt process
- `gram_schmidt_process_orthogonal` :
  the proof that "gram_schmidt_process" produces an orthogonal system of vectors
- `gram_schmidt_process_normed` :
  Normalized "Gram-Schmidt" (i.e each vector in this system has unit length)
- `gram_schmidt_process_orthornormal` :
  the proof that "gram_schmidt_process_normed" produces an orthornormal system of vectors
- `gram_schmidt_process_span_eq` :
  the proof that `gram_schmidt_process` preserves the span of vectors

## Notation

 - `⟪_, _⟫` : inner product operator
-/

open_locale big_operators

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- Gram-Schmidt process -/
noncomputable def gram_schmidt_process (f : ℕ → E) : ℕ → E
| n := f n - ∑ i : fin n, orthogonal_projection (𝕜 ∙ gram_schmidt_process i) (f n)
using_well_founded {dec_tac := `[exact i.prop]}

/-- 'gram_schmidt_process_def' turns the sum over `fin n` into a sum over `ℕ`. -/
lemma gram_schmidt_process_def (f : ℕ → E) (n : ℕ) :
  gram_schmidt_process 𝕜 f n = f n - ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt_process 𝕜 f i) (f n) :=
begin
  rw gram_schmidt_process,
  congr' 1,
  exact fin.sum_univ_eq_sum_range (λ i,
    (orthogonal_projection (𝕜 ∙ gram_schmidt_process 𝕜 f i) (f n) : E)) n,
end

@[simp] lemma gram_schmidt_process_zero (f : ℕ → E) :
  gram_schmidt_process 𝕜 f 0 = f 0 := by simp [gram_schmidt_process]

/-- Gram-Schmidt process produces an orthogonal system of vectors. -/
theorem gram_schmidt_process_orthogonal' (f : ℕ → E) (a b : ℕ) (h₀ : a < b) :
  ⟪gram_schmidt_process 𝕜 f a, gram_schmidt_process 𝕜 f b⟫ = 0 :=
begin
  have hc : ∃ c, b ≤ c := ⟨b+1, by linarith⟩,
  cases hc with c h₁,
  induction c with c hc generalizing a b,
  { simp at h₁,
    simp [h₁] at h₀,
    contradiction },
  { rw nat.le_add_one_iff at h₁,
    cases h₁ with hb₁ hb₂,
    { exact hc _ _ h₀ hb₁ },
    { simp only [gram_schmidt_process_def 𝕜 f (c + 1), hb₂, inner_sub_right, inner_sum],
      have h₂ : ∀ x ∈ finset.range(c + 1), x ≠ a →
        ⟪gram_schmidt_process 𝕜 f a,
          (orthogonal_projection (𝕜 ∙ (gram_schmidt_process 𝕜 f x)) (f (c + 1)) : E)⟫ = 0,
      { intros x hx₁ hx₂,
        simp only [orthogonal_projection_singleton],
        rw inner_smul_right,
        cases hx₂.lt_or_lt with hxa₁ hxa₂,
        { have ha₂ : a ≤ c,
          { rw hb₂ at h₀,
            exact nat.lt_succ_iff.mp h₀ },
          specialize hc x a,
          simp [hxa₁, ha₂] at hc,
          simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero],
          right,
          rwa inner_eq_zero_sym at hc },
        { rw [finset.mem_range, nat.lt_succ_iff] at hx₁,
          specialize hc a x,
          simp [hxa₂, hx₁] at hc,
          simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero],
          right,
          exact hc }},
      rw hb₂ at h₀,
      have ha₂ : a ∈ finset.range(c + 1) := finset.mem_range.mpr h₀,
      rw finset.sum_eq_single_of_mem a ha₂ h₂,
      simp only [orthogonal_projection_singleton],
      rw inner_smul_right,
      by_cases ⟪gram_schmidt_process 𝕜 f a, gram_schmidt_process 𝕜 f a⟫ = 0,
      { simp only [inner_self_eq_zero] at h,
        repeat {rw h},
        simp only [inner_zero_left, mul_zero, sub_zero] },
      { rw ← inner_self_eq_norm_sq_to_K,
        simp [h] }}}
end

/-- **Gram-Schmidt Orthogonalisation**
This version is stronger than `gram_schmidt_process_orthogonal'` as it doesn't require `a < b` -/
theorem gram_schmidt_process_orthogonal (f : ℕ → E) (a b : ℕ) (h₀ : a ≠ b) :
  ⟪gram_schmidt_process 𝕜 f a, gram_schmidt_process 𝕜 f b⟫ = 0 :=
begin
  cases h₀.lt_or_lt with ha hb,
  { exact gram_schmidt_process_orthogonal' 𝕜 f a b ha },
  { rw inner_eq_zero_sym,
    exact gram_schmidt_process_orthogonal' 𝕜 f b a hb }
end

/-- Normalized Gram-Schmidt process
(i.e each vector in 'gram_schmidt_process_normed` has unit length) -/
noncomputable def gram_schmidt_process_normed (f : ℕ → E) (n : ℕ) : E :=
(∥ gram_schmidt_process 𝕜 f n ∥ : 𝕜)⁻¹ • (gram_schmidt_process 𝕜 f n)

lemma gram_schmidt_process_normed_unit_length (f : ℕ → E) (n : ℕ)
  (h : gram_schmidt_process 𝕜 f n ≠ 0) :
    ∥ gram_schmidt_process_normed 𝕜 f n ∥ = 1 :=
by simp only [gram_schmidt_process_normed, norm_smul_inv_norm h]

/-- **Gram-Schmidt Orthonormalization**
Normalized Gram-Schmidt process produces an orthornormal system of vectors. -/
theorem gram_schmidt_process_orthonormal (f : ℕ → E) (h₀ : ∀ n, gram_schmidt_process 𝕜 f n ≠ 0) :
  orthonormal 𝕜 (gram_schmidt_process_normed 𝕜 f) :=
begin
  simp only [orthonormal],
  split,
  { simp [gram_schmidt_process_normed_unit_length, h₀] },
  { intros i j hij,
    simp [gram_schmidt_process_normed, inner_smul_left, inner_smul_right],
    repeat {right},
    exact gram_schmidt_process_orthogonal 𝕜 f i j hij }
end

open submodule set

/-- Gram-Schmidt process preserves span -/
lemma span_gram_schmidt_process (f : ℕ → E) (c : ℕ) :
  span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c) = span 𝕜 (f '' Iic c) :=
begin
  induction c with c hc,
  { simp [Iic, gram_schmidt_process_zero] },
  apply le_antisymm,
  { have h₀ : ∀ x ∈ gram_schmidt_process 𝕜 f '' Iic c.succ, x ∈ span 𝕜 (f '' Iic c.succ),
    { intros x hx,
      simp only [mem_image, mem_Iic] at hx,
      rcases hx with ⟨y, hy₁, hy₂⟩,
      rw nat.succ_eq_add_one at hy₁ ⊢,
      by_cases y ≤ c,
      { have h₁ : x ∈ gram_schmidt_process 𝕜 f '' Iic c := ⟨y, h, hy₂⟩,
        have h₂ : gram_schmidt_process 𝕜 f '' Iic c ⊆
          span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c) := subset_span,
        rw hc at h₂,
        have h₃ : span 𝕜 (f '' Iic c) ≤ span 𝕜 (f '' Iic (c + 1)),
        { have h₄ : f '' Iic c ⊆ f '' Iic (c + 1),
          { have h₅ : Iic c ⊆ Iic (c + 1),
            { simp [Iic],
              intros a ha,
              linarith },
            exact image_subset f h₅ },
          exact span_mono h₄ },
        exact h₃ (h₂ h₁) },
      { have h₁ : y = c + 1 := by linarith,
        rw [h₁, gram_schmidt_process_def] at hy₂,
        simp only [orthogonal_projection_singleton] at hy₂,
        rw ← hy₂,
        apply sub_mem _ _ _,
        { have hc : f (c + 1) ∈ f '' Iic (c + 1),
          { simp only [mem_image, mem_Iic],
            refine ⟨c + 1, by linarith, by refl⟩ },
          have hc₁ : f '' Iic (c + 1) ⊆ span 𝕜 (f '' Iic (c + 1)) := subset_span,
          exact hc₁ hc },
        { apply sum_mem _ _,
          intros c₁ hc₁,
          have hc₂ : c₁ ≤ c,
          { rw finset.mem_range at hc₁,
            linarith },
          have hc₃ : gram_schmidt_process 𝕜 f c₁ ∈ span 𝕜 (f '' Iic (c + 1)),
          { have h₂ : gram_schmidt_process 𝕜 f c₁ ∈ gram_schmidt_process 𝕜 f '' Iic c,
            { simp only [mem_image, mem_Iic],
              refine ⟨c₁, hc₂, by refl⟩ },
            have h₃ : gram_schmidt_process 𝕜 f '' Iic c ⊆
              span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c) := subset_span,
            have h₄ : gram_schmidt_process 𝕜 f c₁ ∈
              span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c) := h₃ h₂,
            rw hc at h₄,
            have h₅ : span 𝕜 (f '' Iic c) ≤ span 𝕜 (f '' Iic (c + 1)),
            { have h₆ : f '' Iic c ⊆ f '' Iic (c + 1),
              { have h₇ : Iic c ⊆ Iic (c + 1),
                { simp [Iic],
                  intros a ha,
                  linarith },
                exact image_subset f h₇ },
              exact span_mono h₆ },
            exact h₅ h₄ },
          exact smul_mem (span 𝕜 (f '' Iic (c + 1)))
            ((⟪gram_schmidt_process 𝕜 f c₁, f (c + 1)⟫
              / ∥gram_schmidt_process 𝕜 f c₁∥ ^ 2) : 𝕜) hc₃ }}},
    have h₁ : gram_schmidt_process 𝕜 f '' Iic c.succ ⊆ span 𝕜 (f '' Iic c.succ) := h₀,
    rwa ← span_le at h₁ },
  { have h₀ : ∀ x ∈ f '' Iic c.succ,
      x ∈ span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c.succ),
    { intros x hx,
      simp only [mem_image, mem_Iic] at hx,
      rcases hx with ⟨y, hy₁, hy₂⟩,
      rw nat.succ_eq_add_one at hy₁ ⊢,
      by_cases y ≤ c,
      { have hx : x ∈ f '' Iic c := ⟨y, h, hy₂⟩,
        have hx₁ : x ∈ span 𝕜 (f '' Iic c),
        { have h₁ : f '' Iic c ⊆ span 𝕜 (f '' Iic c) := subset_span,
          exact h₁ hx },
        rw ← hc at hx₁,
        have h₂ : span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c)
          ≤ span 𝕜 (gram_schmidt_process 𝕜 f '' Iic (c + 1)),
        { have h₃ : gram_schmidt_process 𝕜 f '' Iic c ⊆ gram_schmidt_process 𝕜 f '' Iic (c+1),
          { have h₄ : Iic c ⊆ Iic (c + 1),
            { simp [Iic],
              intros a ha,
              linarith },
            exact image_subset (gram_schmidt_process 𝕜 f) h₄ },
          exact span_mono h₃ },
        exact h₂ hx₁ },
      { have hy₃ : y = c + 1 := by linarith,
        rw hy₃ at hy₂,
        have hx : x = gram_schmidt_process 𝕜 f (c + 1) + ∑ i in finset.range (c + 1),
          orthogonal_projection (𝕜 ∙ gram_schmidt_process 𝕜 f i) x :=
            by simp [gram_schmidt_process_def, hy₂],
        simp only [orthogonal_projection_singleton] at hx,
        rw hx,
        apply add_mem _ _ _,
        { have h₁ : gram_schmidt_process 𝕜 f (c + 1) ∈ gram_schmidt_process 𝕜 f '' Iic c.succ,
          { simp only [mem_image, mem_Iic],
            refine ⟨c + 1, by simp only [nat.succ_eq_add_one], by refl⟩ },
          have h₂ : gram_schmidt_process 𝕜 f '' Iic c.succ
            ⊆ span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c.succ) := subset_span,
          exact h₂ h₁ },
        { apply sum_mem _ _,
          intros c₁ hc,
          have hc₁ : gram_schmidt_process 𝕜 f c₁ ∈
            span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c.succ),
          { have hc₂ : gram_schmidt_process 𝕜 f c₁ ∈ gram_schmidt_process 𝕜 f '' Iic c.succ,
            { simp only [mem_image, mem_Iic, nat.succ_eq_add_one],
              refine ⟨c₁, _, by refl⟩,
              rw finset.mem_range at hc,
              linarith },
            have hc₃ : gram_schmidt_process 𝕜 f '' Iic c.succ ⊆
              span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c.succ) := subset_span,
            exact hc₃ hc₂ },
          exact smul_mem (span 𝕜 (gram_schmidt_process 𝕜 f '' Iic (c + 1)))
            ((⟪gram_schmidt_process 𝕜 f c₁, x⟫ / ∥gram_schmidt_process 𝕜 f c₁∥ ^ 2) : 𝕜)
              hc₁ }}},
    have h₁ : f '' Iic c.succ ⊆ span 𝕜 (gram_schmidt_process 𝕜 f '' Iic c.succ) := h₀,
    rwa ← span_le at h₁ }
end
