/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/

import tactic.basic
import algebra.big_operators.basic
import analysis.inner_product_space.basic
import analysis.inner_product_space.projection
import analysis.normed_space.is_R_or_C

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

## Main results

- `gram_schmidt_process` : Gram-Schmidt process
- `gram_schmidt_process_orthogonal` :
  the proof that "gram_schmidt_process" produces an orthogonal system of vectors
- `gram_schmidt_process_normed` :
  Normalized "Gram-Schmidt" (i.e each vector in this system has unit length)
- `gram_schmidt_process_orthornormal` :
  the proof that "gram_schmidt_process_normed" produces an orthornormal system of vectors
-/

open_locale big_operators

variables (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

/-- Gram-Schmidt process -/
noncomputable def gram_schmidt_process (f : ℕ → E) : ℕ → E
| n := f n - ∑ i : fin n, have ↑i < n := i.prop,
  orthogonal_projection (𝕜 ∙ gram_schmidt_process i) (f n)

/-- 'gram_schmidt_process_def' turns the sum over `fin n` into a sum over `ℕ`. -/
lemma gram_schmidt_process_def (f : ℕ → E) (n : ℕ) :
  gram_schmidt_process 𝕜 E f n = f n - ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt_process 𝕜 E f i) (f n) :=
begin
  rw gram_schmidt_process,
  congr' 1,
  exact fin.sum_univ_eq_sum_range (λ i,
    (orthogonal_projection (𝕜 ∙ gram_schmidt_process 𝕜 E f i) (f n) : E)) n,
end

/-- **Gram-Schmidt Orthogonalisation**
Gram-Schmidt process produces an orthogonal system of vectors. -/
theorem gram_schmidt_process_orthogonal (f : ℕ → E) (a b : ℕ) (h₀ : a < b) :
  (inner (gram_schmidt_process 𝕜 E f a) (gram_schmidt_process 𝕜 E f b) : 𝕜) = 0 :=
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
    { simp only [gram_schmidt_process_def 𝕜 E f (c + 1), hb₂, inner_sub_right, inner_sum],
      have h₂ : ∀ x ∈ finset.range(c + 1), x ≠ a →
      (inner (gram_schmidt_process 𝕜 E f a)
        (orthogonal_projection (𝕜 ∙ (gram_schmidt_process 𝕜 E f x)) (f (c + 1)) : E) : 𝕜) = 0,
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
      by_cases (inner (gram_schmidt_process 𝕜 E f a) (gram_schmidt_process 𝕜 E f a) : 𝕜) = 0,
      { simp only [inner_self_eq_zero] at h,
        repeat {rw h},
        simp only [inner_zero_left, mul_zero, sub_zero] },
      { rw ← inner_self_eq_norm_sq_to_K,
        simp [h] }}}
end

/-- Generalised Gram-Schmidt Orthorgonalization -/
theorem gram_schmidt_process_orthogonal' (f : ℕ → E) (a b : ℕ) (h₀ : a ≠ b) :
  (inner (gram_schmidt_process 𝕜 E f a) (gram_schmidt_process 𝕜 E f b) : 𝕜) = 0 :=
begin
  cases h₀.lt_or_lt with ha hb,
  { exact gram_schmidt_process_orthogonal 𝕜 E f a b ha },
  { rw inner_eq_zero_sym,
    exact gram_schmidt_process_orthogonal 𝕜 E f b a hb }
end

/-- Normalized Gram-Schmidt process
(i.e each vector in 'gram_schmidt_process_normed` has unit length) -/
noncomputable def gram_schmidt_process_normed (f : ℕ → E) (n : ℕ) : E :=
(∥ gram_schmidt_process 𝕜 E f n ∥ : 𝕜)⁻¹ • (gram_schmidt_process 𝕜 E f n)

lemma gram_schmidt_process_normed_unit_length (f : ℕ → E) (n : ℕ)
  (h : gram_schmidt_process 𝕜 E f n ≠ 0) :
    ∥ gram_schmidt_process_normed 𝕜 E f n ∥ = 1 :=
by simp only [gram_schmidt_process_normed, norm_smul_inv_norm h]

/-- **Gram-Schmidt Orthonormalization**
Normalized Gram-Schmidt process produces an orthornormal system of vectors. -/
theorem gram_schmidt_process_orthonormal (f : ℕ → E) (h₀ : ∀ n, gram_schmidt_process 𝕜 E f n ≠ 0) :
  orthonormal 𝕜 (gram_schmidt_process_normed 𝕜 E f) :=
begin
  simp only [orthonormal],
  split,
  { simp [gram_schmidt_process_normed_unit_length, h₀] },
  { intros i j hij,
    simp [gram_schmidt_process_normed, inner_smul_left, inner_smul_right],
    repeat {right},
    exact gram_schmidt_process_orthogonal' 𝕜 E f i j hij }
end
