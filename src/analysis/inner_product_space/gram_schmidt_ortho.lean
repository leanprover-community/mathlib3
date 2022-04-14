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

- `gram_schmidt` : Gram-Schmidt process
- `gram_schmidt_orthogonal` :
  the proof that `gram_schmidt` produces an orthogonal system of vectors
- `span_gram_schmidt` :
  Gram-Schmidt process preserves span of vectors
- `gram_schmidt_ne_zero` :
  If the input of first n vectors of gram_schmidt are linearly independent
  , then output of first n vectors are non-zero
- `gram_schmidt_normed` :
  Normalized "Gram-Schmidt" (i.e each vector in this system has unit length)
- `gram_schmidt_orthornormal` :
  the proof that `gram_schmidt_normed` produces an orthornormal system of vectors

## TODO
  Construct a version with an orthonormal basis from the Gram-Schmidt process.
-/

open_locale big_operators

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- Gram-Schmidt process -/
noncomputable def gram_schmidt (f : ℕ → E) : ℕ → E
| n := f n - ∑ i : fin n, orthogonal_projection (𝕜 ∙ gram_schmidt i) (f n)
using_well_founded {dec_tac := `[exact i.prop]}

/-- 'gram_schmidt_def' turns the sum over `fin n` into a sum over `ℕ`. -/
lemma gram_schmidt_def (f : ℕ → E) (n : ℕ) :
  gram_schmidt 𝕜 f n = f n - ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
begin
  rw gram_schmidt,
  congr' 1,
  exact fin.sum_univ_eq_sum_range (λ i,
    (orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) : E)) n,
end

@[simp] lemma gram_schmidt_zero (f : ℕ → E) :
  gram_schmidt 𝕜 f 0 = f 0 :=
by simp only [gram_schmidt, fintype.univ_of_is_empty, finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**
Gram-Schmidt process produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ℕ → E) (a b : ℕ) (h₀ : a ≠ b) :
  ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0 :=
begin
  suffices : ∀ a b : ℕ, a < b → ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0,
  { cases h₀.lt_or_lt with ha hb,
    { exact this _ _ ha, },
    { rw inner_eq_zero_sym,
      exact this _ _ hb, }, },
  clear h₀ a b,
  intros a b h₀,
  obtain ⟨c, hbc⟩ : ∃ c, b ≤ c := ⟨b, le_rfl⟩,
  induction c using nat.strong_induction_on with c hc generalizing a b,
  rw le_iff_lt_or_eq at hbc,
  rcases hbc with (hbc | rfl),
  { exact hc b hbc a b h₀ le_rfl, },
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    orthogonal_projection_singleton, inner_smul_right],
  rw finset.sum_eq_single_of_mem a (finset.mem_range.mpr h₀),
  { by_cases h : gram_schmidt 𝕜 f a = 0,
    { simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero], },
    { rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self],
      rwa [ne.def, inner_self_eq_zero], }, },
  intros i hi hia,
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero],
  right,
  rw finset.mem_range at hi,
  cases hia.lt_or_lt with hia₁ hia₂,
  { rw inner_eq_zero_sym,
    exact hc a h₀ i a hia₁ le_rfl, },
  { exact hc i hi a i hia₂ le_rfl, },
end

open submodule set

/-- Gram-Schmidt process preserves span -/
lemma span_gram_schmidt (f : ℕ → E) (c : ℕ) :
  span 𝕜 (gram_schmidt 𝕜 f '' Iic c) = span 𝕜 (f '' Iic c) :=
begin
  induction c with c hc,
  { simp only [Iic, gram_schmidt_zero, le_zero_iff,
      set_of_eq_eq_singleton, image_singleton], },
  have h : Iic c.succ = insert c.succ (Iic c),
  { ext,
    simp only [Iic, mem_set_of_eq, mem_insert_iff,
      nat.lt_succ_iff, le_iff_lt_or_eq, or_comm], },
  have h₀ : ∀ b, b ∈ finset.range c.succ → gram_schmidt 𝕜 f b ∈ span 𝕜 (f '' Iic c),
  { intros b hb,
    rw [finset.mem_range, nat.succ_eq_add_one] at hb,
    have hb₁ : b ≤ c := by linarith,
    have hb₂ : gram_schmidt 𝕜 f b ∈ span 𝕜 (gram_schmidt 𝕜 f '' Iic c),
      { have h₀ : gram_schmidt 𝕜 f b ∈ gram_schmidt 𝕜 f '' Iic c,
        { simp only [mem_image, mem_Iic],
          refine ⟨b, hb₁, by refl⟩, },
        have h₁ : gram_schmidt 𝕜 f '' Iic c ≤ span 𝕜 (gram_schmidt 𝕜 f '' Iic c) := subset_span,
        exact h₁ h₀, },
    rwa hc at hb₂, },
  simp only [h, span_insert, image_insert_eq, hc],
  apply le_antisymm,
  { rw gram_schmidt_def,
    simp only [orthogonal_projection_singleton,
      sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    apply sub_mem _ _ _,
    { apply mem_sup_left,
      exact mem_span_singleton_self (f c.succ), },
    { apply sum_mem _ _,
      intros b hb,
      apply mem_sup_right,
      apply smul_mem _ _ _,
      specialize h₀ b hb,
      exact h₀, }, },
  { simp only [sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    have hc₁ : f c.succ = gram_schmidt 𝕜 f c.succ + ∑ i in finset.range c.succ,
      orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f c.succ)
        := by simp only [gram_schmidt_def, sub_add_cancel],
    rw hc₁, clear hc₁,
    simp only [orthogonal_projection_singleton],
    apply add_mem _ _ _,
    { apply mem_sup_left,
      exact mem_span_singleton_self (gram_schmidt 𝕜 f c.succ), },
    { apply sum_mem _ _,
      intros b hb,
      apply mem_sup_right,
      apply smul_mem _ _ _,
      specialize h₀ b hb,
      exact h₀, }, },
end

/-- If the input of first n + 1 vectors of gram_schmidt are linearly independent
,then output of first n + 1 vectors are non-zero -/
lemma gram_schmidt_ne_zero (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 (f ∘ (coe : fin n.succ → ℕ))) :
    gram_schmidt 𝕜 f n ≠ 0 :=
begin
  induction n with n hn,
  { simp only [gram_schmidt_zero, ne.def],
    have h : f 0 = (f ∘ (coe : fin 1 → ℕ)) 0 := by simp only [function.comp_app, fin.coe_zero],
    rw h,
    exact linear_independent.ne_zero 0 h₀, },
  { by_contra h₁,
    rw nat.succ_eq_add_one at hn h₀ h₁,
    have h₂ : f (n + 1) = gram_schmidt 𝕜 f (n + 1) + ∑ i in finset.range (n + 1),
      orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f (n + 1))
        := by simp only [gram_schmidt_def, sub_add_cancel],
    simp only [h₁, orthogonal_projection_singleton, zero_add] at h₂,
    have h₃ : ∑ (x : ℕ) in finset.range (n + 1),
      ((⟪gram_schmidt 𝕜 f x, f (n + 1)⟫ / ∥gram_schmidt 𝕜 f x∥ ^ 2) : 𝕜)
        • gram_schmidt 𝕜 f x ∈ span 𝕜 (gram_schmidt 𝕜 f '' Iic n),
    { apply sum_mem _ _,
      intros a ha,
      apply smul_mem _ _ _,
      have ha₁ : gram_schmidt 𝕜 f a ∈ gram_schmidt 𝕜 f '' Iic n,
      { simp only [mem_image, mem_Iic],
        rw finset.mem_range at ha,
        refine ⟨a, by linarith, by refl⟩, },
      have ha₂ : gram_schmidt 𝕜 f '' Iic n
        ⊆ span 𝕜 (gram_schmidt 𝕜 f '' Iic n) := subset_span,
      exact ha₂ ha₁, },
    rw [span_gram_schmidt 𝕜 f n, ← h₂] at h₃,
    change linear_independent 𝕜 (f ∘ (coe : fin (n + 2) → ℕ)) at h₀,
    have h₄ : ((n + 1) : fin (n + 2)) ∉ (coe : fin (n + 2) → ℕ) ⁻¹' (Iic n),
    { simp only [mem_preimage, mem_Iic, not_le],
      norm_cast,
      have h : n + 1 < n + 2 := by linarith,
      rw fin.coe_coe_of_lt h,
      linarith, },
    apply linear_independent.not_mem_span_image h₀ h₄,
    rw [image_comp, image_preimage_eq_inter_range],
    simp only [function.comp_app, subtype.range_coe_subtype],
    convert h₃,
    { norm_cast,
      apply fin.coe_coe_of_lt,
      linarith, },
    { rw inter_eq_left_iff_subset,
      simp only [Iic, set_of_subset_set_of],
      intros a ha,
      linarith, }, },
end

/-- If the input of gram_schmidt is linearly independent, then output is non-zero -/
lemma gram_schmidt_ne_zero' (f : ℕ → E) (h₀ : linear_independent 𝕜 f) (n : ℕ) :
  gram_schmidt 𝕜 f n ≠ 0 :=
begin
  apply gram_schmidt_ne_zero 𝕜 f n,
  apply linear_independent.comp,
  { exact h₀, },
  { exact fin.coe_injective, },
end

/-- Normalized Gram-Schmidt process
(i.e each vector in 'gram_schmidt_normed` has unit length) -/
noncomputable def gram_schmidt_normed (f : ℕ → E) (n : ℕ) : E :=
(∥gram_schmidt 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt 𝕜 f n)

lemma gram_schmidt_normed_unit_length (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 (f ∘ (coe : fin n.succ → ℕ))) :
    ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero 𝕜 f n h₀,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

lemma gram_schmidt_normed_unit_length' (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 f) :
    ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero' 𝕜 f h₀,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

/-- **Gram-Schmidt Orthonormalization**
Normalized Gram-Schmidt process produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ℕ → E) (h₀ : linear_independent 𝕜 f) :
  orthonormal 𝕜 (gram_schmidt_normed 𝕜 f) :=
begin
  simp only [orthonormal],
  split,
  { simp only [gram_schmidt_normed_unit_length', h₀, forall_const], },
  { intros i j hij,
    simp only [gram_schmidt_normed, inner_smul_left, inner_smul_right, is_R_or_C.conj_inv,
      is_R_or_C.conj_of_real, mul_eq_zero, inv_eq_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero],
    repeat { right },
    exact gram_schmidt_orthogonal 𝕜 f i j hij, },
end
