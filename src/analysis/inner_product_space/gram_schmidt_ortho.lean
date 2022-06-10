/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/

import analysis.inner_product_space.projection
import order.well_founded_set

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gram_schmidt` : the Gram-Schmidt process
- `gram_schmidt_orthogonal` :
  `gram_schmidt` produces an orthogonal system of vectors.
- `span_gram_schmidt` :
  `gram_schmidt` preserves span of vectors.
- `gram_schmidt_ne_zero` :
  If the input vectors of `gram_schmidt` are linearly independent,
  then the output vectors are non-zero.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/

open_locale big_operators
open finset

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {ι : Type*} [linear_order ι] [order_bot ι]
variables [locally_finite_order ι] [is_well_order ι (<)]

local attribute [instance] is_well_order.to_has_well_founded

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gram_schmidt (f : ι → E) : ι → E
| n := f n - ∑ i : Iio n, orthogonal_projection (𝕜 ∙ gram_schmidt i) (f n)
using_well_founded { dec_tac := `[exact (mem_Ico.1 i.2).2] }

/-- This lemma uses `∑ i in` instead of `∑ i :`.-/
lemma gram_schmidt_def (f : ι → E) (n : ι):
  gram_schmidt 𝕜 f n = f n - ∑ i in Iio n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
by { rw [←sum_attach, attach_eq_univ, gram_schmidt], refl }

lemma gram_schmidt_def' (f : ι → E) (n : ι):
  f n = gram_schmidt 𝕜 f n + ∑ i in Iio n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
by rw [gram_schmidt_def, sub_add_cancel]

@[simp] lemma gram_schmidt_zero (f : ι → E) :
  gram_schmidt 𝕜 f ⊥ = f ⊥ :=
by rw [gram_schmidt_def, Iio, finset.Ico_self, finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**:
`gram_schmidt` produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) :
  ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0 :=
begin
  suffices : ∀ a b : ι, a < b → ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0,
  { cases h₀.lt_or_lt with ha hb,
    { exact this _ _ ha, },
    { rw inner_eq_zero_sym,
      exact this _ _ hb, }, },
  clear h₀ a b,
  intros a b h₀,
  revert a,
  apply well_founded.induction (@is_well_order.wf ι (<) _) b,
  intros b ih a h₀,
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    orthogonal_projection_singleton, inner_smul_right],
  rw finset.sum_eq_single_of_mem a (finset.mem_Iio.mpr h₀),
  { by_cases h : gram_schmidt 𝕜 f a = 0,
    { simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero], },
    { rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self],
      rwa [ne.def, inner_self_eq_zero], }, },
  simp_intros i hi hia only [finset.mem_range],
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero],
  right,
  cases hia.lt_or_lt with hia₁ hia₂,
  { rw inner_eq_zero_sym,
    exact ih a h₀ i hia₁ },
  { exact ih i (mem_Ico.1 hi).2 a hia₂ }
end

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ι → E) :
  pairwise (λ a b, ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0) :=
λ a b, gram_schmidt_orthogonal 𝕜 f

open submodule set order

/-- `gram_schmidt` preserves span of vectors. -/
lemma span_gram_schmidt [succ_order ι] [is_succ_archimedean ι] (f : ι → E) (c : ι) :
  span 𝕜 (gram_schmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c) :=
begin
  apply @succ.rec ι _ _ _ (λ c, span 𝕜 (gram_schmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c)) ⊥
    _ _ _ bot_le,
  { simp only [set.Iio_bot, set.image_empty] },
  intros c _ hc,
  by_cases h : succ c = c,
  { rwa h },
  have h₀ : ∀ b, b ∈ finset.Iio c → gram_schmidt 𝕜 f b ∈ span 𝕜 (f '' Iio c),
  { simp_intros b hb only [finset.mem_range, nat.succ_eq_add_one],
    rw ← hc,
    refine subset_span _,
    simp only [set.mem_image, set.mem_Iio],
    refine ⟨b, (finset.mem_Ico.1 hb).2, by refl⟩ },
  rw not_iff_not.2 order.succ_eq_iff_is_max at h,
  rw [order.Iio_succ_eq_insert_of_not_is_max h],
  simp only [span_insert, image_insert_eq, hc],
  apply le_antisymm,
  { simp only [nat.succ_eq_succ,gram_schmidt_def 𝕜 f c, orthogonal_projection_singleton,
      sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    apply submodule.sub_mem _ _ _,
    { exact mem_sup_left (mem_span_singleton_self (f c)) },
    { exact submodule.sum_mem _ (λ b hb, mem_sup_right (smul_mem _ _ (h₀ b hb))) } },
  { rw [gram_schmidt_def' 𝕜 f c],
    simp only [orthogonal_projection_singleton,
      sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    apply submodule.add_mem _ _ _,
    { exact mem_sup_left (mem_span_singleton_self (gram_schmidt 𝕜 f c)), },
    { exact submodule.sum_mem _ (λ b hb, mem_sup_right (smul_mem _ _ (h₀ b hb))) } }
end

lemma gram_schmidt_ne_zero_coe [succ_order ι] [is_succ_archimedean ι]
    (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 (f ∘ (coe : set.Iic n → ι))) :
  gram_schmidt 𝕜 f n ≠ 0 :=
begin
  by_contra h,
  have h₁ : f n ∈ span 𝕜 (f '' Iio n),
  { rw [← span_gram_schmidt 𝕜 f n, gram_schmidt_def' _ f, h, zero_add],
    apply submodule.sum_mem _ _,
    simp_intros a ha only [finset.mem_Ico],
    simp only [set.mem_image, set.mem_Iio, orthogonal_projection_singleton],
    apply submodule.smul_mem _ _ _,
    rw finset.mem_Iio at ha,
    refine subset_span ⟨a, ha, by refl⟩ },
  have h₂ : (f ∘ (coe : set.Iic n → ι)) ⟨n, le_refl n⟩
    ∈ span 𝕜 (f ∘ (coe : set.Iic n → ι) '' Iio ⟨n, le_refl n⟩),
  { rw [image_comp],
    convert h₁ using 3,
    ext i,
    simpa using @le_of_lt _ _ i n },
  apply linear_independent.not_mem_span_image h₀ _ h₂,
  simp only [set.mem_Iio, lt_self_iff_false, not_false_iff]
end

/-- If the input vectors of `gram_schmidt` are linearly independent,
then the output vectors are non-zero. -/
lemma gram_schmidt_ne_zero [succ_order ι] [is_succ_archimedean ι]
    (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 f) :
  gram_schmidt 𝕜 f n ≠ 0 :=
gram_schmidt_ne_zero_coe _ _ _ (linear_independent.comp h₀ _ subtype.coe_injective)

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gram_schmidt_normed (f : ι → E) (n : ι) : E :=
(∥gram_schmidt 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt 𝕜 f n)

lemma gram_schmidt_normed_unit_length_coe [succ_order ι] [is_succ_archimedean ι]
    (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 (f ∘ (coe : set.Iic n → ι))) :
  ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero_coe 𝕜 f n h₀,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

lemma gram_schmidt_normed_unit_length [succ_order ι] [is_succ_archimedean ι]
    (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 f) :
  ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
gram_schmidt_normed_unit_length_coe _ _ _ (linear_independent.comp h₀ _ subtype.coe_injective)

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal [succ_order ι] [is_succ_archimedean ι]
    (f : ι → E) (h₀ : linear_independent 𝕜 f) :
  orthonormal 𝕜 (gram_schmidt_normed 𝕜 f) :=
begin
  unfold orthonormal,
  split,
  { simp only [gram_schmidt_normed_unit_length, h₀, forall_const] },
  { intros i j hij,
    simp only [gram_schmidt_normed, inner_smul_left, inner_smul_right, is_R_or_C.conj_inv,
      is_R_or_C.conj_of_real, mul_eq_zero, inv_eq_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero],
    repeat { right },
    exact gram_schmidt_orthogonal 𝕜 f hij }
end
