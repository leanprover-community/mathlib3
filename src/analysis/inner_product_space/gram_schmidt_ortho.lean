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
  If the input of the first `n + 1` vectors of `gram_schmidt` are linearly independent,
  then the output of the first `n + 1` vectors are non-zero.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/
namespace locally_finite_order

lemma exists_min_greater {α : Type*} [linear_order α] [locally_finite_order α] (x : α) :
  ∃ sx, x ≤ sx ∧ ∀ y, x < y → x < sx ∧ sx ≤ y :=
begin
  by_cases h : ∃ y, x < y,
  { rcases h with ⟨y, hy⟩,
    use finset.min' (finset.Ioc x y) ⟨y, finset.mem_Ioc.2 ⟨hy, le_refl y⟩⟩,
    have h_min' : x < (finset.Ioc x y).min' _ ∧ (finset.Ioc x y).min' _ ≤ y :=
      (finset.mem_Ioc.1 (finset.min'_mem (finset.Ioc x y) ⟨y, finset.mem_Ioc.2 ⟨hy, le_refl y⟩⟩)),
    refine ⟨finset.le_min' _ _ _ (λ z hz, le_of_lt (finset.mem_Ioc.1 hz).1), _⟩,
    intros z hz,
    by_cases hzy : z ≤ y,
    { exact ⟨h_min'.1, finset.min'_le (finset.Ioc x y) z (finset.mem_Ioc.2 ⟨hz, hzy⟩)⟩, },
    { exact ⟨h_min'.1, h_min'.2.trans (le_of_not_le hzy)⟩, } },
  { refine ⟨x, le_refl x, λ y hy, false.elim ((not_exists.1 h) _ hy)⟩ }
end

noncomputable instance {α : Type*} [linear_order α] [locally_finite_order α] : succ_order α := {
  succ := λ x, classical.some (exists_min_greater x),
  le_succ := λ x, (classical.some_spec (exists_min_greater x)).1,
  max_of_succ_le := λ x hx y hxy, classical.by_contradiction
    (λ h, not_le_of_lt ((classical.some_spec (exists_min_greater x)).2 y (lt_of_not_le h)).1 hx),
  succ_le_of_lt := λ x y hxy, ((classical.some_spec (exists_min_greater x)).2 y hxy).2,
  le_of_lt_succ := λ y x hy, by {contrapose hy, simp only [not_lt, not_le] at *,
    exact ((classical.some_spec (exists_min_greater x)).2 y hy).2},
}

end locally_finite_order
--TODO: move
namespace encodable

local attribute [instance] nat.locally_finite_order
local attribute [-instance] nat.encodable
local attribute [-instance] denumerable.nat

instance {ι : Type*} [encodable ι] : partial_order ι := {
  le := λ i j, (encode i) ≤ (encode j),
  le_refl := λ i, nat.le_refl _,
  le_trans := λ i j k hij hjk, nat.le_trans hij hjk,
  le_antisymm := λ i j h₁ h₂, encode_injective (nat.le_antisymm h₁ h₂)
}

noncomputable def preimage_encode {ι : Type*} [encodable ι] (s : finset ℕ) : finset ι :=
finset.preimage s encode (set.inj_on_of_injective encode_injective _)

open locally_finite_order

noncomputable instance {ι : Type*} [encodable ι] : locally_finite_order ι := {
  finset_Icc := λ i j, preimage_encode (finset_Icc (encode i) (encode j)),
  finset_Ioc := λ i j, preimage_encode (finset_Ioc (encode i) (encode j)),
  finset_Ico := λ i j, preimage_encode (finset_Ico (encode i) (encode j)),
  finset_Ioo := λ i j, preimage_encode (finset_Ioo (encode i) (encode j)),
  finset_mem_Icc := λ i j k, by { rw [preimage_encode, finset.mem_preimage], apply finset_mem_Icc },
  finset_mem_Ioc := λ i j k,
    by { simp only [preimage_encode, finset.mem_preimage, finset_mem_Ioc, nat.lt_iff_le_not_le],
         refl },
  finset_mem_Ico := λ i j k,
    by { simp only  [preimage_encode, finset.mem_preimage, finset_mem_Ico, nat.lt_iff_le_not_le],
         refl },
  finset_mem_Ioo := λ i j k,
    by { simp only [preimage_encode, finset.mem_preimage, finset_mem_Ioo, nat.lt_iff_le_not_le],
         refl },
}

instance {ι : Type*} [encodable ι] : linear_order ι := {
  le_total := λ i j, @nat.le_total (encode i) (encode j),
  decidable_le := λ i j, nat.decidable_le (encode i) (encode j),
  ..encodable.partial_order
}

-- TODO: use locally_finite_order.of_Icc or locally_finite_order.of_finite_Icc?


noncomputable instance {ι : Type*} [encodable ι] : succ_order ι := {
  succ := λ i, @nat.find (λ n, encode i < n ∧ (decode ι n).is_some),
  le_succ := _,
  max_of_succ_le := _,
  succ_le_of_lt := _,
  le_of_lt_succ := _,

}

noncomputable instance {ι : Type*} [encodable ι] : has_bot ι := {
}

end encodable

open_locale big_operators

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables (ι : Type*) [encodable ι]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gram_schmidt (f : ι → E) : ι → E
| n := f n - ∑ i : fin n, orthogonal_projection (𝕜 ∙ gram_schmidt i) (f n)
using_well_founded {dec_tac := `[exact i.prop]}

/-- `gram_schmidt_def` turns the sum over `fin n` into a sum over `ℕ`. -/
lemma gram_schmidt_def (f : ℕ → E) (n : ℕ) :
  gram_schmidt 𝕜 f n = f n - ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
begin
  rw gram_schmidt,
  congr' 1,
  exact fin.sum_univ_eq_sum_range (λ i,
    (orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) : E)) n,
end

lemma gram_schmidt_def' (f : ℕ → E) (n : ℕ):
  f n = gram_schmidt 𝕜 f n + ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
by simp only [gram_schmidt_def, sub_add_cancel]

@[simp] lemma gram_schmidt_zero (f : ℕ → E) :
  gram_schmidt 𝕜 f 0 = f 0 :=
by simp only [gram_schmidt, fintype.univ_of_is_empty, finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**:
`gram_schmidt` produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ℕ → E) {a b : ℕ} (h₀ : a ≠ b) :
  ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0 :=
begin
  suffices : ∀ a b : ℕ, a < b → ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0,
  { cases h₀.lt_or_lt with ha hb,
    { exact this _ _ ha, },
    { rw inner_eq_zero_sym,
      exact this _ _ hb, }, },
  clear h₀ a b,
  intros a b h₀,
  induction b using nat.strong_induction_on with b ih generalizing a,
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    orthogonal_projection_singleton, inner_smul_right],
  rw finset.sum_eq_single_of_mem a (finset.mem_range.mpr h₀),
  { by_cases h : gram_schmidt 𝕜 f a = 0,
    { simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero], },
    { rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self],
      rwa [ne.def, inner_self_eq_zero], }, },
  simp_intros i hi hia only [finset.mem_range],
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero],
  right,
  cases hia.lt_or_lt with hia₁ hia₂,
  { rw inner_eq_zero_sym,
    exact ih a h₀ i hia₁, },
  { exact ih i hi a hia₂, },
end

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ℕ → E) :
  pairwise (λ a b, ⟪gram_schmidt 𝕜 f a, gram_schmidt 𝕜 f b⟫ = 0) :=
@gram_schmidt_orthogonal 𝕜 _ _ _ f

open submodule set order

/-- `gram_schmidt` preserves span of vectors. -/
lemma span_gram_schmidt (f : ℕ → E) (c : ℕ) :
  span 𝕜 (gram_schmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c) :=
begin
  induction c with c hc,
  { simp only [Iio, not_lt_zero', set_of_false, image_empty], },
  have h₀ : ∀ b, b ∈ finset.range c → gram_schmidt 𝕜 f b ∈ span 𝕜 (f '' Iio c),
  { simp_intros b hb only [finset.mem_range, nat.succ_eq_add_one],
    rw ← hc,
    refine subset_span _,
    simp only [mem_image, mem_Iio],
    refine ⟨b, by linarith, by refl⟩, },
  rw [← nat.succ_eq_succ, Iio_succ_eq_insert],
  simp only [span_insert, image_insert_eq, hc],
  apply le_antisymm,
  { simp only [nat.succ_eq_succ,gram_schmidt_def 𝕜 f c, orthogonal_projection_singleton,
      sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    apply submodule.sub_mem _ _ _,
    { exact mem_sup_left (mem_span_singleton_self (f c)), },
    { exact submodule.sum_mem _ (λ b hb, mem_sup_right (smul_mem _ _ (h₀ b hb))), }, },
  { rw [gram_schmidt_def' 𝕜 f c],
    simp only [orthogonal_projection_singleton,
      sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_true],
    apply submodule.add_mem _ _ _,
    { exact mem_sup_left (mem_span_singleton_self (gram_schmidt 𝕜 f c)), },
    { exact submodule.sum_mem _ (λ b hb, mem_sup_right (smul_mem _ _ (h₀ b hb))), }, },
end

/-- If the input of the first `n` vectors of `gram_schmidt` are linearly independent,
then the output of the first `n` vectors are non-zero. -/
lemma gram_schmidt_ne_zero (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 (f ∘ (coe : fin n → ℕ))) :
    ∀ i, i < n → gram_schmidt 𝕜 f i ≠ 0 :=
begin
  induction n with n hn,
  { intros, linarith },
  { intros i hi h₁,
    rw nat.succ_eq_add_one at hi,
    have h₂ := gram_schmidt_def' 𝕜 f i,
    simp only [nat.succ_eq_add_one, h₁, orthogonal_projection_singleton, zero_add] at h₂,
    have h₃ : f i ∈ span 𝕜 (f '' Iio i),
    { rw [h₂, ← span_gram_schmidt 𝕜 f i],
      apply submodule.sum_mem _ _,
      simp_intros a ha only [finset.mem_range],
      apply submodule.smul_mem _ _ _,
      refine subset_span _,
      simp only [mem_image, mem_Iio],
      exact ⟨a, by linarith, by refl⟩, },
    change linear_independent 𝕜 (f ∘ (coe : fin (n + 1) → ℕ)) at h₀,
    have h₄ : (i : fin (n + 1)) ∉ (coe : fin (n + 1) → ℕ) ⁻¹' (Iio i),
    { simp only [mem_preimage, mem_Iio, not_le],
      rw [fin.coe_coe_of_lt, not_lt],
      exact hi },
    apply linear_independent.not_mem_span_image h₀ h₄,
    rw [image_comp, image_preimage_eq_inter_range],
    simp only [function.comp_app, subtype.range_coe_subtype],
    convert h₃,
    { exact fin.coe_coe_of_lt hi, },
    { simp only [inter_eq_left_iff_subset, Iio, set_of_subset_set_of],
      exact (λ a ha, by linarith) } }
end

/-- If the input of `gram_schmidt` is linearly independent, then the output is non-zero. -/
lemma gram_schmidt_ne_zero' (f : ℕ → E) (h₀ : linear_independent 𝕜 f) (n : ℕ) :
  ∀ i, i < n → gram_schmidt 𝕜 f i ≠ 0 :=
λ i hi, gram_schmidt_ne_zero 𝕜 f n (linear_independent.comp h₀ _ (fin.coe_injective)) i hi

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gram_schmidt_normed (f : ℕ → E) (n : ℕ) : E :=
(∥gram_schmidt 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt 𝕜 f n)

lemma gram_schmidt_normed_unit_length (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 (f ∘ (coe : fin n → ℕ))) (i : ℕ) (hi : i < n) :
    ∥gram_schmidt_normed 𝕜 f i∥ = 1 :=
by simp only [gram_schmidt_ne_zero 𝕜 f n h₀ i hi,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

lemma gram_schmidt_normed_unit_length' (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 f) :
    ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero' 𝕜 f h₀ n.succ n (lt_succ n),
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ℕ → E) (h₀ : linear_independent 𝕜 f) :
  orthonormal 𝕜 (gram_schmidt_normed 𝕜 f) :=
begin
  unfold orthonormal,
  split,
  { simp only [gram_schmidt_normed_unit_length', h₀, forall_const], },
  { intros i j hij,
    simp only [gram_schmidt_normed, inner_smul_left, inner_smul_right, is_R_or_C.conj_inv,
      is_R_or_C.conj_of_real, mul_eq_zero, inv_eq_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero],
    repeat { right },
    exact gram_schmidt_orthogonal 𝕜 f hij, },
end
