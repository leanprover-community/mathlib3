/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/

import analysis.inner_product_space.projection

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
  If the first `n` input vectors of `gram_schmidt` are linearly independent,
  then the first `n` output vectors are non-zero.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/

open_locale big_operators

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gram_schmidt (f : ℕ → E) : ℕ → E
| n := f n - ∑ i : fin n, orthogonal_projection (𝕜 ∙ gram_schmidt i) (f n)
using_well_founded {dec_tac := `[exact i.prop]}

noncomputable def gram_schmidt_fin {m : ℕ} (f : fin m → E) : fin m → E :=
  λ i, have hm : fact (0 < m), from ⟨lt_of_le_of_lt (nat.zero_le _) i.2⟩,
    gram_schmidt 𝕜 (λ j, f (@fin.of_nat' _ hm j)) i

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

-- TODO: move
lemma fin.of_nat'_coe {m : ℕ} (n : fin m) :
  @fin.of_nat' _ ⟨lt_of_le_of_lt (nat.zero_le _) n.2⟩ n = n :=
begin
  haveI hm : fact (0 < m), from ⟨lt_of_le_of_lt (nat.zero_le _) n.2⟩,
  ext,
  rw [fin.coe_of_nat_eq_mod', nat.mod_eq_of_lt],
  exact n.2,
end

-- TODO: move
lemma fin.cast_lt_cast_lt {m n : ℕ} (i : fin n) (hm : i.val < m) (hn : i.val < n) :
  (i.cast_lt hm).cast_lt hn = i :=
by simp [fin.cast_lt]

-- TODO: move
lemma sum_fin_range_eq_sum_range {M : Type*} [add_comm_monoid M] (n : ℕ) (f : ℕ → M) :
∑ i in finset.fin_range n, f i = ∑ i in finset.range n, f i :=
begin
  apply finset.sum_bij (λ (i : fin n) ih, i.val),
  exact λ i ih, finset.mem_range.2 i.2,
  { intros, rw fin.coe_eq_val },
  exact λ _ _ _ _, (fin.eq_iff_veq _ _).2,
  exact λ i hi, ⟨⟨i, finset.mem_range.1 hi⟩, finset.mem_fin_range _, rfl⟩
end

lemma gram_schmidt_fin_def {m : ℕ} (f : fin m → E) (n : fin m) :
  gram_schmidt_fin 𝕜 f n = f n - ∑ i in finset.fin_range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt_fin 𝕜 f (i.cast_lt (lt_trans i.2 n.2))) (f n) :=
begin
  haveI hm : fact (0 < m), from ⟨lt_of_le_of_lt (nat.zero_le _) n.2⟩,
  convert gram_schmidt_def 𝕜 (λ (j : ℕ), f (fin.of_nat' j)) n using 2,
  { rw [fin.of_nat'_coe] },
  { rw [←sum_fin_range_eq_sum_range, fin.of_nat'_coe], refl }
end

lemma gram_schmidt_def' (f : ℕ → E) (n : ℕ):
  f n = gram_schmidt 𝕜 f n + ∑ i in finset.range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt 𝕜 f i) (f n) :=
by simp only [gram_schmidt_def, sub_add_cancel]

lemma gram_schmidt_fin_def' {m : ℕ} (f : fin m → E) (n : fin m) :
  f n = gram_schmidt_fin 𝕜 f n + ∑ i in finset.fin_range n,
    orthogonal_projection (𝕜 ∙ gram_schmidt_fin 𝕜 f (i.cast_lt (lt_trans i.2 n.2))) (f n) :=
by simp only [gram_schmidt_fin_def, sub_add_cancel]

@[simp] lemma gram_schmidt_zero (f : ℕ → E) :
  gram_schmidt 𝕜 f 0 = f 0 :=
by simp only [gram_schmidt, fintype.univ_of_is_empty, finset.sum_empty, sub_zero]

@[simp] lemma gram_schmidt_fin_zero {m : ℕ} (f : fin m.succ → E) :
  gram_schmidt_fin 𝕜 f 0 = f 0 :=
by { simp [gram_schmidt_fin, gram_schmidt_zero], refl }

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

theorem gram_schmidt_fin_orthogonal {m : ℕ} (f : fin m → E) {a b : fin m} (h₀ : a ≠ b) :
  ⟪gram_schmidt_fin 𝕜 f a, gram_schmidt_fin 𝕜 f b⟫ = 0 :=
gram_schmidt_orthogonal 𝕜 _ (λ h, h₀ ((fin.ext_iff _ _).2 h))

theorem gram_schmidt_fin_pairwise_orthogonal {m : ℕ} (f : fin m → E) :
  pairwise (λ a b, ⟪gram_schmidt_fin 𝕜 f a, gram_schmidt_fin 𝕜 f b⟫ = 0) :=
@gram_schmidt_fin_orthogonal 𝕜 _ _ _ _ f

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

lemma fin.image_of_nat' (m : ℕ) [h : fact (0 < m)] :
  (fin.of_nat' '' Iio m) = (set.univ : set (fin m)) :=
eq_univ_of_forall (λ i, (mem_image _ _ _).2 ⟨i, mem_Iio.2 i.2, fin.of_nat'_coe _⟩)

lemma fin.range_coe (m : ℕ) : range (λ (i : fin m), (i : ℕ)) = Iio m :=
by simp [Iio]

lemma span_gram_schmidt_fin {m : ℕ} (f : fin m → E) (c : ℕ) :
  span 𝕜 (range (gram_schmidt_fin 𝕜 f)) = span 𝕜 (range f) :=
begin
  cases m,
  { simp only [matrix.range_empty] },
  { haveI : fact (0 < m.succ) := ⟨nat.zero_lt_succ m⟩,
    rw [gram_schmidt_fin, range_comp (gram_schmidt 𝕜 (λ (j : ℕ), f (fin.of_nat' j))) coe,
      fin.range_coe, ←image_univ, span_gram_schmidt 𝕜 (λ i, f (fin.of_nat' i)) m.succ,
      image_comp f (λ (x : ℕ), fin.of_nat' x), fin.image_of_nat', image_univ] }
end

/-- If the input of the first `n + 1` vectors of `gram_schmidt` are linearly independent,
then the output of the first `n + 1` vectors are non-zero. -/
lemma gram_schmidt_ne_zero_aux (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 (f ∘ (coe : fin n → ℕ))) :
    ∀ i (h : i < n), gram_schmidt 𝕜 f i ≠ 0 :=
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
      exact (λ a ha, by linarith), }, },
end

/-- If the input of `gram_schmidt` is linearly independent, then the output is non-zero. -/
lemma gram_schmidt_ne_zero (f : ℕ → E) (h₀ : linear_independent 𝕜 f) (n : ℕ) :
  gram_schmidt 𝕜 f n ≠ 0 :=
gram_schmidt_ne_zero_aux 𝕜 f (n + 1) (linear_independent.comp h₀ _ (fin.coe_injective)) n (lt_succ n)

lemma gram_schmidt_fin_ne_zero {m : ℕ} (f : fin m → E)
  (h₀ : linear_independent 𝕜 f) :
    ∀ i, gram_schmidt_fin 𝕜 f i ≠ 0 :=
begin
  intro i,
  haveI : fact (0 < m) := ⟨lt_of_le_of_lt (nat.zero_le _) i.2⟩,
  have : linear_independent 𝕜 ((λ (j : fin m), f (fin.of_nat' ↑j))),
    by simpa only [fin.of_nat'_coe],
  exact gram_schmidt_ne_zero_aux 𝕜 (λ (j : ℕ), f (fin.of_nat' j)) m this i.1 i.2,
end

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gram_schmidt_normed (f : ℕ → E) (n : ℕ) : E :=
(∥gram_schmidt 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt 𝕜 f n)

noncomputable def gram_schmidt_normed_fin {m : ℕ} (f : fin m → E) (n : fin m) : E :=
  have hm : fact (0 < m), from ⟨lt_of_le_of_lt (nat.zero_le _) n.2⟩,
  gram_schmidt_normed 𝕜 (λ i, f (@fin.of_nat' m hm i)) n

lemma gram_schmidt_normed_fin_def {m : ℕ} (f : fin m → E) (n : fin m) :
  gram_schmidt_normed_fin 𝕜 f n = (∥gram_schmidt_fin 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt_fin 𝕜 f n) :=
rfl

lemma gram_schmidt_normed_unit_length (f : ℕ → E) (n : ℕ)
  (h₀ : linear_independent 𝕜 f) :
    ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero 𝕜 f h₀,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

lemma gram_schmidt_normed_fin_unit_length {m : ℕ} (f : fin m → E) (n : fin m)
  (h₀ : linear_independent 𝕜 f):
    ∥gram_schmidt_normed_fin 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_fin_ne_zero 𝕜 f h₀,
  gram_schmidt_normed_fin_def, norm_smul_inv_norm, ne.def, not_false_iff]

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ℕ → E) (h₀ : linear_independent 𝕜 f) :
  orthonormal 𝕜 (gram_schmidt_normed 𝕜 f) :=
begin
  unfold orthonormal,
  split,
  { simp only [gram_schmidt_normed_unit_length, h₀, forall_const], },
  { intros i j hij,
    simp only [gram_schmidt_normed, inner_smul_left, inner_smul_right, is_R_or_C.conj_inv,
      is_R_or_C.conj_of_real, mul_eq_zero, inv_eq_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero],
    repeat { right },
    exact gram_schmidt_orthogonal 𝕜 f hij, },
end

theorem gram_schmidt_fin_orthonormal {m : ℕ} (f : fin m → E) (h₀ : linear_independent 𝕜 f) :
  orthonormal 𝕜 (gram_schmidt_normed_fin 𝕜 f) :=
begin
  unfold orthonormal,
  split,
  { intro i, simp only [gram_schmidt_normed_fin_unit_length, h₀, forall_const] },
  { intros i j hij,
    simp only [gram_schmidt_normed_fin_def, inner_smul_left, inner_smul_right, is_R_or_C.conj_inv,
      is_R_or_C.conj_of_real, mul_eq_zero, inv_eq_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero],
    repeat { right },
    exact gram_schmidt_fin_orthogonal 𝕜 f hij, },
end
