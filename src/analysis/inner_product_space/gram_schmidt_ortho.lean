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

namespace basis
lemma repr_support_of_mem_span {R M : Type*} {ι : Type*} [semiring R]
[add_comm_monoid M] [module R M]
  (b : basis ι R M) (s : set ι) (m : M) (hm : m ∈ submodule.span R (b '' s)) : ↑(b.repr m).support ⊆ s :=
begin
  rcases (finsupp.mem_span_image_iff_total _).1 hm with ⟨l, hl, hlm⟩,
  rwa [←hlm, repr_total, ←finsupp.mem_supported R l]
end
end basis

namespace submodule

variables (R : Type*) {M : Type*} [semiring R] [add_comm_monoid M] [module R M] (s t : set M)

lemma span_eq_span (hs : s ⊆ span R t) (ht : t ⊆ span R s) : span R s = span R t :=
le_antisymm (span_le.2 hs) (span_le.2 ht)

end submodule

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

lemma mem_span_gram_schmidt (f : ι → E) (i j : ι) (hij : i ≤ j) :
  f i ∈ span 𝕜 (gram_schmidt 𝕜 f '' Iic j) :=
begin
  rw [gram_schmidt_def' 𝕜 f i],
  refine submodule.add_mem _ (subset_span (mem_image_of_mem _ hij)) _,
  apply submodule.sum_mem _ (λ k hk, _),
  rw [orthogonal_projection_singleton],
  apply smul_mem (span 𝕜 (gram_schmidt 𝕜 f '' Iic j)) _
    (subset_span (set.mem_image_of_mem (gram_schmidt 𝕜 f) _)),
  exact (le_of_lt (finset.mem_Iio.1 hk)).trans hij
end

lemma gram_schmidt_mem_span (f : ι → E) (j : ι) :
  ∀ i, i ≤ j → gram_schmidt 𝕜 f i ∈ span 𝕜 (f '' Iic j) :=
begin
  apply well_founded.induction (@is_well_order.wf ι (<) _) j,
  intros j ih i hij,
  rw [gram_schmidt_def 𝕜 f i],
  refine submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (submodule.sum_mem _ (λ k hk, _)),
  simp only [orthogonal_projection_singleton],
  apply smul_mem _ _ _,
  apply span_mono,
  apply set.image_subset f (Iic_subset_Iic.2 ((le_of_lt (finset.mem_Iio.1 hk)).trans hij)),
  exact ih k (lt_of_lt_of_le (finset.mem_Iio.1 hk) hij) k (le_refl k),
end

lemma span_gram_schmidt_Iic (f : ι → E) (c : ι) :
  span 𝕜 (gram_schmidt 𝕜 f '' Iic c) = span 𝕜 (f '' Iic c) :=
begin
  apply span_eq_span,
  { intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨i, hi, hix⟩,
    rw [← hix],
    exact gram_schmidt_mem_span _ _ c i hi },
  { intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨i, hi, hix⟩,
    rw [← hix],
    exact mem_span_gram_schmidt _ _ i c hi }
end

lemma span_gram_schmidt_Iio (f : ι → E) (c : ι) :
  span 𝕜 (gram_schmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c) :=
begin
  apply span_eq_span,
  { intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨i, hi, hix⟩,
    rw [← hix],
    exact span_mono (set.image_subset f (Iic_subset_Iio.2 hi))
      (gram_schmidt_mem_span 𝕜 f i i (le_refl i)) },
  { intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨i, hi, hix⟩,
    rw [← hix],
    exact span_mono (set.image_subset _ (Iic_subset_Iio.2 hi))
      (mem_span_gram_schmidt 𝕜 f i i (le_refl i)) }
end

/-- `gram_schmidt` preserves span of vectors. -/
lemma span_gram_schmidt (f : ι → E) :
  span 𝕜 (range (gram_schmidt 𝕜 f)) = span 𝕜 (range f) :=
begin
  apply span_eq_span,
  { intros x hx,
    rw set.mem_range at hx,
    rcases hx with ⟨i, hix⟩,
    rw [← hix],
    exact span_mono (image_subset_range _ (Iic i)) (gram_schmidt_mem_span 𝕜 f i i (le_refl i)) },
  { intros x hx,
    rw set.mem_range at hx,
    rcases hx with ⟨i, hix⟩,
    rw [← hix],
    exact span_mono (image_subset_range _ (Iic i)) (mem_span_gram_schmidt 𝕜 f i i (le_refl i)) }
end

/-- If the input vectors of `gram_schmidt` are linearly independent,
then the output vectors are non-zero. -/
lemma gram_schmidt_ne_zero (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 f) :
  gram_schmidt 𝕜 f n ≠ 0 :=
begin
  by_contra h,
  have h₃ : f n ∈ span 𝕜 (f '' Iio n),
  { rw [← span_gram_schmidt_Iio 𝕜 f n, gram_schmidt_def' _ f, h, zero_add],
    apply submodule.sum_mem _ _,
    simp_intros a ha only [finset.mem_Ico],
    simp only [set.mem_image, set.mem_Iio, orthogonal_projection_singleton],
    apply submodule.smul_mem _ _ _,
    rw finset.mem_Iio at ha,
    refine subset_span ⟨a, ha, by refl⟩, },
  apply linear_independent.not_mem_span_image h₀ _ h₃,
  simp only [set.mem_Iio, lt_self_iff_false, not_false_iff]
end

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gram_schmidt_normed (f : ι → E) (n : ι) : E :=
(∥gram_schmidt 𝕜 f n∥ : 𝕜)⁻¹ • (gram_schmidt 𝕜 f n)

lemma gram_schmidt_normed_unit_length (f : ι → E) (n : ι) (h₀ : linear_independent 𝕜 f) :
  ∥gram_schmidt_normed 𝕜 f n∥ = 1 :=
by simp only [gram_schmidt_ne_zero 𝕜 f n h₀,
  gram_schmidt_normed, norm_smul_inv_norm, ne.def, not_false_iff]

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ι → E) (h₀ : linear_independent 𝕜 f) :
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

lemma gram_schmidt_triangular {i j : ι} (hij : i < j) (b : basis ι 𝕜 E) :
  b.repr (gram_schmidt 𝕜 b i) j = 0 :=
begin
  have : gram_schmidt 𝕜 b i ∈ span 𝕜 (gram_schmidt 𝕜 b '' set.Iio j),
    from subset_span ((set.mem_image _ _ _).2 ⟨i, hij, rfl⟩),
  have : gram_schmidt 𝕜 b i ∈ span 𝕜 (b '' set.Iio j),
    by rwa [← span_gram_schmidt_Iio 𝕜 b j],
  have : ↑(((b.repr) (gram_schmidt 𝕜 b i)).support) ⊆ set.Iio j,
    from basis.repr_support_of_mem_span b (set.Iio j) (gram_schmidt 𝕜 b i) this,
  exact (finsupp.mem_supported' _ _).1
    ((finsupp.mem_supported 𝕜 _).2 this) j (not_mem_Iio.2 (le_refl j)),
end


#check linear_independent_of_ne_zero_of_inner_eq_zero
#check basis.mk
#check mem_span_finite_of_mem_span
